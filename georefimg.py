"""
Aplicación sencilla para:
1. Cargar una imagen PNG.
2. Marcar al menos 3 puntos de control sobre la imagen (clics).
3. Asignar coordenadas reales (X,Y) a cada punto manualmente o importarlas desde un CSV.
4. Calcular la transformación afín (world file) para georreferenciar la imagen y opcionalmente guardar el *.pgw.
5. Segunda etapa: Digitalizar polígonos a mano alzada (freehand) sobre la imagen ya georreferenciada.
6. Asignar nombre a cada polígono y guardarlos en un Shapefile y también exportar los vértices a un CSV.

Dependencias principales:
 - tkinter (incluido en Python estándar)
 - matplotlib
 - numpy
 - pyshp (shapefile)
Opcional:
 - shapely (si está instalada se usa para cerrar / limpiar geometrías, sino se omite)

CSV de puntos de control aceptado:
  Formato recomendado con encabezados: col,row,x,y
  - col y row: píxel (0-based) opcionales; si no están se infiere orden por filas.
  - x,y: coordenadas reales.
Si sólo hay columnas x,y se asignan en el orden de los puntos clicados (debe coincidir el número).

CSV de salida de vértices de polígonos:
  columns: poly_id,name,vertex_index,x,y

Shapefile de salida:
  Campos: ID (int), NAME (str)

Uso rápido:
  python georefimg.py

Autor: Generado por GitHub Copilot
"""

import os
import csv
import math
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

import numpy as np
import matplotlib
matplotlib.use("TkAgg")
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

try:
    import shapefile  # pyshp
except ImportError:
    shapefile = None

try:
    from shapely.geometry import Polygon as ShapelyPolygon
    from shapely.geometry import LinearRing as ShapelyLinearRing
    from shapely.ops import unary_union
except ImportError:
    ShapelyPolygon = None
    ShapelyLinearRing = None
    unary_union = None


@dataclass
class ControlPoint:
    col: float
    row: float
    x: Optional[float] = None
    y: Optional[float] = None

    @property
    def is_complete(self) -> bool:
        return self.x is not None and self.y is not None


@dataclass
class DigitizedPolygon:
    name: str
    pixel_points: List[Tuple[float, float]]  # (col,row)
    world_points: List[Tuple[float, float]]  # (x,y)
    id: int = field(default=0)


class GeoRefApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("Georreferenciar PNG y Digitalizar Polígonos")
        self.image_path: Optional[str] = None
        self.img_array: Optional[np.ndarray] = None
        self.control_points: List[ControlPoint] = []
        self.transform: Optional[np.ndarray] = None  # 6 params (A,B,C,D,E,F) world file style
        self.stage = 1  # 1 puntos, 2 polígonos
        self.drawing = False
        self.drawing_mode = "freehand"  # "freehand" or "rectangle"
        self.rect_start = None
        self._last_mouse_pos = None
        self.current_poly_pixels = []
        self.current_group_pixels = []  # Lista de polígonos en el grupo actual
        self.polygons = []
        self.next_poly_id = 1
        self.current_group_name = None
        
        # Navigation control variables
        self.pan_mode = False
        self.pan_start = None
        self.pan_start_xlim = None
        self.pan_start_ylim = None
        self._ignore_next_click = False  # Para evitar clicks espurios

        self._build_ui()

    # ---------------- UI BUILD -----------------
    def _build_ui(self):
        self.main_pane = ttk.Panedwindow(self.root, orient=tk.HORIZONTAL)
        self.main_pane.pack(fill=tk.BOTH, expand=True)

        # Left frame - controls with scrollbar
        self.left_container = ttk.Frame(self.main_pane, padding=5)
        self.main_pane.add(self.left_container, weight=0)
        
        # Create canvas and scrollbar for left panel
        self.left_canvas = tk.Canvas(self.left_container, width=250, highlightthickness=0)
        self.left_scrollbar = ttk.Scrollbar(self.left_container, orient="vertical", command=self.left_canvas.yview)
        self.left_scrollable_frame = ttk.Frame(self.left_canvas)
        
        # Configure scrolling
        self.left_scrollable_frame.bind(
            "<Configure>",
            lambda e: self.left_canvas.configure(scrollregion=self.left_canvas.bbox("all"))
        )
        
        self.left_canvas.create_window((0, 0), window=self.left_scrollable_frame, anchor="nw")
        self.left_canvas.configure(yscrollcommand=self.left_scrollbar.set)
        
        # Pack canvas and scrollbar
        self.left_canvas.pack(side="left", fill="both", expand=True)
        self.left_scrollbar.pack(side="right", fill="y")
        
        # Bind mousewheel to canvas and frame
        self.left_canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.left_scrollable_frame.bind("<MouseWheel>", self._on_mousewheel)
        # For Linux
        self.left_canvas.bind("<Button-4>", self._on_mousewheel)
        self.left_canvas.bind("<Button-5>", self._on_mousewheel)
        self.left_scrollable_frame.bind("<Button-4>", self._on_mousewheel)
        self.left_scrollable_frame.bind("<Button-5>", self._on_mousewheel)
        
        # Bind mouse enter events to enable scrolling when mouse is over the left panel
        self.left_canvas.bind("<Enter>", lambda e: self.left_canvas.focus_set())
        self.left_scrollable_frame.bind("<Enter>", lambda e: self.left_canvas.focus_set())
        
        # Use the scrollable frame as the left_frame for all controls
        self.left_frame = self.left_scrollable_frame

        # Right frame - figure and zoom controls
        self.right_frame = ttk.Frame(self.main_pane)
        self.main_pane.add(self.right_frame, weight=1)

        # Create a horizontal frame to hold the figure and zoom buttons
        self.image_container = ttk.Frame(self.right_frame)
        self.image_container.pack(fill=tk.BOTH, expand=True)

        # Figure frame (takes most of the space)
        self.figure_frame = ttk.Frame(self.image_container)
        self.figure_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Zoom buttons frame (fixed width on the right)
        self.zoom_buttons_frame = ttk.Frame(self.image_container, width=80)
        self.zoom_buttons_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=(5, 0))
        self.zoom_buttons_frame.pack_propagate(False)  # Maintain fixed width

        # Figure
        self.fig = Figure(figsize=(6, 6))
        self.ax = self.fig.add_subplot(111)
        self.ax.set_axis_off()
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.figure_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Connect mouse and keyboard events
        self.canvas.mpl_connect('button_press_event', self.on_click)
        self.canvas.mpl_connect('motion_notify_event', self.on_motion)
        self.canvas.mpl_connect('button_release_event', self.on_release)
        self.canvas.mpl_connect('scroll_event', self.on_scroll)
        self.canvas.mpl_connect('key_press_event', self.on_key_press)
        
        # Make canvas focusable for keyboard events
        self.canvas.get_tk_widget().focus_set()
        self.canvas.get_tk_widget().bind('<Button-1>', self._focus_canvas)

        # Add zoom buttons beside the image
        self._create_image_zoom_controls()

        # Controls for stage 1
        ttk.Label(self.left_frame, text="Etapa 1: Puntos de Control").pack(anchor='w', pady=(0, 4))
        ttk.Button(self.left_frame, text="Cargar PNG", command=self.load_image).pack(fill='x')
        self.points_listbox = tk.Listbox(self.left_frame, height=8)
        self.points_listbox.pack(fill='both', expand=False, pady=4)
        
        # First row of control point buttons
        btn_frame = ttk.Frame(self.left_frame)
        btn_frame.pack(fill='x')
        ttk.Button(btn_frame, text="Asignar Coord", command=self.assign_coord).pack(side=tk.LEFT, expand=True, fill='x', padx=(0,1))
        ttk.Button(btn_frame, text="Importar CSV", command=self.import_control_csv).pack(side=tk.LEFT, expand=True, fill='x', padx=(1,0))
        
        # Second row of control point buttons
        btn_frame2 = ttk.Frame(self.left_frame)
        btn_frame2.pack(fill='x', pady=(2,0))
        ttk.Button(btn_frame2, text="Borrar Último Punto", command=self.delete_last_point).pack(side=tk.LEFT, expand=True, fill='x', padx=(0,1))
        ttk.Button(btn_frame2, text="Limpiar Todo", command=self.clear_all_points).pack(side=tk.LEFT, expand=True, fill='x', padx=(1,0))
        ttk.Button(self.left_frame, text="Calcular Transformación", command=self.compute_transform).pack(fill='x', pady=(4, 0))
        self.lbl_transform = ttk.Label(self.left_frame, text="Transformación: --")
        self.lbl_transform.pack(fill='x', pady=4)
        ttk.Button(self.left_frame, text="Guardar World File", command=self.save_world_file).pack(fill='x')
        self.btn_to_polys = ttk.Button(self.left_frame, text="Ir a Polígonos", command=self.go_to_polygons, state=tk.DISABLED)
        self.btn_to_polys.pack(fill='x', pady=(6, 4))

        # Separator for stage 2
        self.sep2 = ttk.Separator(self.left_frame, orient=tk.HORIZONTAL)
        self.sep2.pack(fill='x', pady=4)
        ttk.Label(self.left_frame, text="Etapa 2: Polígonos").pack(anchor='w')
        
        # Drawing mode selection
        mode_frame = ttk.Frame(self.left_frame)
        mode_frame.pack(fill='x', pady=2)
        self.mode_var = tk.StringVar(value="freehand")
        ttk.Radiobutton(mode_frame, text="Mano alzada", variable=self.mode_var, value="freehand").pack(side=tk.LEFT)
        ttk.Radiobutton(mode_frame, text="Rectángulo", variable=self.mode_var, value="rectangle").pack(side=tk.LEFT)
        
        self.btn_new_poly = ttk.Button(self.left_frame, text="Nuevo Polígono", command=self.start_polygon, state=tk.DISABLED)
        self.btn_new_poly.pack(fill='x', pady=2)
        self.btn_finish_poly = ttk.Button(self.left_frame, text="Finalizar Polígono", command=self._finish_polygon_button, state=tk.DISABLED)
        self.btn_finish_poly.pack(fill='x', pady=2)
        self.btn_undo_poly = ttk.Button(self.left_frame, text="Eliminar Último", command=self.delete_last_polygon, state=tk.DISABLED)
        self.btn_undo_poly.pack(fill='x', pady=2)
        self.poly_listbox = tk.Listbox(self.left_frame, height=8)
        self.poly_listbox.pack(fill='both', expand=False, pady=4)
        ttk.Button(self.left_frame, text="Guardar Shapefile & CSV", command=self.export_polygons, state=tk.NORMAL).pack(fill='x', pady=(8, 4))
        self.status_var = tk.StringVar(value="Listo")
        ttk.Label(self.left_frame, textvariable=self.status_var, wraplength=220, foreground='blue').pack(fill='x', pady=(10,0))
        
        # Bind mousewheel to all children widgets in left panel
        self._bind_mousewheel_to_children(self.left_scrollable_frame)
        
        # Set minimum window size to ensure usability
        self.root.minsize(900, 600)

    def _create_image_zoom_controls(self):
        """Create zoom control buttons beside the image"""
        # Title for the zoom controls
        ttk.Label(self.zoom_buttons_frame, text="Zoom", font=('TkDefaultFont', 9, 'bold')).pack(pady=(10, 5))
        
        # Zoom In button with icon-like appearance
        self.zoom_in_btn = ttk.Button(
            self.zoom_buttons_frame, 
            text="🔍+\nZoom In", 
            command=self.zoom_in,
            width=10
        )
        self.zoom_in_btn.pack(pady=5, fill='x')
        
        # Zoom Out button with icon-like appearance
        self.zoom_out_btn = ttk.Button(
            self.zoom_buttons_frame, 
            text="🔍-\nZoom Out", 
            command=self.zoom_out,
            width=10
        )
        self.zoom_out_btn.pack(pady=5, fill='x')
        
        # Reset View button
        self.reset_btn = ttk.Button(
            self.zoom_buttons_frame, 
            text="⌂\nReset", 
            command=self.reset_view,
            width=10
        )
        self.reset_btn.pack(pady=5, fill='x')
        
        # Pan toggle button
        self.image_pan_btn = ttk.Button(
            self.zoom_buttons_frame, 
            text="✋\nPan", 
            command=self.toggle_pan,
            width=10
        )
        self.image_pan_btn.pack(pady=5, fill='x')
        
        # Separator
        ttk.Separator(self.zoom_buttons_frame, orient=tk.HORIZONTAL).pack(fill='x', pady=5)
        
        # Navigation arrows title
        ttk.Label(self.zoom_buttons_frame, text="Navegar", font=('TkDefaultFont', 9, 'bold')).pack(pady=(5, 2))
        
        # Arrow navigation buttons in cross pattern
        # Up arrow
        self.nav_up_btn = ttk.Button(
            self.zoom_buttons_frame, 
            text="↑", 
            command=lambda: self.navigate_arrow('up'),
            width=5
        )
        self.nav_up_btn.pack(pady=2)
        
        # Left and Right arrows in same row
        nav_lr_frame = ttk.Frame(self.zoom_buttons_frame)
        nav_lr_frame.pack()
        
        self.nav_left_btn = ttk.Button(
            nav_lr_frame, 
            text="←", 
            command=lambda: self.navigate_arrow('left'),
            width=5
        )
        self.nav_left_btn.pack(side=tk.LEFT, padx=2)
        
        self.nav_right_btn = ttk.Button(
            nav_lr_frame, 
            text="→", 
            command=lambda: self.navigate_arrow('right'),
            width=5
        )
        self.nav_right_btn.pack(side=tk.LEFT, padx=2)
        
        # Down arrow
        self.nav_down_btn = ttk.Button(
            self.zoom_buttons_frame, 
            text="↓", 
            command=lambda: self.navigate_arrow('down'),
            width=5
        )
        self.nav_down_btn.pack(pady=2)
        
        # Separator
        ttk.Separator(self.zoom_buttons_frame, orient=tk.HORIZONTAL).pack(fill='x', pady=5)
        
        # Instructions
        instructions = ttk.Label(
            self.zoom_buttons_frame, 
            text="• Rueda: zoom\n• Flechas: navegar\n• Arrastrar: pan",
            font=('TkDefaultFont', 7),
            foreground='gray',
            justify='center'
        )
        instructions.pack(pady=5)

    def _on_mousewheel(self, event):
        """Handle mouse wheel scrolling in the left panel"""
        # Handle different platforms
        if event.delta:  # Windows
            self.left_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        else:  # macOS/Linux
            if event.num == 4:
                self.left_canvas.yview_scroll(-1, "units")
            elif event.num == 5:
                self.left_canvas.yview_scroll(1, "units")
    
    def _bind_mousewheel_to_children(self, widget):
        """Recursively bind mousewheel event to all children widgets"""
        widget.bind("<MouseWheel>", self._on_mousewheel)
        # For Linux
        widget.bind("<Button-4>", self._on_mousewheel)
        widget.bind("<Button-5>", self._on_mousewheel)
        for child in widget.winfo_children():
            self._bind_mousewheel_to_children(child)

    # -------------- IMAGE HANDLING --------------
    def load_image(self):
        path = filedialog.askopenfilename(title="Seleccionar PNG", filetypes=[("PNG","*.png")])
        if not path:
            return
        try:
            import imageio.v2 as imageio
        except ImportError:
            messagebox.showerror("Falta dependencia", "Instale imageio: pip install imageio")
            return
        try:
            arr = imageio.imread(path)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo leer la imagen: {e}")
            return
        self.image_path = path
        self.img_array = arr
        self.control_points.clear()
        self.transform = None
        self.update_points_list()
        self.ax.clear()
        self.ax.imshow(arr)
        self.ax.set_title(os.path.basename(path))
        self.ax.set_axis_off()
        self.canvas.draw_idle()
        self.status("Imagen cargada. Haga clic para agregar puntos de control.")
        self.btn_to_polys.config(state=tk.DISABLED)
        self.btn_new_poly.config(state=tk.DISABLED)
        self.btn_undo_poly.config(state=tk.DISABLED)
        self.poly_listbox.delete(0, tk.END)
        self.polygons.clear()
        self.next_poly_id = 1

    # -------------- CONTROL POINTS AND NAVIGATION --------------
    def _focus_canvas(self, event):
        """Ensure canvas has focus for keyboard events"""
        self.canvas.get_tk_widget().focus_set()
    
    def on_click(self, event):
        # Verificar que el click sea dentro del área de la imagen
        if event.inaxes != self.ax:
            return
        
        # Verificar que las coordenadas sean válidas (dentro de la imagen)
        if event.xdata is None or event.ydata is None:
            return
        
        # Ignorar click si está marcado para ignorar
        if self._ignore_next_click:
            self._ignore_next_click = False
            return
            
        # Handle pan mode
        if self.pan_mode and event.button == 1:  # Left click for panning
            self.pan_start = (event.x, event.y)
            self.pan_start_xlim = self.ax.get_xlim()
            self.pan_start_ylim = self.ax.get_ylim()
            return
            
        if self.stage == 1:
            if self.img_array is None:
                return
            self.control_points.append(ControlPoint(col=event.xdata, row=event.ydata))
            self.update_points_list()
            self.redraw()
        elif self.stage == 2:
            if self.pan_mode:
                return  # Don't draw polygons in pan mode
                
            self.drawing_mode = self.mode_var.get()
            if self.drawing_mode == "freehand" and self.drawing:
                # Add vertex to polygon - pero solo si realmente estamos dibujando
                self.current_poly_pixels.append((event.xdata, event.ydata))
                self.redraw()
                # Habilitar el botón de finalizar cuando tenemos al menos 3 puntos
                if len(self.current_poly_pixels) >= 3:
                    self.btn_finish_poly.config(state=tk.NORMAL)
                # Si es el primer punto, muestra instrucciones
                if len(self.current_poly_pixels) == 1:
                    self.status("Click para agregar vértices. Necesita al menos 3 vértices para crear un polígono.")
                elif len(self.current_poly_pixels) < 3:
                    self.status(f"Vértice {len(self.current_poly_pixels)} agregado. Necesita {3-len(self.current_poly_pixels)} vértices más.")
                else:
                    self.status(f"Vértice {len(self.current_poly_pixels)} agregado. Use el botón 'Finalizar Polígono' cuando termine.")
            elif self.drawing_mode == "rectangle" and self.drawing:
                # Start rectangle - first click
                if self.rect_start is None:
                    self.rect_start = (event.xdata, event.ydata)
                else:
                    # Second click - complete rectangle
                    x1, y1 = self.rect_start
                    x2, y2 = event.xdata, event.ydata
                    # Create rectangle points (clockwise)
                    self.current_poly_pixels = [(x1, y1), (x2, y1), (x2, y2), (x1, y2)]
                    self.rect_start = None
                    self._finish_polygon()

    def on_motion(self, event):
        if event.inaxes == self.ax and event.xdata is not None and event.ydata is not None:
            self._last_mouse_pos = (event.xdata, event.ydata)
            # Si estamos dibujando, actualizar la vista para mostrar la línea de vista previa
            if self.drawing and self.stage == 2:
                self.redraw()
        
        # Handle panning
        if self.pan_mode and self.pan_start is not None and event.button == 1:
            dx = event.x - self.pan_start[0]
            dy = event.y - self.pan_start[1]
            
            # Convert pixel movement to data coordinates
            xlim_range = self.pan_start_xlim[1] - self.pan_start_xlim[0]
            ylim_range = self.pan_start_ylim[1] - self.pan_start_ylim[0]
            
            # Get canvas size
            canvas_width = self.canvas.get_tk_widget().winfo_width()
            canvas_height = self.canvas.get_tk_widget().winfo_height()
            
            if canvas_width > 0 and canvas_height > 0:
                dx_data = -dx * xlim_range / canvas_width
                dy_data = dy * ylim_range / canvas_height
                
                new_xlim = (self.pan_start_xlim[0] + dx_data, self.pan_start_xlim[1] + dx_data)
                new_ylim = (self.pan_start_ylim[0] + dy_data, self.pan_start_ylim[1] + dy_data)
                
                self.ax.set_xlim(new_xlim)
                self.ax.set_ylim(new_ylim)
                self.canvas.draw_idle()
            return
        
        if self.stage != 2 or not self.drawing:
            return
        if event.inaxes != self.ax:
            return
        if event.xdata is None or event.ydata is None:
            return
            
        self.drawing_mode = self.mode_var.get()
        # Para el modo a mano alzada, solo actualizamos la vista previa
        if self.drawing_mode == "freehand" and self.current_poly_pixels:
            self.redraw()  # Esto mostrará la línea provisional al punto actual
        elif self.drawing_mode == "rectangle" and self.rect_start:
            # Show preview of rectangle
            self.redraw()

    def on_release(self, event):
        # Reset pan state
        if self.pan_mode:
            self.pan_start = None
            self.pan_start_xlim = None
            self.pan_start_ylim = None
            return
            
        # No automatic polygon finishing on mouse release for freehand mode
        # Users must use the "Finalizar Polígono" button
        # Rectangle mode handles completion automatically in on_click

    def on_scroll(self, event):
        """Handle mouse wheel zoom"""
        if event.inaxes != self.ax or self.img_array is None:
            return
            
        # Get mouse position in data coordinates
        center_x, center_y = event.xdata, event.ydata
        if center_x is None or center_y is None:
            return
            
        # Zoom factor based on scroll direction
        zoom_factor = 0.8 if event.button == 'up' else 1.25
        
        # Zoom around mouse position
        self.zoom_at_point(center_x, center_y, zoom_factor)
    
    def on_key_press(self, event):
        """Handle keyboard shortcuts"""
        if event.key == '+' or event.key == '=':
            self.zoom_in()
        elif event.key == '-':
            self.zoom_out()
        elif event.key == 'p' or event.key == 'P':
            self.toggle_pan()
        elif event.key == 'r' or event.key == 'R':
            self.reset_view()
        elif event.key == 'Delete' or event.key == 'BackSpace':
            # Delete last control point if in stage 1
            if self.stage == 1:
                self.delete_last_point()
        elif event.key == 'ctrl+Delete' or (event.key == 'Delete' and 'ctrl' in str(event)):
            # Clear all control points if in stage 1
            if self.stage == 1:
                self.clear_all_points()
        elif event.key == 'Enter' or event.key == 'return':
            # Finalizar polígono en etapa 2 si estamos dibujando
            if self.stage == 2 and self.drawing and len(self.current_poly_pixels) >= 3:
                self._finish_polygon()
        elif event.key == 'escape':
            # Cancelar dibujo actual
            if self.stage == 2 and self.drawing:
                self.current_poly_pixels.clear()
                self.drawing = False
                self.rect_start = None
                self.btn_new_poly.config(state=tk.NORMAL)
                self.btn_finish_poly.config(state=tk.DISABLED)
                self.status("Dibujo de polígono cancelado.")
                self.redraw()
        # Arrow key navigation
        elif event.key == 'up':
            self.navigate_arrow('up')
        elif event.key == 'down':
            self.navigate_arrow('down')
        elif event.key == 'left':
            self.navigate_arrow('left')
        elif event.key == 'right':
            self.navigate_arrow('right')

    def _finish_polygon(self):
        """Helper function to complete polygon creation"""
        # Prevenir procesamiento múltiple
        if not self.drawing or len(self.current_poly_pixels) == 0:
            return
            
        # Deshabilitar temporalmente el dibujo para evitar clicks adicionales
        was_drawing = self.drawing
        self.drawing = False
        
        # Store current view limits
        current_xlim = self.ax.get_xlim()
        current_ylim = self.ax.get_ylim()
        
        # Verificar si hay suficientes puntos para formar un polígono
        if len(self.current_poly_pixels) < 3:
            messagebox.showinfo("Aviso", "Se necesitan al menos 3 vértices para crear un polígono.")
            # Restaurar el estado de dibujo si no había suficientes puntos
            self.drawing = was_drawing
            return
        
        # Cerrar el polígono actual
        if self.current_poly_pixels[0] != self.current_poly_pixels[-1]:
            self.current_poly_pixels.append(self.current_poly_pixels[0])
        
        # Si es el primer polígono del grupo, pedir nombre
        if self.current_group_name is None:
            name = self._ask_polygon_name()
            if not name:
                name = f"Polígono {self.next_poly_id}"
            self.current_group_name = name
        
        # Agregar el polígono actual al grupo
        self.current_group_pixels.append(list(self.current_poly_pixels))
        self.current_poly_pixels.clear()
        
        # Preguntar si desea agregar otro polígono al grupo
        wants_more = messagebox.askyesno("Grupo de Polígonos", 
                              f"Polígono agregado al grupo '{self.current_group_name}'\n\n¿Desea agregar otro polígono a este grupo?")
        
        if wants_more:
            # Continuar dibujando en el mismo grupo
            self.status(f"Dibuje el siguiente polígono para el grupo '{self.current_group_name}'")
            self.drawing = True  # Permitir continuar dibujando
            self.btn_new_poly.config(state=tk.DISABLED)
            self.btn_finish_poly.config(state=tk.NORMAL)
            return
        
        # Finalizar el grupo - crear polígono final
        if len(self.current_group_pixels) == 1:
            # Solo un polígono - crear como polígono individual
            poly_pixels = self.current_group_pixels[0]
            world_pts = [self.pixel_to_world(c, r) for c, r in poly_pixels]
            
            # Optional shapely cleanup
            if ShapelyPolygon is not None:
                try:
                    poly_geom = ShapelyPolygon(world_pts)
                    if not poly_geom.is_valid:
                        clean = poly_geom.buffer(0)
                        if clean.type == 'MultiPolygon':
                            clean = max(clean.geoms, key=lambda p: p.area)
                        world_pts = list(clean.exterior.coords)
                        # Update pixel points by inverse transform
                        poly_pixels = []
                        for wx, wy in world_pts:
                            col, row = self.world_to_pixel(wx, wy)
                            poly_pixels.append((col, row))
                except Exception as e:
                    messagebox.showwarning("Aviso", f"No se pudo limpiar el polígono: {e}")
            
            # Crear polígono individual
            poly = DigitizedPolygon(
                name=self.current_group_name,
                pixel_points=poly_pixels,
                world_points=world_pts,
                id=self.next_poly_id
            )
            self.polygons.append(poly)
            self.next_poly_id += 1
            self.update_polygons_list()
            self.status(f"Polígono '{self.current_group_name}' creado.")
        else:
            # Múltiples polígonos - crear como grupo
            group_world_points = []
            for poly_pixels in self.current_group_pixels:
                world_pts = [self.pixel_to_world(c, r) for c, r in poly_pixels]
                group_world_points.append(world_pts)
            
            # Crear polígono con múltiples partes (grupo)
            poly = DigitizedPolygon(
                name=self.current_group_name,
                pixel_points=list(self.current_group_pixels),
                world_points=group_world_points,
                id=self.next_poly_id
            )
            self.polygons.append(poly)
            self.next_poly_id += 1
            self.update_polygons_list()
            self.status(f"Grupo de polígonos '{self.current_group_name}' creado con {len(self.current_group_pixels)} partes.")
        
        # Limpiar variables del grupo
        self.current_group_pixels.clear()
        self.current_group_name = None
        
        self.current_poly_pixels.clear()
        self.drawing = False
        self.rect_start = None
        
        # Redraw and restore view limits
        self.redraw()
        self.ax.set_xlim(current_xlim)
        self.ax.set_ylim(current_ylim)
        self.canvas.draw_idle()
        
        # Restaurar estado de botones
        self.btn_new_poly.config(state=tk.NORMAL)
        self.btn_finish_poly.config(state=tk.DISABLED)

    def _finish_polygon_button(self):
        """Función específica para el botón de finalizar polígono que evita conflictos con eventos de mouse"""
        # Marcar para ignorar el siguiente click para evitar puntos espurios
        self._ignore_next_click = True
        # Usar after() para ejecutar la función con un pequeño retardo
        # esto evita que el click del botón interfiera con el canvas
        self.root.after(10, self._finish_polygon)

    def assign_coord(self):
        sel = self.points_listbox.curselection()
        if not sel:
            messagebox.showinfo("Seleccione", "Seleccione un punto en la lista.")
            return
        idx = sel[0]
        cp = self.control_points[idx]
        x = simpledialog.askfloat("Coordenada X", f"X para punto {idx} (pixel col={cp.col:.1f}):", initialvalue=cp.x if cp.x is not None else 0.0)
        if x is None:
            return
        y = simpledialog.askfloat("Coordenada Y", f"Y para punto {idx} (pixel row={cp.row:.1f}):", initialvalue=cp.y if cp.y is not None else 0.0)
        if y is None:
            return
        cp.x, cp.y = x, y
        self.update_points_list()

    def delete_last_point(self):
        """Delete the last control point"""
        if not self.control_points:
            messagebox.showinfo("Sin puntos", "No hay puntos de control para borrar.")
            return
        
        # Ask for confirmation
        if messagebox.askyesno("Confirmar", f"¿Borrar el último punto de control (punto {len(self.control_points)-1})?"):
            self.control_points.pop()
            self.update_points_list()
            self.redraw()
            self.status(f"Punto de control eliminado. Quedan {len(self.control_points)} puntos.")
            
            # Reset transformation if we have less than 3 points
            if len(self.control_points) < 3:
                self.transform = None
                self.lbl_transform.config(text="Transformación: --")
                self.btn_to_polys.config(state=tk.DISABLED)

    def clear_all_points(self):
        """Clear all control points"""
        if not self.control_points:
            messagebox.showinfo("Sin puntos", "No hay puntos de control para borrar.")
            return
            
        # Ask for confirmation
        if messagebox.askyesno("Confirmar", f"¿Borrar todos los {len(self.control_points)} puntos de control?"):
            self.control_points.clear()
            self.transform = None
            self.update_points_list()
            self.redraw()
            self.lbl_transform.config(text="Transformación: --")
            self.btn_to_polys.config(state=tk.DISABLED)
            self.status("Todos los puntos de control eliminados.")

    def import_control_csv(self):
        if not self.control_points:
            messagebox.showinfo("Primero puntos", "Primero cree puntos clicando sobre la imagen.")
            return
        path = filedialog.askopenfilename(title="CSV puntos", filetypes=[("CSV","*.csv")])
        if not path:
            return
        try:
            with open(path, newline='', encoding='utf-8-sig') as f:
                reader = csv.DictReader(f)
                rows = list(reader)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo leer CSV: {e}")
            return
        if not rows:
            messagebox.showerror("Error", "CSV vacío")
            return
        # Determine mode
        has_col = 'col' in rows[0] and 'row' in rows[0]
        has_xy = 'x' in rows[0] and 'y' in rows[0]
        if not has_xy:
            messagebox.showerror("Error", "CSV debe contener columnas x,y (y opcionalmente col,row)")
            return
        if has_col:
            # Map by (closest) pixel coordinate if near existing control points
            for r in rows:
                try:
                    col = float(r['col']); row = float(r['row'])
                    x = float(r['x']); y = float(r['y'])
                except Exception:
                    continue
                # find nearest existing cp
                nearest = min(self.control_points, key=lambda cp: (cp.col - col)**2 + (cp.row - row)**2)
                nearest.x, nearest.y = x, y
        else:
            if len(rows) != len(self.control_points):
                messagebox.showerror("Error", "Número de filas CSV no coincide con puntos actuales")
                return
            for cp, r in zip(self.control_points, rows):
                try:
                    cp.x = float(r['x']); cp.y = float(r['y'])
                except Exception:
                    pass
        self.update_points_list()
        self.status("Coordenadas importadas.")

    def compute_transform(self):
        complete = [cp for cp in self.control_points if cp.is_complete]
        if len(complete) < 3:
            messagebox.showerror("Faltan puntos", "Se requieren al menos 3 puntos con coordenadas.")
            return
        # Solve least squares for world file style transform:
        # x = C + A*col + B*row
        # y = F + D*col + E*row
        cols = np.array([cp.col for cp in complete])
        rows = np.array([cp.row for cp in complete])
        xs = np.array([cp.x for cp in complete])
        ys = np.array([cp.y for cp in complete])
        G = np.column_stack((np.ones_like(cols), cols, rows))  # for C,A,B and F,D,E separately
        # Solve for x params
        p_x, *_ = np.linalg.lstsq(G, xs, rcond=None)  # [C, A, B]
        p_y, *_ = np.linalg.lstsq(G, ys, rcond=None)  # [F, D, E]
        C, A, B = p_x
        F, D, E = p_y
        self.transform = np.array([A, B, C, D, E, F], dtype=float)  # store in order similar to world file lines mapping
        # Compute residuals
        xs_pred = C + A*cols + B*rows
        ys_pred = F + D*cols + E*rows
        err = np.sqrt((xs - xs_pred)**2 + (ys - ys_pred)**2)
        rmse = float(np.sqrt(np.mean(err**2)))
        self.lbl_transform.config(text=f"RMSE={rmse:.4f} A={A:.6f} B={B:.6f} D={D:.6f} E={E:.6f}")
        self.status(f"Transformación calculada. RMSE={rmse:.4f}")
        self.redraw()
        self.btn_to_polys.config(state=tk.NORMAL)

    def save_world_file(self):
        if self.transform is None or not self.image_path:
            messagebox.showinfo("Primero", "Calcule la transformación y cargue la imagen.")
            return
        A, B, C, D, E, F = self.transform
        # World file lines order: A, D, B, E, C, F
        out_path = filedialog.asksaveasfilename(defaultextension=".pgw", filetypes=[("World File","*.pgw"), ("Todos","*.*")])
        if not out_path:
            return
        try:
            with open(out_path, 'w', encoding='utf-8') as wf:
                wf.write(f"{A}\n{D}\n{B}\n{E}\n{C}\n{F}\n")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo escribir world file: {e}")
            return
        self.status(f"World file guardado: {os.path.basename(out_path)}")

    def go_to_polygons(self):
        if self.transform is None:
            messagebox.showinfo("Primero", "Calcule la transformación.")
            return
        self.stage = 2
        self.btn_new_poly.config(state=tk.NORMAL)
        self.btn_undo_poly.config(state=tk.NORMAL)
        self.status("Etapa 2: Dibuje polígonos (click 'Nuevo Polígono').")
        self.redraw()

    # -------------- POLYGONS --------------
    def start_polygon(self):
        if self.transform is None:
            messagebox.showinfo("Primero", "Calcule la transformación.")
            return
        if self.pan_mode:
            messagebox.showinfo("Modo Pan", "Desactive el modo Pan antes de dibujar polígonos.")
            return
            
        self.drawing = True
        self.rect_start = None
        self.current_poly_pixels.clear()
        self.drawing_mode = self.mode_var.get()
        
        if self.drawing_mode == "freehand":
            if self.current_group_name:
                self.status(f"Click para añadir vértices al grupo '{self.current_group_name}'.")
            else:
                self.status("Click para añadir vértices al nuevo polígono.")
        else:  # rectangle
            self.status("Dibujando rectángulo: click en esquina inicial, luego en esquina opuesta.")
        
        self.btn_new_poly.config(state=tk.DISABLED)
        self.btn_finish_poly.config(state=tk.DISABLED)  # Se habilitará cuando se agregue el primer punto

    def delete_last_polygon(self):
        if not self.polygons:
            return
        removed = self.polygons.pop()
        self.poly_listbox.delete(tk.END)
        self.status(f"Polígono eliminado: {removed.name}")
        self.redraw()

    def export_polygons(self):
        if not self.polygons:
            messagebox.showinfo("Nada", "No hay polígonos para exportar.")
            return
        base = filedialog.asksaveasfilename(title="Guardar Shapefile", defaultextension=".shp", filetypes=[("Shapefile","*.shp")])
        if not base:
            return
        shp_path = base
        csv_path = os.path.splitext(base)[0] + "_vertices.csv"
        # Write shapefile
        if shapefile is None:
            messagebox.showerror("Falta pyshp", "Instale pyshp: pip install pyshp")
            return
        try:
            with shapefile.Writer(shp_path, shapeType=shapefile.POLYGON) as w:
                w.autoBalance = 1
                w.field('ID', 'N', decimal=0)
                w.field('NAME', 'C')
                for poly in self.polygons:
                    # Verificar si es un grupo de polígonos o un polígono individual
                    # Un grupo tiene world_points como lista de listas, un individual como lista simple
                    if (isinstance(poly.world_points, list) and 
                        len(poly.world_points) > 0 and 
                        isinstance(poly.world_points[0], list)):  # Grupo de polígonos
                        # Cada polígono en el grupo es una parte del mismo registro
                        parts = []
                        for part in poly.world_points:
                            # Ensure each part is closed
                            if part[0] != part[-1]:
                                part = part + [part[0]]
                            parts.append(part)
                        w.poly(parts)  # Múltiples partes = múltiples polígonos en el mismo registro
                        w.record(poly.id, poly.name)
                    else:  # Polígono individual
                        # Ensure closed ring
                        pts = poly.world_points
                        if pts[0] != pts[-1]:
                            pts = pts + [pts[0]]
                        w.poly([pts])
                        w.record(poly.id, poly.name)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo escribir shapefile: {e}")
            return
        # Write vertices CSV
        try:
            with open(csv_path, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow(['poly_id','name','vertex_index','x','y'])
                for poly in self.polygons:
                    # Verificar si es un grupo de polígonos o un polígono individual
                    if (isinstance(poly.world_points, list) and 
                        len(poly.world_points) > 0 and 
                        isinstance(poly.world_points[0], list)):  # Grupo de polígonos
                        # Para grupos, escribir cada parte con un índice de parte
                        for part_idx, part in enumerate(poly.world_points):
                            for vertex_idx, (x, y) in enumerate(part):
                                writer.writerow([poly.id, poly.name, f"part{part_idx}_v{vertex_idx}", x, y])
                    else:  # Polígono individual
                        for i, (x, y) in enumerate(poly.world_points):
                            writer.writerow([poly.id, poly.name, i, x, y])
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo escribir CSV: {e}")
            return
        self.status(f"Exportado: {os.path.basename(shp_path)} y CSV de vértices")

    # -------------- UTILS --------------
    def pixel_to_world(self, col: float, row: float) -> Tuple[float, float]:
        if self.transform is None:
            return (float('nan'), float('nan'))
        A, B, C, D, E, F = self.transform
        x = C + A*col + B*row
        y = F + D*col + E*row
        return x, y

    def world_to_pixel(self, x: float, y: float) -> Tuple[float, float]:
        # Invert affine using linear algebra
        if self.transform is None:
            return (float('nan'), float('nan'))
        A, B, C, D, E, F = self.transform
        # Solve [A B; D E] [col; row] = [x-C; y-F]
        M = np.array([[A,B],[D,E]])
        v = np.array([x - C, y - F])
        try:
            col,row = np.linalg.solve(M, v)
        except np.linalg.LinAlgError:
            return (float('nan'), float('nan'))
        return float(col), float(row)

    def update_points_list(self):
        self.points_listbox.delete(0, tk.END)
        for i, cp in enumerate(self.control_points):
            if cp.is_complete:
                self.points_listbox.insert(tk.END, f"{i}: col={cp.col:.1f} row={cp.row:.1f} -> X={cp.x:.3f} Y={cp.y:.3f}")
            else:
                self.points_listbox.insert(tk.END, f"{i}: col={cp.col:.1f} row={cp.row:.1f} -> (sin coord)")
        self.redraw()

    def update_polygons_list(self):
        """Update the polygons listbox with current polygons"""
        self.poly_listbox.delete(0, tk.END)
        for poly in self.polygons:
            vertex_count = len(poly.world_points)
            if vertex_count > 0 and poly.world_points[0] == poly.world_points[-1]:
                vertex_count -= 1  # Don't count the closing vertex twice
            self.poly_listbox.insert(tk.END, f"{poly.id}: {poly.name} ({vertex_count} vtx)")

    def redraw(self):
        if self.img_array is None:
            return
            
        # Store current view limits if they exist
        try:
            current_xlim = self.ax.get_xlim()
            current_ylim = self.ax.get_ylim()
            has_limits = True
        except:
            has_limits = False
            
        self.ax.clear()
        self.ax.imshow(self.img_array)
        self.ax.set_axis_off()
        
        # Draw control points
        for cp in self.control_points:
            color = 'lime' if cp.is_complete else 'yellow'
            self.ax.plot(cp.col, cp.row, 'o', color=color, markersize=6)
            
        # Draw saved polygons
        for poly in self.polygons:
            # Verificar si es un grupo de polígonos o un polígono individual
            # Un grupo tiene pixel_points como lista de listas, un individual como lista de tuplas
            if (isinstance(poly.pixel_points, list) and 
                len(poly.pixel_points) > 0 and 
                isinstance(poly.pixel_points[0], list)):  # Grupo de polígonos
                for pix in poly.pixel_points:
                    xs = [p[0] for p in pix]
                    ys = [p[1] for p in pix]
                    self.ax.plot(xs, ys, '-', color='red', linewidth=1.5)
                # Label en el centroide del primer polígono del grupo
                first_poly = poly.pixel_points[0]
                cx = np.mean([p[0] for p in first_poly])
                cy = np.mean([p[1] for p in first_poly])
                self.ax.text(cx, cy, poly.name, color='white', fontsize=8, ha='center', va='center',
                           bbox=dict(boxstyle="round,pad=0.3", facecolor='red', alpha=0.7))
            else:  # Polígono individual
                pix = poly.pixel_points
                # Asegurar que esté cerrado para la visualización
                xs = [p[0] for p in pix]
                ys = [p[1] for p in pix]
                if pix[0] != pix[-1]:
                    xs.append(pix[0][0])
                    ys.append(pix[0][1])
                self.ax.plot(xs, ys, '-', color='red', linewidth=1.5)
                cx = np.mean([p[0] for p in pix])
                cy = np.mean([p[1] for p in pix])
                self.ax.text(cx, cy, poly.name, color='white', fontsize=8, ha='center', va='center',
                           bbox=dict(boxstyle="round,pad=0.3", facecolor='red', alpha=0.7))
        
        # Draw current group's completed polygons
        for pix in self.current_group_pixels:
            xs = [p[0] for p in pix]
            ys = [p[1] for p in pix]
            self.ax.plot(xs, ys, '-', color='orange', linewidth=1.5)
        # Current drawing
        if self.drawing and self.current_poly_pixels:
            # Dibuja los puntos y líneas del polígono actual
            xs = [p[0] for p in self.current_poly_pixels]
            ys = [p[1] for p in self.current_poly_pixels]
            # Dibuja los vértices como puntos
            self.ax.plot(xs, ys, 'o', color='cyan', markersize=4)
            # Dibuja las líneas entre vértices
            self.ax.plot(xs, ys, '-', color='cyan', linewidth=1)
            
            # Si estamos en modo mano alzada y tenemos al menos un punto,
            # dibuja una línea provisional desde el último punto hasta la posición actual del mouse
            if self.drawing_mode == "freehand" and self._last_mouse_pos and len(self.current_poly_pixels) > 0:
                last_x, last_y = self.current_poly_pixels[-1]
                mouse_x, mouse_y = self._last_mouse_pos
                self.ax.plot([last_x, mouse_x], [last_y, mouse_y], '--', color='cyan', alpha=0.5)
                
                # Si tenemos más de 2 puntos, también mostramos una línea punteada al primer punto
                if len(self.current_poly_pixels) > 2:
                    first_x, first_y = self.current_poly_pixels[0]
                    self.ax.plot([mouse_x, first_x], [mouse_y, first_y], '--', color='cyan', alpha=0.3)
        
        # Rectangle preview
        if self.drawing and self.drawing_mode == "rectangle" and self.rect_start:
            # Get current mouse position from the last motion event
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            if hasattr(self, '_last_mouse_pos') and self._last_mouse_pos:
                x1, y1 = self.rect_start
                x2, y2 = self._last_mouse_pos
                # Draw preview rectangle
                rect_xs = [x1, x2, x2, x1, x1]
                rect_ys = [y1, y1, y2, y2, y1]
                self.ax.plot(rect_xs, rect_ys, '--', color='cyan', alpha=0.7)
        
        # Restore view limits if they existed
        if has_limits:
            self.ax.set_xlim(current_xlim)
            self.ax.set_ylim(current_ylim)
            
        self.canvas.draw_idle()

    def status(self, msg: str):
        self.status_var.set(msg)
        self.root.update_idletasks()

    @staticmethod
    def _dist(a: Tuple[float,float], b: Tuple[float,float]) -> float:
        return math.hypot(a[0]-b[0], a[1]-b[1])

    def zoom_in(self, factor: float = 0.8):
        """Zoom in centered on current view"""
        if self.ax.get_images():
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            cx, cy = np.mean(xlim), np.mean(ylim)
            self.zoom_at_point(cx, cy, factor)

    def zoom_out(self, factor: float = 1.25):
        """Zoom out centered on current view"""
        if self.ax.get_images():
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            cx, cy = np.mean(xlim), np.mean(ylim)
            self.zoom_at_point(cx, cy, factor)
            
    def zoom_at_point(self, center_x: float, center_y: float, factor: float):
        """Zoom in/out centered at a specific point"""
        if not self.ax.get_images():
            return
            
        xlim = self.ax.get_xlim()
        ylim = self.ax.get_ylim()
        
        # Calculate new ranges
        new_width = (xlim[1] - xlim[0]) * factor
        new_height = (ylim[1] - ylim[0]) * factor
        
        # Calculate new limits centered on the specified point
        new_xlim = (center_x - new_width / 2, center_x + new_width / 2)
        new_ylim = (center_y - new_height / 2, center_y + new_height / 2)
        
        # Apply zoom limits to prevent zooming too far out
        if self.img_array is not None:
            max_width = self.img_array.shape[1] * 2  # Allow 2x image size
            max_height = self.img_array.shape[0] * 2
            
            if new_width > max_width:
                center_x = np.clip(center_x, max_width/2, self.img_array.shape[1] - max_width/2)
                new_xlim = (center_x - max_width / 2, center_x + max_width / 2)
            if new_height > max_height:
                center_y = np.clip(center_y, max_height/2, self.img_array.shape[0] - max_height/2)
                new_ylim = (center_y - max_height / 2, center_y + max_height / 2)
        
        self.ax.set_xlim(new_xlim)
        self.ax.set_ylim(new_ylim)
        self.canvas.draw_idle()

    def reset_view(self):
        """Reset view to show entire image"""
        if self.img_array is not None:
            self.ax.set_xlim(0, self.img_array.shape[1])
            self.ax.set_ylim(self.img_array.shape[0], 0)  # Invert Y for image coordinates
            self.canvas.draw_idle()
            if self.pan_mode:
                self.toggle_pan()  # Turn off pan mode when resetting view

    def navigate_arrow(self, direction: str):
        """Navigate the image using arrow directions"""
        if not self.ax.get_images():
            return
            
        xlim = self.ax.get_xlim()
        ylim = self.ax.get_ylim()
        
        # Calculate step size as 10% of current view range
        x_step = (xlim[1] - xlim[0]) * 0.1
        y_step = (ylim[1] - ylim[0]) * 0.1
        
        # Calculate new limits based on direction (up/down inverted for intuitive navigation)
        if direction == 'up':
            # Moving up should show more of the upper part of the image
            new_ylim = (ylim[0] + y_step, ylim[1] + y_step)
            new_xlim = xlim
        elif direction == 'down':
            # Moving down should show more of the lower part of the image
            new_ylim = (ylim[0] - y_step, ylim[1] - y_step)
            new_xlim = xlim
        elif direction == 'left':
            new_xlim = (xlim[0] - x_step, xlim[1] - x_step)
            new_ylim = ylim
        elif direction == 'right':
            new_xlim = (xlim[0] + x_step, xlim[1] + x_step)
            new_ylim = ylim
        else:
            return
            
        # Apply the navigation
        self.ax.set_xlim(new_xlim)
        self.ax.set_ylim(new_ylim)
        self.canvas.draw_idle()

    def _ask_polygon_name(self) -> str:
        """Ask user for a polygon name and return it"""
        name = simpledialog.askstring("Nombre del Polígono", 
                                    "Introduzca un nombre para el polígono:",
                                    initialvalue=f"Polígono {self.next_poly_id}")
        if not name:
            name = f"Polígono {self.next_poly_id}"
        return name

    def toggle_pan(self):
        """Toggle pan mode on/off"""
        self.pan_mode = not self.pan_mode
        if self.pan_mode:
            # Update image side pan button
            self.image_pan_btn.config(text="✋\nPan ON")
            self.image_pan_btn.state(['pressed'])
            self.status("Modo Pan activado. Arrastre para navegar por la imagen.")
        else:
            # Update image side pan button
            self.image_pan_btn.config(text="✋\nPan")
            self.image_pan_btn.state(['!pressed'])
            self.status("Modo Pan desactivado.")
            # Reset pan state
            self.pan_start = None
            self.pan_start_xlim = None
            self.pan_start_ylim = None


def main():
    root = tk.Tk()
    app = GeoRefApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
