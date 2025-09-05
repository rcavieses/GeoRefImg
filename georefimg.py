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
        self.mouse_pressed = False
        self.rect_start = None
        self._last_mouse_pos = None
        self.current_poly_pixels = []
        self.polygons = []
        self.next_poly_id = 1
        
        # Navigation control variables
        self.pan_mode = False
        self.pan_start = None
        self.pan_start_xlim = None
        self.pan_start_ylim = None

        self._build_ui()

    # ---------------- UI BUILD -----------------
    def _build_ui(self):
        self.main_pane = ttk.Panedwindow(self.root, orient=tk.HORIZONTAL)
        self.main_pane.pack(fill=tk.BOTH, expand=True)

        # Left frame - controls
        self.left_frame = ttk.Frame(self.main_pane, padding=5)
        self.main_pane.add(self.left_frame, weight=0)

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

        # Zoom controls
        zoom_frame = ttk.LabelFrame(self.left_frame, text="Navegación", padding=5)
        zoom_frame.pack(fill='x', pady=4)
        
        # First row of zoom controls
        zoom_row1 = ttk.Frame(zoom_frame)
        zoom_row1.pack(fill='x', pady=2)
        ttk.Button(zoom_row1, text="Zoom In (+)", command=self.zoom_in).pack(side=tk.LEFT, expand=True, fill='x', padx=(0,2))
        ttk.Button(zoom_row1, text="Zoom Out (-)", command=self.zoom_out).pack(side=tk.LEFT, expand=True, fill='x', padx=(2,0))
        
        # Second row of zoom controls
        zoom_row2 = ttk.Frame(zoom_frame)
        zoom_row2.pack(fill='x', pady=2)
        self.pan_button = ttk.Button(zoom_row2, text="Pan (P)", command=self.toggle_pan)
        self.pan_button.pack(side=tk.LEFT, expand=True, fill='x', padx=(0,2))
        ttk.Button(zoom_row2, text="Reset (R)", command=self.reset_view).pack(side=tk.LEFT, expand=True, fill='x', padx=(2,0))
        
        # Navigation instructions
        nav_info = ttk.Label(zoom_frame, text="• Rueda del ratón: Zoom\n• Arrastrar: Pan (modo Pan activo)\n• Teclas: +/- zoom, P pan, R reset\n• Flechas ↑↓←→: navegar imagen\n• Del/Backspace: borrar último punto", 
                            font=('TkDefaultFont', 8), foreground='gray')
        nav_info.pack(fill='x', pady=(4,0))

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
        self.btn_undo_poly = ttk.Button(self.left_frame, text="Eliminar Último", command=self.delete_last_polygon, state=tk.DISABLED)
        self.btn_undo_poly.pack(fill='x', pady=2)
        self.poly_listbox = tk.Listbox(self.left_frame, height=8)
        self.poly_listbox.pack(fill='both', expand=False, pady=4)
        ttk.Button(self.left_frame, text="Guardar Shapefile & CSV", command=self.export_polygons, state=tk.NORMAL).pack(fill='x', pady=(8, 4))
        self.status_var = tk.StringVar(value="Listo")
        ttk.Label(self.left_frame, textvariable=self.status_var, wraplength=220, foreground='blue').pack(fill='x', pady=(10,0))

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
        if event.inaxes != self.ax:
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
                # Start freehand drawing - mouse press
                self.mouse_pressed = True
                self.current_poly_pixels.append((event.xdata, event.ydata))
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
        
        if self.stage != 2 or not self.drawing or self.pan_mode:
            return
        if event.inaxes != self.ax:
            return
        if event.xdata is None or event.ydata is None:
            return
            
        self.drawing_mode = self.mode_var.get()
        if self.drawing_mode == "freehand" and self.mouse_pressed:
            # Decimate points to avoid huge arrays
            if not self.current_poly_pixels or self._dist(self.current_poly_pixels[-1], (event.xdata, event.ydata)) > 2:
                self.current_poly_pixels.append((event.xdata, event.ydata))
                self.redraw()
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
            
        if self.stage == 2 and self.drawing:
            self.drawing_mode = self.mode_var.get()
            if self.drawing_mode == "freehand" and self.mouse_pressed:
                # Finish freehand polygon
                self.mouse_pressed = False
                self._finish_polygon()
            # Rectangle mode doesn't use release event

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
        if len(self.current_poly_pixels) > 2:
            name = simpledialog.askstring("Nombre", "Nombre del polígono:")
            if not name:
                name = f"Poly_{self.next_poly_id}"
            world_pts = [self.pixel_to_world(c, r) for c, r in self.current_poly_pixels]
            poly = DigitizedPolygon(name=name, pixel_points=list(self.current_poly_pixels), world_points=world_pts, id=self.next_poly_id)
            self.polygons.append(poly)
            self.next_poly_id += 1
            self.poly_listbox.insert(tk.END, f"{poly.id}: {poly.name} ({len(poly.world_points)} vtx)")
            self.status(f"Polígono '{poly.name}' creado.")
        else:
            self.status("Polígono descartado: muy pocos puntos.")
        self.current_poly_pixels.clear()
        self.drawing = False
        self.redraw()
        self.btn_new_poly.config(state=tk.NORMAL)

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
        self.mouse_pressed = False
        self.rect_start = None
        self.current_poly_pixels.clear()
        self.drawing_mode = self.mode_var.get()
        
        if self.drawing_mode == "freehand":
            self.status("Dibujando polígono: mantenga presionado y mueva el mouse (libere para finalizar).")
        else:  # rectangle
            self.status("Dibujando rectángulo: haga click en esquina inicial, luego en esquina opuesta.")
        
        self.btn_new_poly.config(state=tk.DISABLED)
        self.redraw()

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
                    for i,(x,y) in enumerate(poly.world_points):
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

    def redraw(self):
        if self.img_array is None:
            return
        self.ax.clear()
        self.ax.imshow(self.img_array)
        self.ax.set_axis_off()
        # Draw control points
        for cp in self.control_points:
            color = 'lime' if cp.is_complete else 'yellow'
            self.ax.plot(cp.col, cp.row, 'o', color=color, markersize=6)
        # Draw polygons
        for poly in self.polygons:
            pix = poly.pixel_points
            xs = [p[0] for p in pix] + [pix[0][0]]
            ys = [p[1] for p in pix] + [pix[0][1]]
            self.ax.plot(xs, ys, '-', color='red', linewidth=1.5)
            # Label roughly at centroid of pixel points
            cx = np.mean([p[0] for p in pix])
            cy = np.mean([p[1] for p in pix])
            self.ax.text(cx, cy, poly.name, color='white', fontsize=8, ha='center', va='center')
        # Current drawing
        if self.drawing and self.current_poly_pixels:
            xs = [p[0] for p in self.current_poly_pixels]
            ys = [p[1] for p in self.current_poly_pixels]
            self.ax.plot(xs, ys, '-', color='cyan')
        
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

    def toggle_pan(self):
        """Toggle pan mode on/off"""
        self.pan_mode = not self.pan_mode
        if self.pan_mode:
            # Update left panel pan button
            self.pan_button.config(text="Pan (Activo)")
            self.pan_button.state(['pressed'])
            # Update image side pan button
            self.image_pan_btn.config(text="✋\nPan ON")
            self.image_pan_btn.state(['pressed'])
            self.status("Modo Pan activado. Arrastre para navegar por la imagen.")
        else:
            # Update left panel pan button
            self.pan_button.config(text="Pan (P)")
            self.pan_button.state(['!pressed'])
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
