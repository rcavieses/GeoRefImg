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
    pixel_rings: List[List[Tuple[float, float]]]  # Multiple rings (col,row)
    world_rings: List[List[Tuple[float, float]]]  # Multiple rings (x,y)
    id: int = field(default=0)
    
    @property
    def pixel_points(self):
        """Backward compatibility - returns first ring"""
        return self.pixel_rings[0] if self.pixel_rings else []
    
    @property 
    def world_points(self):
        """Backward compatibility - returns first ring"""
        return self.world_rings[0] if self.world_rings else []


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
        self.drawing_mode = "lines"  # "lines" or "rectangle"
        self.mouse_pressed = False
        self.rect_start = None
        self._last_mouse_pos = None
        self.current_poly_pixels = []  # Current ring being drawn
        self.current_polygon_rings = []  # All rings of current polygon
        self.current_polygon_name = None  # Name of polygon being drawn
        self.polygons = []
        self.next_poly_id = 1

        self._build_ui()

    # ---------------- UI BUILD -----------------
    def _build_ui(self):
        self.main_pane = ttk.Panedwindow(self.root, orient=tk.HORIZONTAL)
        self.main_pane.pack(fill=tk.BOTH, expand=True)

        # Left frame - controls
        self.left_frame = ttk.Frame(self.main_pane, padding=5)
        self.main_pane.add(self.left_frame, weight=0)

        # Right frame - figure
        self.right_frame = ttk.Frame(self.main_pane)
        self.main_pane.add(self.right_frame, weight=1)

        # Figure
        self.fig = Figure(figsize=(6, 6))
        self.ax = self.fig.add_subplot(111)
        self.ax.set_axis_off()
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.right_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.canvas.mpl_connect('button_press_event', self.on_click)
        self.canvas.mpl_connect('motion_notify_event', self.on_motion)
        self.canvas.mpl_connect('button_release_event', self.on_release)

        # Controls for stage 1
        ttk.Label(self.left_frame, text="Etapa 1: Puntos de Control").pack(anchor='w', pady=(0, 4))
        ttk.Button(self.left_frame, text="Cargar PNG", command=self.load_image).pack(fill='x')
        self.points_listbox = tk.Listbox(self.left_frame, height=8)
        self.points_listbox.pack(fill='both', expand=False, pady=4)
        btn_frame = ttk.Frame(self.left_frame)
        btn_frame.pack(fill='x')
        ttk.Button(btn_frame, text="Asignar Coord", command=self.assign_coord).pack(side=tk.LEFT, expand=True, fill='x')
        ttk.Button(btn_frame, text="Importar CSV", command=self.import_control_csv).pack(side=tk.LEFT, expand=True, fill='x')
        ttk.Button(self.left_frame, text="Calcular Transformación", command=self.compute_transform).pack(fill='x', pady=(4, 0))
        self.lbl_transform = ttk.Label(self.left_frame, text="Transformación: --")
        self.lbl_transform.pack(fill='x', pady=4)
        ttk.Button(self.left_frame, text="Guardar World File", command=self.save_world_file).pack(fill='x')
        self.btn_to_polys = ttk.Button(self.left_frame, text="Ir a Polígonos", command=self.go_to_polygons, state=tk.DISABLED)
        self.btn_to_polys.pack(fill='x', pady=(6, 10))

        # Separator for stage 2
        self.sep2 = ttk.Separator(self.left_frame, orient=tk.HORIZONTAL)
        self.sep2.pack(fill='x', pady=4)
        ttk.Label(self.left_frame, text="Etapa 2: Polígonos").pack(anchor='w')
        
        # Drawing mode selection
        mode_frame = ttk.Frame(self.left_frame)
        mode_frame.pack(fill='x', pady=2)
        self.mode_var = tk.StringVar(value="lines")
        ttk.Radiobutton(mode_frame, text="Líneas", variable=self.mode_var, value="lines").pack(side=tk.LEFT)
        ttk.Radiobutton(mode_frame, text="Rectángulo", variable=self.mode_var, value="rectangle").pack(side=tk.LEFT)
        
        self.btn_new_poly = ttk.Button(self.left_frame, text="Nuevo Polígono", command=self.start_polygon, state=tk.DISABLED)
        self.btn_new_poly.pack(fill='x', pady=2)
        self.btn_close_ring = ttk.Button(self.left_frame, text="Cerrar Anillo", command=self.close_current_ring, state=tk.DISABLED)
        self.btn_close_ring.pack(fill='x', pady=2)
        self.btn_add_ring = ttk.Button(self.left_frame, text="Agregar Anillo", command=self.start_new_ring, state=tk.DISABLED)
        self.btn_add_ring.pack(fill='x', pady=2)
        self.btn_finish_poly = ttk.Button(self.left_frame, text="Finalizar Polígono", command=self.finish_current_polygon, state=tk.DISABLED)
        self.btn_finish_poly.pack(fill='x', pady=2)
        self.btn_undo_poly = ttk.Button(self.left_frame, text="Eliminar Último", command=self.delete_last_polygon, state=tk.DISABLED)
        self.btn_undo_poly.pack(fill='x', pady=2)
        self.poly_listbox = tk.Listbox(self.left_frame, height=8)
        self.poly_listbox.pack(fill='both', expand=False, pady=4)
        ttk.Button(self.left_frame, text="Guardar Shapefile & CSV", command=self.export_polygons, state=tk.NORMAL).pack(fill='x', pady=(8, 4))
        self.status_var = tk.StringVar(value="Listo")
        ttk.Label(self.left_frame, textvariable=self.status_var, wraplength=220, foreground='blue').pack(fill='x', pady=(10,0))

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

    # -------------- CONTROL POINTS --------------
    def on_click(self, event):
        if event.inaxes != self.ax:
            return
        if self.stage == 1:
            if self.img_array is None:
                return
            self.control_points.append(ControlPoint(col=event.xdata, row=event.ydata))
            self.update_points_list()
            self.redraw()
        elif self.stage == 2:
            self.drawing_mode = self.mode_var.get()
            if self.drawing_mode == "lines" and self.drawing:
                # Add point for line drawing
                self.current_poly_pixels.append((event.xdata, event.ydata))
                self.redraw()
                # Check for double-click to finish polygon (or right-click in future)
                if len(self.current_poly_pixels) >= 3:
                    # Could add logic here to detect double-click or add finish button
                    pass
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
        
        if self.stage != 2 or not self.drawing:
            return
        if event.inaxes != self.ax:
            return
        if event.xdata is None or event.ydata is None:
            return
            
        self.drawing_mode = self.mode_var.get()
        if self.drawing_mode == "lines" and self.drawing and self.current_poly_pixels:
            # Show preview line to current mouse position
            self.redraw()
        elif self.drawing_mode == "rectangle" and self.rect_start:
            # Show preview of rectangle
            self.redraw()

    def on_release(self, event):
        # No longer needed for lines mode, only used for rectangle mode completion
        pass

    def _finish_polygon(self):
        """Helper function to complete polygon creation - only for rectangle mode"""
        if len(self.current_poly_pixels) > 2:
            name = simpledialog.askstring("Nombre", "Nombre del polígono:")
            if not name:
                name = f"Poly_{self.next_poly_id}"
            world_pts = [self.pixel_to_world(c, r) for c, r in self.current_poly_pixels]
            # Create single-ring polygon for backward compatibility
            poly = DigitizedPolygon(
                name=name, 
                pixel_rings=[list(self.current_poly_pixels)], 
                world_rings=[world_pts], 
                id=self.next_poly_id
            )
            self.polygons.append(poly)
            self.next_poly_id += 1
            self.poly_listbox.insert(tk.END, f"{poly.id}: {poly.name} (1 anillo, {len(world_pts)} vtx)")
            self.status(f"Polígono '{poly.name}' creado.")
        else:
            self.status("Polígono descartado: muy pocos puntos.")
        self.current_poly_pixels.clear()
        self.drawing = False
        self.redraw()
        self.btn_new_poly.config(state=tk.NORMAL)
        self.btn_close_ring.config(state=tk.DISABLED)
        self.btn_add_ring.config(state=tk.DISABLED)
        self.btn_finish_poly.config(state=tk.DISABLED)

    def assign_coord(self):
        sel = self.points_listbox.curselection()
        if not sel:
            messagebox.showinfo("Seleccione", "Seleccione un punto en la lista.")
            return
        idx = sel[0]
        cp = self.control_points[idx]
        x = simpledialog.askfloat("Asignar Longitud", f"Longitud para punto {idx} (formato: -116.5833):", initialvalue=cp.x if cp.x is not None else 0.0)
        if x is None:
            return
        y = simpledialog.askfloat("Asignar Latitud", f"Latitud para punto {idx} (formato: 31.8667):", initialvalue=cp.y if cp.y is not None else 0.0)
        if y is None:
            return
        cp.x, cp.y = x, y
        self.update_points_list()

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
            messagebox.showerror("Error", "CSV debe contener columnas x,y (longitud,latitud) y opcionalmente col,row")
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
        
        # Ask for polygon name at the beginning
        name = simpledialog.askstring("Nombre", "Nombre del polígono:")
        if not name:
            name = f"Poly_{self.next_poly_id}"
        
        self.drawing = True
        self.mouse_pressed = False
        self.rect_start = None
        self.current_poly_pixels.clear()
        self.current_polygon_rings.clear()
        self.current_polygon_name = name
        self.drawing_mode = self.mode_var.get()
        
        if self.drawing_mode == "lines":
            self.status(f"Dibujando '{name}': clic para puntos. 'Cerrar Anillo' para finalizar anillo actual.")
            self.btn_close_ring.config(state=tk.NORMAL)
            self.btn_add_ring.config(state=tk.DISABLED)
            self.btn_finish_poly.config(state=tk.NORMAL)
        else:  # rectangle
            self.status("Dibujando rectángulo: haga click en esquina inicial, luego en esquina opuesta.")
            self.btn_close_ring.config(state=tk.DISABLED)
            self.btn_add_ring.config(state=tk.DISABLED)
            self.btn_finish_poly.config(state=tk.DISABLED)
        
        self.btn_new_poly.config(state=tk.DISABLED)
        self.redraw()

    def close_current_ring(self):
        """Close the current ring and add it to the polygon"""
        if not self.drawing or self.drawing_mode != "lines":
            return
        if len(self.current_poly_pixels) < 3:
            self.status("Necesita al menos 3 puntos para cerrar un anillo.")
            return
        
        # Add current ring to polygon rings
        self.current_polygon_rings.append(list(self.current_poly_pixels))
        self.current_poly_pixels.clear()
        
        # Enable adding more rings
        self.btn_add_ring.config(state=tk.NORMAL)
        self.btn_close_ring.config(state=tk.DISABLED)
        
        self.status(f"Anillo cerrado. Total anillos: {len(self.current_polygon_rings)}. Puede agregar más anillos o finalizar.")
        self.redraw()

    def start_new_ring(self):
        """Start drawing a new ring for the current polygon"""
        if not self.drawing:
            return
        
        self.current_poly_pixels.clear()
        self.btn_add_ring.config(state=tk.DISABLED)
        self.btn_close_ring.config(state=tk.NORMAL)
        
        self.status(f"Dibujando nuevo anillo para '{self.current_polygon_name}': clic para agregar puntos.")
        self.redraw()

    def finish_current_polygon(self):
        """Finish the current polygon being drawn in lines mode"""
        if not self.drawing:
            return
        
        # If there's a current ring being drawn, ask to close it
        if self.current_poly_pixels and len(self.current_poly_pixels) >= 3:
            result = messagebox.askyesnocancel("Anillo abierto", 
                "Hay un anillo abierto. ¿Desea cerrarlo antes de finalizar?")
            if result is True:  # Yes
                self.close_current_ring()
            elif result is None:  # Cancel
                return
            # If No (False), continue without closing current ring
        
        if not self.current_polygon_rings:
            self.status("No hay anillos cerrados para guardar.")
            return
        
        self._save_multipolygon()

    def _save_multipolygon(self):
        """Save the current multi-ring polygon"""
        if not self.current_polygon_rings:
            return
        
        # Convert all rings to world coordinates
        world_rings = []
        for ring in self.current_polygon_rings:
            world_ring = [self.pixel_to_world(c, r) for c, r in ring]
            world_rings.append(world_ring)
        
        # Create polygon with multiple rings
        poly = DigitizedPolygon(
            name=self.current_polygon_name,
            pixel_rings=list(self.current_polygon_rings),
            world_rings=world_rings,
            id=self.next_poly_id
        )
        
        self.polygons.append(poly)
        self.next_poly_id += 1
        
        # Update UI
        total_vertices = sum(len(ring) for ring in world_rings)
        ring_count = len(world_rings)
        self.poly_listbox.insert(tk.END, f"{poly.id}: {poly.name} ({ring_count} anillos, {total_vertices} vtx)")
        self.status(f"Polígono '{poly.name}' guardado con {ring_count} anillos.")
        
        # Reset state
        self.current_poly_pixels.clear()
        self.current_polygon_rings.clear()
        self.current_polygon_name = None
        self.drawing = False
        
        # Reset button states
        self.btn_new_poly.config(state=tk.NORMAL)
        self.btn_close_ring.config(state=tk.DISABLED)
        self.btn_add_ring.config(state=tk.DISABLED)
        self.btn_finish_poly.config(state=tk.DISABLED)
        
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
                w.field('RINGS', 'N', decimal=0)  # Number of rings
                for poly in self.polygons:
                    # Handle multiple rings
                    all_rings = []
                    for ring in poly.world_rings:
                        # Ensure closed ring
                        if ring and ring[0] != ring[-1]:
                            ring = ring + [ring[0]]
                        all_rings.append(ring)
                    
                    if all_rings:
                        w.poly(all_rings)
                        w.record(poly.id, poly.name, len(all_rings))
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo escribir shapefile: {e}")
            return
        # Write vertices CSV
        try:
            with open(csv_path, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow(['poly_id','name','ring_id','vertex_index','x','y'])
                for poly in self.polygons:
                    for ring_idx, ring in enumerate(poly.world_rings):
                        for vertex_idx, (x, y) in enumerate(ring):
                            writer.writerow([poly.id, poly.name, ring_idx, vertex_idx, x, y])
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
                self.points_listbox.insert(tk.END, f"{i}: col={cp.col:.1f} row={cp.row:.1f} -> Lon={cp.x:.6f} Lat={cp.y:.6f}")
            else:
                self.points_listbox.insert(tk.END, f"{i}: col={cp.col:.1f} row={cp.row:.1f} -> (sin coordenadas)")
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
        # Draw polygons (all rings)
        for poly in self.polygons:
            # Draw all rings for each polygon
            for ring_idx, ring in enumerate(poly.pixel_rings):
                if not ring:
                    continue
                xs = [p[0] for p in ring] + [ring[0][0]]  # Close the ring
                ys = [p[1] for p in ring] + [ring[0][1]]
                color = 'red' if ring_idx == 0 else 'darkred'  # Different colors for outer/inner rings
                self.ax.plot(xs, ys, '-', color=color, linewidth=1.5)
            
            # Label at centroid of first ring
            if poly.pixel_rings and poly.pixel_rings[0]:
                first_ring = poly.pixel_rings[0]
                cx = np.mean([p[0] for p in first_ring])
                cy = np.mean([p[1] for p in first_ring])
                self.ax.text(cx, cy, poly.name, color='white', fontsize=8, ha='center', va='center')
        
        # Draw completed rings of current polygon being drawn
        for ring_idx, ring in enumerate(self.current_polygon_rings):
            if not ring:
                continue
            xs = [p[0] for p in ring] + [ring[0][0]]
            ys = [p[1] for p in ring] + [ring[0][1]]
            self.ax.plot(xs, ys, '-', color='orange', linewidth=2, alpha=0.8)
        
        # Current drawing (active ring)
        if self.drawing and self.current_poly_pixels:
            xs = [p[0] for p in self.current_poly_pixels]
            ys = [p[1] for p in self.current_poly_pixels]
            # Draw the current polygon lines
            if len(xs) > 1:
                self.ax.plot(xs, ys, 'o-', color='cyan', linewidth=2, markersize=4)
            else:
                self.ax.plot(xs, ys, 'o', color='cyan', markersize=6)
            
            # Show preview line to mouse cursor for lines mode
            if self.drawing_mode == "lines" and hasattr(self, '_last_mouse_pos') and self._last_mouse_pos:
                if len(self.current_poly_pixels) > 0:
                    last_x, last_y = self.current_poly_pixels[-1]
                    mouse_x, mouse_y = self._last_mouse_pos
                    self.ax.plot([last_x, mouse_x], [last_y, mouse_y], '--', color='cyan', alpha=0.7)
        
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


def main():
    root = tk.Tk()
    app = GeoRefApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
