def _ask_polygon_name(self) -> str:
    """Ask user for a polygon name and return it"""
    name = simpledialog.askstring("Nombre del Polígono", 
                                "Introduzca un nombre para el polígono:",
                                initialvalue=f"Polígono {self.next_poly_id}")
    if not name:
        name = f"Polígono {self.next_poly_id}"
    return name