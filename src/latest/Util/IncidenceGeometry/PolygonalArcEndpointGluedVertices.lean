import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

def PolygonalArcEndpointGluedVertices
    (pieces : List PolygonalArc) : List (EuclideanSpace ℝ (Fin 2)) :=
  match pieces with
  | [] => []
  | Γ :: rest => Γ.vertices ++ (rest.map (fun Δ => Δ.vertices.tail)).flatten
