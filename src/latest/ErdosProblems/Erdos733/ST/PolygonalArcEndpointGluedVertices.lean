import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcEndpointGluedVertices]
def PolygonalArcEndpointGluedVertices
    (pieces : List PolygonalArc) : List (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  match pieces with
  | [] => []
  | Γ :: rest => Γ.vertices ++ (rest.map (fun Δ => Δ.vertices.tail)).flatten
