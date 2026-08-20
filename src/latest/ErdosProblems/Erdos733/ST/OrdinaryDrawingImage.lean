import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingImage]
def OrdinaryDrawingImage {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  Set.range D.vertexPlacement ∪ ⋃ e : G.edgeFinset, (D.edgeArc e).carrier
