import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingImageWithoutEdge]
def OrdinaryDrawingImageWithoutEdge {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  Set.range D.vertexPlacement ∪
    ⋃ f : {f : G.edgeFinset // f ≠ e}, (D.edgeArc f.1).carrier
