import Util.IncidenceGeometry.OrdinaryPolygonalDrawing

open Classical
noncomputable section

def OrdinaryDrawingImage {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Set.range D.vertexPlacement ∪ ⋃ e : G.edgeFinset, (D.edgeArc e).carrier
