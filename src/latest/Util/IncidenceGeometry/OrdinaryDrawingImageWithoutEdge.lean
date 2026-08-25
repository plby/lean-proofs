import Util.IncidenceGeometry.OrdinaryPolygonalDrawing

open Classical
noncomputable section

def OrdinaryDrawingImageWithoutEdge {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Set.range D.vertexPlacement ∪
    ⋃ f : {f : G.edgeFinset // f ≠ e}, (D.edgeArc f.1).carrier
