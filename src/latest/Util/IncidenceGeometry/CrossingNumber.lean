import Util.IncidenceGeometry.OrdinaryPolygonalDrawing

open Classical
noncomputable section

noncomputable def CrossingNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : ℕ :=
  sInf (Set.range (fun D : OrdinaryPolygonalDrawing G => D.crossingSet.card))
