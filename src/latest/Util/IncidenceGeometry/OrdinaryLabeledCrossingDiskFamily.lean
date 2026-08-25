import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskData

open Classical
noncomputable section

structure OrdinaryLabeledCrossingDiskFamily {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) where
  disk :
    ∀ x : {p // p ∈ D.crossingSet}, OrdinaryLabeledCrossingDiskData G D x
  closedBalls_pairwise_disjoint :
    ∀ ⦃x y : {p // p ∈ D.crossingSet}⦄,
      x ≠ y →
        Disjoint (Metric.closedBall x.1 (disk x).radius)
          (Metric.closedBall y.1 (disk y).radius)
