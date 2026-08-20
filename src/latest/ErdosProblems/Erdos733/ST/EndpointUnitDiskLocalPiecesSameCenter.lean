import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskLocalPiecesSameCenter]
lemma EndpointUnitDiskLocalPiecesSameCenter
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hdisjoint : ∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → w ∈ T → z ≠ w →
        Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)))
    {z w : EuclideanSpace ℝ (Fin 2)}
    (hzT : z ∈ T) (hwT : w ∈ T)
    {Ξz Ξw : PolygonalArc}
    (hzcarrier : Ξz.carrier ⊆ Metric.closedBall z (r z))
    (hwcarrier : Ξw.carrier ⊆ Metric.closedBall w (r w))
    {p : EuclideanSpace ℝ (Fin 2)}
    (hpz : p ∈ Ξz.relativeInterior)
    (hpw : p ∈ Ξw.relativeInterior) :
    z = w := by
-- BODY
  by_contra hne
  have hpzCarrier : p ∈ Ξz.carrier := by
    have hp' := hpz
    rw [Ξz.relativeInterior_eq] at hp'
    exact hp'.1
  have hpwCarrier : p ∈ Ξw.carrier := by
    have hp' := hpw
    rw [Ξw.relativeInterior_eq] at hp'
    exact hp'.1
  have hpzBall : p ∈ Metric.closedBall z (r z) := hzcarrier hpzCarrier
  have hpwBall : p ∈ Metric.closedBall w (r w) := hwcarrier hpwCarrier
  have hdis : Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w)) :=
    hdisjoint hzT hwT hne
  rw [Set.disjoint_left] at hdis
  exact hdis hpzBall hpwBall
