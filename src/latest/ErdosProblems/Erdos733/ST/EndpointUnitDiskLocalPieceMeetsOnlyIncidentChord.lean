import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskLocalPieceMeetsOnlyIncidentChord]
lemma EndpointUnitDiskLocalPieceMeetsOnlyIncidentChord {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hmiss : ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
      z ∈ T → ∀ i,
        z ∉ segment ℝ (a i) (b i) →
          Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)))
    {z : EuclideanSpace ℝ (Fin 2)}
    (hzT : z ∈ T)
    {i : ι}
    (hnot : z ∉ segment ℝ (a i) (b i))
    {Ξ : PolygonalArc}
    (hcarrier : Ξ.carrier ⊆ Metric.closedBall z (r z))
    {p : EuclideanSpace ℝ (Fin 2)}
    (hpΞ : p ∈ Ξ.relativeInterior)
    (hpseg : p ∈ segment ℝ (a i) (b i)) :
    False := by
-- BODY
  have hpCarrier : p ∈ Ξ.carrier := by
    have hp' := hpΞ
    rw [Ξ.relativeInterior_eq] at hp'
    exact hp'.1
  have hpball : p ∈ Metric.closedBall z (r z) := hcarrier hpCarrier
  have hdis : Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i)) :=
    hmiss hzT i hnot
  rw [Set.disjoint_left] at hdis
  exact hdis hpball hpseg
