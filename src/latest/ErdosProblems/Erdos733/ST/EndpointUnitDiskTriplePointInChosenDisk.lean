import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskTriplePointInChosenDisk]
lemma EndpointUnitDiskTriplePointInChosenDisk {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hT : ∀ z, z ∈ T ↔
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ∃ i j k : ι,
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            z ∈ openSegment ℝ (a i) (b i) ∧
              z ∈ openSegment ℝ (a j) (b j) ∧
                z ∈ openSegment ℝ (a k) (b k))
    (hrpos : ∀ z ∈ T, 0 < r z)
    {p : EuclideanSpace ℝ (Fin 2)}
    (hpball : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpi : p ∈ openSegment ℝ (a i) (b i))
    (hpj : p ∈ openSegment ℝ (a j) (b j))
    (hpk : p ∈ openSegment ℝ (a k) (b k)) :
    ∃ z, z ∈ T ∧ p ∈ Metric.closedBall z (r z) := by
-- BODY
  have hpT : p ∈ T :=
    (hT p).2 ⟨hpball, ⟨i, j, k, hij, hik, hjk, hpi, hpj, hpk⟩⟩
  refine ⟨p, hpT, ?_⟩
  simpa [Metric.mem_closedBall] using (le_of_lt (hrpos p hpT) : (0 : ℝ) ≤ r p)
