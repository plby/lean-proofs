/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLostVertexCount

/-! # Exact reindexing of the literal prime-edge probabilities -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem SourceProbabilityData.pinnedTranslation_injective {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℤ) {p : ℕ} (hp : 0 < p) :
    Function.Injective (fun i : Fin D.dimension => q - (D.shifts i : ℤ) * p) := by
  intro i j h
  apply D.shifts_injective
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmul : (D.shifts i : ℤ) * p = (D.shifts j : ℤ) * p := by linarith
  exact_mod_cast mul_right_cancel₀ hp0 hmul

open scoped Classical in
theorem SourceProbabilityData.primeTupleEdge_translations_eq_image {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (S Q : Finset ℕ) (a : ResidueAssignment S) {p q : ℕ}
    (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (hq : q ∈ Q)
    (hqy : (q : ℝ) ≤ sourceIntervalLength c x) (hsurv : residueAssignmentAvoids S {(q : ℤ)} a) :
    ((integerWeightWindow (sourceIntervalLength c x)).filter fun n =>
      q ∈ D.primeTupleEdge S Q a p n) =
        Finset.univ.image (fun i : Fin D.dimension => (q : ℤ) - (D.shifts i : ℤ) * p) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨_hnwin, hnedge⟩ := Finset.mem_filter.mp hn
    have htuple := ((D.mem_primeTupleEdge S Q a p n q).mp hnedge).2.1
    obtain ⟨i, hi⟩ := (D.mem_residueTuple p n q).mp htuple
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by omega⟩
  · intro hn
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_filter.mpr ⟨D.pinnedTranslation_mem_window hshift hqy hp i, ?_⟩
    apply (D.mem_primeTupleEdge S Q a p _ q).mpr
    refine ⟨hq, ?_, hsurv⟩
    rw [D.mem_residueTuple]
    exact ⟨i, by ring⟩

theorem SourceProbabilityData.primeTupleEdgeProbability_eq_pinned_conditioned {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (S Q : Finset ℕ) (a : ResidueAssignment S) {p q : ℕ}
    (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (hq : q ∈ Q)
    (hqy : (q : ℝ) ≤ sourceIntervalLength c x) (hsurv : residueAssignmentAvoids S {(q : ℤ)} a) :
    D.primeTupleEdgeProbability S Q a p q =
      ∑ i : Fin D.dimension, D.conditionedTupleMass S a p ((q : ℤ) - (D.shifts i : ℤ) * p) := by
  classical
  unfold primeTupleEdgeProbability
  rw [← Finset.sum_filter, D.primeTupleEdge_translations_eq_image hshift S Q a hp hq hqy hsurv]
  exact Finset.sum_image (fun i _hi j _hj h =>
    D.pinnedTranslation_injective q (mem_commonPinnedPrimeSet.mp hp).2.2.pos h)

theorem SourceProbabilityData.primeTupleEdgeProbability_eq_good_pinned {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (S Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (a : ResidueAssignment S) {p q : ℕ}
    (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (hq : q ∈ Q)
    (hqy : (q : ℝ) ≤ sourceIntervalLength c x) (hsurv : residueAssignmentAvoids S {(q : ℤ)} a) :
    D.primeTupleEdgeProbability S Q a p q =
      if p ∈ D.badTuplePrimes S a then 0 else
        (∑ i : Fin D.dimension,
          D.survivingTupleWeight S a p ((q : ℤ) - (D.shifts i : ℤ) * p)) /
            D.tupleSurvivalMass S p a := by
  classical
  by_cases hbad : p ∈ D.badTuplePrimes S a
  · rw [if_pos hbad, D.primeTupleEdgeProbability_zero_of_bad S Q hQ a hp hbad q]
  · rw [if_neg hbad, D.primeTupleEdgeProbability_eq_pinned_conditioned hshift S Q a hp hq hqy hsurv]
    simp only [conditionedTupleMass, if_neg hbad, survivingTupleWeight, Finset.sum_div]

theorem SourceProbabilityData.pinnedGoodMass_eq_prime_sum {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ) (a : ResidueAssignment S) :
    D.pinnedGoodMass S q a =
      ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
        if p ∈ D.badTuplePrimes S a then 0 else
          (∑ i : Fin D.dimension,
            D.survivingTupleWeight S a p ((q : ℤ) - (D.shifts i : ℤ) * p)) /
              residueSieveDensity S ^ D.dimension := by
  classical
  unfold pinnedGoodMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hbad : p ∈ D.badTuplePrimes S a <;>
    simp only [hbad, ↓reduceIte, Finset.sum_const_zero, Finset.sum_div]

end

end Erdos4b.FGKMT
