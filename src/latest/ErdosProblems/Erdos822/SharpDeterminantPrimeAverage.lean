/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SharpDeterminantFiber

/-! # The prime-square-tail saving in the determinant first moment -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem sum_inv_sq_smallDeterminantPrimes_le_prime_tail
    {U z k r h : ℕ} :
    (∑ p ∈ smallDeterminantPrimes U z k r h, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      ∑ p ∈ (Nat.primesLE U).filter (fun p ↦ z < p), (1 : ℝ) / (p : ℝ) ^ 2 := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpdata := mem_smallDeterminantPrimes_iff.mp hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpdata.2.1, hpdata.2.2.1⟩, hpdata.1⟩
  · intro p hp hnot
    positivity

theorem exists_eventually_sharp_smallDeterminantPrime_average (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (B : Finset ℕ) (x k r m' h U z cutoff : ℕ),
        k ∈ oddSmallFactors N → r ∈ middlePrimes N → 0 < m' →
        (∀ q ∈ largePrimes N, ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s) →
        (∀ s ∈ outerPrimes x m', m' < s) →
        B ⊆ largeGcdFreeOddCofactors N cutoff →
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ) →
        0 < h → h ≤ N ^ 3 → primeDivisorReciprocalMass h ≤ C → U ≤ N → 2 ≤ z →
        (∑ p ∈ smallDeterminantPrimes U z k r h, ((1 : ℝ) / p) *
          ∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h, (1 : ℝ) / q) ≤
          K / ((h : ℝ) * z * Real.log (z : ℝ)) := by
  obtain ⟨D, hD, htail⟩ := exists_sum_inv_sq_primesAbove_le
  obtain ⟨K, hK, hbound⟩ := exists_eventually_sharp_smallDeterminantFiber_bound C
  refine ⟨K * D, by positivity, ?_⟩
  filter_upwards [hbound] with N hbound
  intro B x k r m' h U z cutoff hk hr hm' hlarge hlarge' hB hsupport hh hhN hmass hUN hz
  have hpoint (p : ℕ) (hp : p ∈ smallDeterminantPrimes U z k r h) :
      (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h, (1 : ℝ) / q) ≤ K / (p * h : ℕ) := by
    have hdata := mem_smallDeterminantPrimes_iff.mp hp
    exact hbound B x k r m' p h cutoff hdata.2.2.1 (hdata.2.1.trans hUN)
      hk hr hm' hlarge hlarge' hdata.2.2.2.1 hdata.2.2.2.2.1 hB hsupport
      hdata.2.2.2.2.2 hh hhN hmass
  calc
    _ ≤ ∑ p ∈ smallDeterminantPrimes U z k r h, ((1 : ℝ) / p) * (K / (p * h : ℕ)) :=
      Finset.sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_left (hpoint p hp) (by positivity)
    _ = (K / h) * ∑ p ∈ smallDeterminantPrimes U z k r h, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      push_cast
      ring
    _ ≤ (K / h) * (D / ((z : ℝ) * Real.log (z : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (sum_inv_sq_smallDeterminantPrimes_le_prime_tail.trans (htail U z hz)) (by positivity)
    _ = _ := by ring

#print axioms exists_eventually_sharp_smallDeterminantPrime_average

end Erdos822
