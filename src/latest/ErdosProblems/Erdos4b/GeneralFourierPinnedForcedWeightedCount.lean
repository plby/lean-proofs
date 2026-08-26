/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedBilinear
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedCompatibility

/-!
# The forced weighted prime sum and its exact graph main term

Only supported coefficient pairs are required to satisfy the coordinate
bounds. The empty state at the forced prime retains its totient factor.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sum_pinnedForcedIntegerPrimeExpected_eq_graphKernel
    {K w m p₀ Y p a A B : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (hrough : ∀ r ∈ P, w < r) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hpP : p ∈ P)
    (b c : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ) → ℂ)
    (hsmall : ∀ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      b (fun i ↦ d i false) * c (fun i ↦ d i true) ≠ 0 →
        (∀ i t, d (.inl i) t < p₀) ∧ (∀ i t, d (.inr i) t ≤ Y)) :
    (∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      (b (fun i ↦ d i false) * c (fun i ↦ d i true)) *
        (pinnedForcedIntegerPrimeExpected h w m p₀ p a A B d : ℂ)) =
      ((auxiliaryPrimeInterval A B).card : ℂ) *
        cutoffForcedSelbergBilinearSum P (roughPinnedFourierEdges h w m p₀ Y)
          (truncatedPinnedFourierCompanion m Y) p (PinnedForcedLocalEquations h w m p₀ p a)
          b c := by
  classical
  rw [cutoffForcedSelbergBilinearSum_eq_raw_supported P hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : b (fun i ↦ d i false) * c (fun i ↦ d i true) = 0
  · simp only [hz, zero_mul, zero_div, ite_self, mul_zero]
  · obtain ⟨hD, hE⟩ := hsmall d hd hz
    have hi := pinnedForcedIntegerSolvable_iff_graph_and_local (a := a) h P hP hrough hKw
      hm hp₀ hcop hpP d ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd) hD hE
    simp only [← hi]
    unfold pinnedForcedIntegerPrimeExpected
    by_cases hs : PinnedForcedIntegerSolvable h w m p₀ p a d
    · simp only [if_pos hs, Complex.ofReal_div, Complex.ofReal_natCast,
        pinnedFlatDivisorModulus]
      ring
    · simp only [if_neg hs, Complex.ofReal_zero, mul_zero]

theorem norm_pinnedForcedWeightedPrimeCount_sub_graphKernel_le
    {K w m p₀ Y p a A B : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (hrough : ∀ r ∈ P, w < r) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hpP : p ∈ P) (ha : a.Coprime p)
    (hA : 0 < A) (hAB : A ≤ B)
    (b c : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ) → ℂ)
    (hsmall : ∀ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      b (fun i ↦ d i false) * c (fun i ↦ d i true) ≠ 0 →
        (∀ i t, d (.inl i) t < p₀) ∧ (∀ i t, d (.inr i) t ≤ Y)) :
    ‖(∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      (b (fun i ↦ d i false) * c (fun i ↦ d i true)) *
        (pinnedForcedIntegerPrimeCount h w m p₀ p a A B d : ℂ)) -
      ((auxiliaryPrimeInterval A B).card : ℂ) *
        cutoffForcedSelbergBilinearSum P (roughPinnedFourierEdges h w m p₀ Y)
          (truncatedPinnedFourierCompanion m Y) p (PinnedForcedLocalEquations h w m p₀ p a)
          b c‖ ≤
      ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
        ‖b (fun i ↦ d i false) * c (fun i ↦ d i true)‖ *
          (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
            (Nat.lcm (pinnedFlatDivisorModulus h d) p) +
          BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
            (Nat.lcm (pinnedFlatDivisorModulus h d) p)) := by
  rw [← sum_pinnedForcedIntegerPrimeExpected_eq_graphKernel h P hP hrough hKw hm hp₀
    hcop hpP b c hsmall, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  by_cases hz : b (fun i ↦ d i false) * c (fun i ↦ d i true) = 0
  · simp only [hz, zero_mul, sub_self, norm_zero, le_refl]
  · obtain ⟨hD, hE⟩ := hsmall d hd hz
    have herror := abs_pinnedForcedIntegerPrimeCount_sub_expected_le h P hP hrough hKw
      hm hp₀ hcop (hP p hpP).pos ha hA hAB d
      ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd) hD hE
    rw [← mul_sub, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hid : (pinnedForcedIntegerPrimeCount h w m p₀ p a A B d : ℂ) -
        (pinnedForcedIntegerPrimeExpected h w m p₀ p a A B d : ℂ) =
        (((pinnedForcedIntegerPrimeCount h w m p₀ p a A B d : ℝ) -
          pinnedForcedIntegerPrimeExpected h w m p₀ p a A B d : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hid, Complex.norm_real, Real.norm_eq_abs]
    exact herror

end

end Erdos4b
