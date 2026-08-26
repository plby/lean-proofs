/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeCount
import ErdosProblems.Erdos4b.GeneralFourierTotientCoefficientSquare
import ErdosProblems.Erdos4b.GeneralFourierRawCrtKernel

/-!
# The finite pinned weighted prime sum and the totient graph kernel

Every raw divisor quadruple is retained. The expected count vanishes
outside the within-family and graph restrictions. The error is bounded
by a literal coefficient-weighted sum of progression discrepancies.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

open Classical in
theorem cutoffTotientSelbergBilinearSum_eq_raw_supported
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (a b : ((ι ⊕ ι) → ℕ) → ℂ) :
    cutoffTotientSelbergBilinearSum P edges companion a b =
      ∑ d ∈ rawDoubledCutoffDivisorTuples ι P,
        if d ∈ doubledCutoffDivisorTuples ι P ∧ DoubledDivisorPrimeCompatible P edges companion d
        then a (fun i ↦ d i false) * b (fun i ↦ d i true) /
          ((Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
            (fun ib ↦ d ib.1 ib.2)) : ℕ) : ℂ) else 0 := by
  classical
  have hsubset : doubledCutoffDivisorTuples ι P ⊆ rawDoubledCutoffDivisorTuples ι P := by
    intro d hd
    exact (mem_rawDoubledCutoffDivisorTuples P hP d).mpr
      ((mem_doubledCutoffDivisorTuples P hP d).mp hd).1
  unfold cutoffTotientSelbergBilinearSum
  calc
    _ = ∑ d ∈ doubledCutoffDivisorTuples ι P,
        if d ∈ doubledCutoffDivisorTuples ι P ∧ DoubledDivisorPrimeCompatible P edges companion d
        then a (fun i ↦ d i false) * b (fun i ↦ d i true) /
          ((Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
            (fun ib ↦ d ib.1 ib.2)) : ℕ) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [hd, true_and]
    _ = _ := Finset.sum_subset hsubset (fun d hd hn ↦ by simp only [hn, false_and, if_false])

theorem sum_pinnedIntegerDivisorPrimeExpected_eq_totientKernel
    {K w m p₀ Y A B : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a b : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ) → ℂ) :
    (∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      (a (fun i ↦ d i false) * b (fun i ↦ d i true)) *
        (pinnedIntegerDivisorPrimeExpected h P w m p₀ Y A B d : ℂ)) =
      ((auxiliaryPrimeInterval A B).card : ℂ) *
        cutoffTotientSelbergBilinearSum P (roughPinnedFourierEdges h w m p₀ Y)
          (truncatedPinnedFourierCompanion m Y) a b := by
  classical
  rw [cutoffTotientSelbergBilinearSum_eq_raw_supported P hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  unfold pinnedIntegerDivisorPrimeExpected
  split_ifs with hc
  · simp only [Complex.ofReal_div, Complex.ofReal_natCast, pinnedFlatDivisorModulus]
    ring
  · simp only [Complex.ofReal_zero, mul_zero]

theorem norm_pinnedWeightedPrimeCount_sub_totientKernel_le
    {K w m p₀ Y A B : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hA : 0 < A) (hAB : A ≤ B)
    (a b : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ) → ℂ)
    (hsmall : ∀ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      a (fun i ↦ d i false) * b (fun i ↦ d i true) ≠ 0 →
        (∀ i c, d (.inl i) c < p₀) ∧ (∀ i c, d (.inr i) c ≤ Y)) :
    ‖(∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
      (a (fun i ↦ d i false) * b (fun i ↦ d i true)) *
        (pinnedIntegerDivisorPrimeCount h w m p₀ A B d : ℂ)) -
      ((auxiliaryPrimeInterval A B).card : ℂ) *
        cutoffTotientSelbergBilinearSum P (roughPinnedFourierEdges h w m p₀ Y)
          (truncatedPinnedFourierCompanion m Y) a b‖ ≤
      ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
        ‖a (fun i ↦ d i false) * b (fun i ↦ d i true)‖ *
          (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) (pinnedFlatDivisorModulus h d) +
            BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
              (pinnedFlatDivisorModulus h d)) := by
  rw [← sum_pinnedIntegerDivisorPrimeExpected_eq_totientKernel h P hP a b,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  by_cases hz : a (fun i ↦ d i false) * b (fun i ↦ d i true) = 0
  · simp only [hz, zero_mul, sub_self, norm_zero, le_refl]
  · obtain ⟨hD, hE⟩ := hsmall d hd hz
    have herror := abs_pinnedIntegerDivisorPrimeCount_sub_expected_le h P hP hrough hKw
      hm hp₀ hcop hA hAB d ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd) hD hE
    rw [← mul_sub, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hid : (pinnedIntegerDivisorPrimeCount h w m p₀ A B d : ℂ) -
        (pinnedIntegerDivisorPrimeExpected h P w m p₀ Y A B d : ℂ) =
        (((pinnedIntegerDivisorPrimeCount h w m p₀ A B d : ℝ) -
          pinnedIntegerDivisorPrimeExpected h P w m p₀ Y A B d : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hid, Complex.norm_real, Real.norm_eq_abs]
    exact herror

end

end Erdos4b
