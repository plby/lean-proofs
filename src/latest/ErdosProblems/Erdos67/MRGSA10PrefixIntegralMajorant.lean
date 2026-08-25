import ErdosProblems.Erdos67.MRGSA10ShiuMean

/-!
# Generic prefix and interval majorants for GS A.10

These two elementary estimates are the aggregation step used after the
coefficientwise Shiu majorants.  They are deliberately independent of the
special A.10 coefficients: the alternating low coefficient is kept whole by
the caller, and this file introduces no deletion-by-deletion estimate.
-/

open scoped BigOperators
open Finset Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- A pointwise nonnegative majorant on the positive prefix controls the norm
of the whole complex prefix by its ordinary partial sum. -/
theorem norm_positivePrefixSum_le_partialSum
    {a : ℕ → ℂ} {w : ℕ → ℝ} {X : ℕ}
    (hmajor : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ w n) :
    ‖positivePrefixSum a X‖ ≤
      HalberstamScratch.partialSum w X := by
  have hset : Finset.Icc 1 X = Finset.Ico 1 (X + 1) := by
    ext n
    simp
  have hprefix : positivePrefixSum a X =
      ∑ n ∈ Finset.Icc 1 X, a n := by
    unfold positivePrefixSum
    rw [hset, Finset.sum_Ico_eq_sub a (by omega)]
    simp
  rw [hprefix]
  calc
    ‖∑ n ∈ Finset.Icc 1 X, a n‖ ≤
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, w n := by
      exact Finset.sum_le_sum hmajor
    _ = HalberstamScratch.partialSum w X := by
      rfl

/-- A uniform prefix bound on a nonnegative interval controls the norm of its
interval average with the exact interval length. -/
theorem norm_intervalIntegral_positivePrefixSum_le
    {a : ℝ → ℕ → ℂ} {X : ℕ} {eta B : ℝ}
    (heta : 0 ≤ eta)
    (hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ‖positivePrefixSum (a alpha) X‖ ≤ B) :
    ‖∫ alpha in 0..eta, positivePrefixSum (a alpha) X‖ ≤
      eta * B := by
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun alpha : ℝ ↦ positivePrefixSum (a alpha) X)
    (C := B) (a := (0 : ℝ)) (b := eta) (fun alpha halpha ↦ by
      rw [Set.uIoc_of_le heta] at halpha
      exact hmajor alpha ⟨halpha.1.le, halpha.2⟩)
  simpa [abs_of_nonneg heta, mul_comm] using hraw

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.norm_positivePrefixSum_le_partialSum
#print axioms Erdos67.MRHalaszBands.norm_intervalIntegral_positivePrefixSum_le
