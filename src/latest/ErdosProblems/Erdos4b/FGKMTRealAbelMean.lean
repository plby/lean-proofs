/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTHarmonicMean
import BoundedGaps.Maynard.WeightedSmoothAbel

/-!
# Real endpoints for the cumulative mean

Passing from the integer endpoint to its real argument costs at most
the main density times `log 2`. The contribution at zero stays zero,
matching the exact cumulative function in the Abel-summation API.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem log_sub_log_natFloor_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ Real.log t - Real.log (Nat.floor t) ∧
      Real.log t - Real.log (Nat.floor t) ≤ Real.log 2 := by
  have hn : 1 ≤ Nat.floor t := Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  have hnR : (1 : ℝ) ≤ Nat.floor t := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < Nat.floor t := by linarith
  have hnt : (Nat.floor t : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htn := Nat.lt_floor_add_one t
  have hdouble : t ≤ 2 * (Nat.floor t : ℝ) := by linarith
  have hlower := Real.log_le_log hn0 hnt
  have hupper := Real.log_le_log (by linarith : 0 < t) hdouble
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne'] at hupper
  constructor <;> linarith

theorem sum_Icc_zero_eq_sum_Ioc {c : ℕ → ℝ} (hc : c 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, c n) = ∑ n ∈ Finset.Ioc 0 N, c n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨hn0.le, hnN⟩
  · intro n hn hnnot
    have hnN := (Finset.mem_Icc.mp hn).2
    have hn0 : n = 0 := by
      by_contra hnot
      exact hnnot (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hnot, hnN⟩)
    simpa only [hn0] using hc

theorem abelCumulative_error_of_integer_bounds {c : ℕ → ℝ} (hc : c 0 = 0)
    {S E : ℝ} (hS : 0 ≤ S)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Ioc 0 N, c n) - S * Real.log N| ≤ E)
    {t : ℝ} (ht : 1 ≤ t) :
    |BoundedGaps.Maynard.abelCumulative c t - S * Real.log t| ≤ E + S * Real.log 2 := by
  obtain ⟨hlog0, hlog2⟩ := log_sub_log_natFloor_bounds ht
  have hnatural := hbound (Nat.floor t)
    (Nat.le_floor (by simpa only [Nat.cast_one] using ht))
  have hshift : |S * Real.log (Nat.floor t) - S * Real.log t| ≤ S * Real.log 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hS,
      abs_of_nonpos (by linarith : Real.log (Nat.floor t) - Real.log t ≤ 0)]
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hS]
  have hid : BoundedGaps.Maynard.abelCumulative c t =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor t), c n := sum_Icc_zero_eq_sum_Ioc hc _
  calc
    _ ≤ |BoundedGaps.Maynard.abelCumulative c t - S * Real.log (Nat.floor t)| +
        |S * Real.log (Nat.floor t) - S * Real.log t| :=
      abs_sub_le _ _ _
    _ ≤ E + S * Real.log 2 := by
      rw [hid]
      exact add_le_add hnatural hshift

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.abelCumulative_error_of_integer_bounds
