/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Counting inequalities for the layered lower construction

These are deliberately stated over `ℝ`: this is the form used after dividing
cardinalities by the cardinality of the finite outcome space.
-/

namespace Erdos182

open scoped Nat

/-- The usual estimate `choose n k ≤ (e n / k)^k`, with the harmless
constant `3` in place of `e`.  The formulation at `k = 0` is also valid. -/
theorem natCast_choose_le_three_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp
  by_cases hkn : n < k
  · rw [Nat.choose_eq_zero_of_lt hkn]
    simpa only [Nat.cast_zero] using
      (pow_nonneg (by positivity : 0 ≤ 3 * (n : ℝ) / (k : ℝ)) k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hfacpos : (0 : ℝ) < k ! := by positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) ≤ Real.pi := (Real.pi_gt_three : (3 : ℝ) < Real.pi).le
    nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk]
  have hstirling : ((k : ℝ) / Real.exp 1) ^ k ≤ (k ! : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤
          Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (k ! : ℝ) := Stirling.le_factorial_stirling k
  have he3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k ! : ℝ) := by
    exact Nat.choose_le_pow_div k n
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k ! : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / Real.exp 1) ^ k) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hstirling
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      simp only [div_pow]
      field_simp
      <;> ring
    _ ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
      gcongr

end Erdos182
