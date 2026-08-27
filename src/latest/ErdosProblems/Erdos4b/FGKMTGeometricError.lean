/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Exact accumulation of errors in positive coordinate sums

This finite inequality retains the geometric error. In particular no
constant depending on the number of coordinates is hidden in an
asymptotic notation.
-/

namespace Erdos4b.FGKMT

theorem geometric_error_step {A B c Q T U : ℝ} (j : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hstep : |U - c * A * T| ≤ c * B * T)
    (htail : |T - Q * A ^ j| ≤ Q * ((A + B) ^ j - A ^ j)) :
    |U - (c * Q) * A ^ (j + 1)| ≤
      (c * Q) * ((A + B) ^ (j + 1) - A ^ (j + 1)) := by
  have hT : T ≤ Q * (A + B) ^ j := by
    have h := (le_abs_self (T - Q * A ^ j)).trans htail
    nlinarith
  have hidentity : U - (c * Q) * A ^ (j + 1) =
      (U - c * A * T) + (c * A) * (T - Q * A ^ j) := by
    rw [pow_succ]
    ring
  rw [hidentity]
  calc
    _ ≤ |U - c * A * T| + |(c * A) * (T - Q * A ^ j)| := abs_add_le _ _
    _ = |U - c * A * T| + (c * A) * |T - Q * A ^ j| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hc hA)]
    _ ≤ c * B * T + (c * A) * (Q * ((A + B) ^ j - A ^ j)) :=
      add_le_add hstep (mul_le_mul_of_nonneg_left htail (mul_nonneg hc hA))
    _ ≤ c * B * (Q * (A + B) ^ j) + (c * A) * (Q * ((A + B) ^ j - A ^ j)) :=
      add_le_add (mul_le_mul_of_nonneg_left hT (mul_nonneg hc hB)) le_rfl
    _ = _ := by rw [pow_succ, pow_succ]; ring

theorem one_add_pow_sub_one_le_linear {ε : ℝ} (hε : 0 ≤ ε) (j : ℕ)
    (hj : (j : ℝ) * ε ≤ 1) : (1 + ε) ^ j - 1 ≤ 2 * (j : ℝ) * ε := by
  have hj0 : 0 ≤ (j : ℝ) * ε := mul_nonneg (Nat.cast_nonneg j) hε
  have hbase : 1 + ε ≤ Real.exp ε := by linarith [Real.add_one_le_exp ε]
  have hpow : (1 + ε) ^ j ≤ Real.exp ((j : ℝ) * ε) := by
    calc
      _ ≤ (Real.exp ε) ^ j := pow_le_pow_left₀ (by linarith) hbase j
      _ = _ := by rw [Real.exp_nat_mul]
  have hexp := Real.abs_exp_sub_one_le (x := (j : ℝ) * ε)
    (by rwa [abs_of_nonneg hj0])
  rw [abs_of_nonneg hj0] at hexp
  have hle := le_abs_self (Real.exp ((j : ℝ) * ε) - 1)
  linarith

theorem geometric_error_le_linear {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hBA : B ≤ A * ε) (j : ℕ) (hj : (j : ℝ) * ε ≤ 1) :
    (A + B) ^ j - A ^ j ≤ A ^ j * (2 * (j : ℝ) * ε) := by
  have hbase : A + B ≤ A * (1 + ε) := by linarith
  calc
    _ ≤ (A * (1 + ε)) ^ j - A ^ j :=
      sub_le_sub_right (pow_le_pow_left₀ (add_nonneg hA hB) hbase j) _
    _ = A ^ j * ((1 + ε) ^ j - 1) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_add_pow_sub_one_le_linear hε j hj)
      (pow_nonneg hA j)

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.geometric_error_step
