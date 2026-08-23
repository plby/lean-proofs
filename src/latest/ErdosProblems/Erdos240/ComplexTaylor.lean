/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Explicit Taylor bounds for the complex exponential

The elementary estimate in this file is uniform in both the complex
argument and the truncation order.  A second version factors out the value
of the exponential at an arbitrary base point.  We also record Mathlib's
sharper factorial estimate in the range where the tail is geometrically
decreasing by a factor at most `1 / 2`.
-/

namespace Erdos240.ComplexTaylor

open Finset

/-- The degree-`N - 1` Taylor polynomial for the complex exponential at
zero.  For `N = 0` this is the empty sum. -/
noncomputable def expPartialSum (z : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, z ^ k / k.factorial

@[simp]
lemma expPartialSum_zero (z : ℂ) : expPartialSum z 0 = 0 := by
  simp [expPartialSum]

@[simp]
lemma expPartialSum_succ (z : ℂ) (N : ℕ) :
    expPartialSum z (N + 1) =
      expPartialSum z N + z ^ N / N.factorial := by
  simp [expPartialSum, sum_range_succ]

/-- A global explicit remainder bound for the complex exponential series. -/
theorem norm_exp_sub_partialSum_le (z : ℂ) (N : ℕ) :
    ‖Complex.exp z - expPartialSum z N‖ ≤
      Real.exp ‖z‖ * ‖z‖ ^ N := by
  simpa only [expPartialSum, mul_comm] using
    Complex.norm_exp_sub_sum_le_norm_mul_exp z N

/-- When the first omitted term is already in the geometric-decay range,
one retains the factorial in the denominator. -/
theorem norm_exp_sub_partialSum_le_two_mul_div_factorial
    {z : ℂ} {N : ℕ} (hsmall : ‖z‖ / N.succ ≤ 1 / 2) :
    ‖Complex.exp z - expPartialSum z N‖ ≤
      2 * (‖z‖ ^ N / N.factorial) := by
  simpa only [expPartialSum, mul_comm] using Complex.exp_bound' hsmall

/-- Translating the Taylor expansion to a base point `w` simply multiplies
the remainder by `exp w`. -/
theorem norm_exp_add_sub_exp_mul_partialSum_le (w z : ℂ) (N : ℕ) :
    ‖Complex.exp (w + z) - Complex.exp w * expPartialSum z N‖ ≤
      ‖Complex.exp w‖ * (Real.exp ‖z‖ * ‖z‖ ^ N) := by
  have hfactor :
      Complex.exp (w + z) - Complex.exp w * expPartialSum z N =
        Complex.exp w * (Complex.exp z - expPartialSum z N) := by
    rw [Complex.exp_add]
    ring
  rw [hfactor, Complex.norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_exp_sub_partialSum_le z N)
    (norm_nonneg _)

/-- A version of the translated estimate depending only on the norms of
`w` and `z`. -/
theorem norm_exp_add_sub_exp_mul_partialSum_le_exp_norm (w z : ℂ) (N : ℕ) :
    ‖Complex.exp (w + z) - Complex.exp w * expPartialSum z N‖ ≤
      Real.exp (‖w‖ + ‖z‖) * ‖z‖ ^ N := by
  calc
    ‖Complex.exp (w + z) - Complex.exp w * expPartialSum z N‖ ≤
        ‖Complex.exp w‖ * (Real.exp ‖z‖ * ‖z‖ ^ N) :=
      norm_exp_add_sub_exp_mul_partialSum_le w z N
    _ ≤ Real.exp ‖w‖ * (Real.exp ‖z‖ * ‖z‖ ^ N) := by
      gcongr
      exact Complex.norm_exp_le_exp_norm w
    _ = Real.exp (‖w‖ + ‖z‖) * ‖z‖ ^ N := by
      rw [Real.exp_add]
      ring

/-- The translated factorial estimate in the geometric-decay range. -/
theorem norm_exp_add_sub_exp_mul_partialSum_le_two_mul_div_factorial
    (w : ℂ) {z : ℂ} {N : ℕ} (hsmall : ‖z‖ / N.succ ≤ 1 / 2) :
    ‖Complex.exp (w + z) - Complex.exp w * expPartialSum z N‖ ≤
      ‖Complex.exp w‖ * (2 * (‖z‖ ^ N / N.factorial)) := by
  have hfactor :
      Complex.exp (w + z) - Complex.exp w * expPartialSum z N =
        Complex.exp w * (Complex.exp z - expPartialSum z N) := by
    rw [Complex.exp_add]
    ring
  rw [hfactor, Complex.norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_exp_sub_partialSum_le_two_mul_div_factorial hsmall) (norm_nonneg _)

end Erdos240.ComplexTaylor

#print axioms Erdos240.ComplexTaylor.norm_exp_sub_partialSum_le
#print axioms Erdos240.ComplexTaylor.norm_exp_add_sub_exp_mul_partialSum_le
#print axioms Erdos240.ComplexTaylor.norm_exp_add_sub_exp_mul_partialSum_le_exp_norm
