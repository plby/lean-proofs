/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Frequency and terminal-variance estimates for the local root-count tail.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalTailParameters

namespace Erdos521

theorem variance_ge_one (x : ℝ) (n : ℕ) : 1 ≤ geometricVariance x (n + 1) := by
  simpa [geometricVariance] using geometricVariance_mono x (show 1 ≤ n + 1 by omega)

theorem local_tail_variance_condition (n j : ℕ) (hj : 1 ≤ j) {x : ℝ} (hx : 0 ≤ x)
    (hx₁ : x ≤ 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    x ^ (2 * (n + 1)) ≤ 1 / 2 := by
  calc
    x ^ (2 * (n + 1)) ≤ x ^ (n / 2) := pow_le_pow_of_le_one hx hx₁ (by omega)
    _ ≤ (1 / 2 : ℝ) ^ (3 * j) := half_degree_power_le n j hj hx hx₁ hgap
    _ ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 2 := pow_one _

theorem local_tail_frequency_lower (n j : ℕ) (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x)
    (hx₁ : x ≤ 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    (j : ℝ) ≤ ((1 / 2 : ℝ) ^ j * Real.sqrt (geometricVariance x (n + 1))) *
      (x ^ (n / 2))⁻¹ := by
  have hinv : (2 : ℝ) ^ (3 * j) ≤ (x ^ (n / 2))⁻¹ := by
    have h := (inv_le_inv₀ (by positivity : 0 < (1 / 2 : ℝ) ^ (3 * j))
      (pow_pos hx _)).mpr (half_degree_power_le n j hj hx.le hx₁ hgap)
    simpa only [one_div, inv_pow, inv_inv] using h
  have hsqrt : 1 ≤ Real.sqrt (geometricVariance x (n + 1)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (variance_ge_one x n)
  have hjpow : (j : ℝ) ≤ (2 : ℝ) ^ (2 * j) := by
    have h₁ : (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast (Nat.lt_two_pow_self (n := j)).le
    exact h₁.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  calc
    (j : ℝ) ≤ (2 : ℝ) ^ (2 * j) := hjpow
    _ = (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ (3 * j) := by
      rw [show 3 * j = j + 2 * j by omega, pow_add]
      simp only [one_div, inv_pow]
      field_simp
    _ ≤ ((1 / 2 : ℝ) ^ j * Real.sqrt (geometricVariance x (n + 1))) *
        (x ^ (n / 2))⁻¹ := by
      apply mul_le_mul _ hinv (by positivity) (by positivity)
      exact le_mul_of_one_le_right (by positivity) hsqrt

theorem local_tail_frequency_error (n j : ℕ) (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x)
    (hx₁ : x ≤ 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    Real.exp (-(((1 / 2 : ℝ) ^ j * Real.sqrt (geometricVariance x (n + 1))) *
      (x ^ (n / 2))⁻¹) ^ 2 / 2) ≤ Real.exp (-(j : ℝ) / 2) := by
  have h := local_tail_frequency_lower n j hj hx hx₁ hgap
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((((1 / 2 : ℝ) ^ j * Real.sqrt (geometricVariance x (n + 1))) *
    (x ^ (n / 2))⁻¹) - j)]

end Erdos521
