/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Second-derivative moments on intervals inside the unit circle.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Moments
import ErdosProblems.Erdos521.PolynomialDerivatives

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem integral_polynomial_second_derivative_sq (n : ℕ) (x : ℝ) :
    (∫ ε, ((polynomial ε n).derivative.derivative.eval x) ^ 2 ∂sequenceLaw) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2)) ^ 2 := by
  have heq (ε : ℕ → ℝ) : (polynomial ε n).derivative.derivative.eval x =
      ∑ k ∈ Finset.range (n + 1), ((k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2)) * ε k := by
    rw [polynomial_second_derivative_eval]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [heq]
  exact integral_linearForm_sq _ _

theorem derivative_weight_choose_bound (k : ℕ) :
    (((k : ℝ) + 2) * (k + 1)) ^ 2 ≤ 24 * ((k + 4).choose 4 : ℝ) := by
  have hchoose : 24 * ((k + 4).choose 4 : ℝ) =
      ((k : ℝ) + 1) * (k + 2) * (k + 3) * (k + 4) := by
    calc
      24 * ((k + 4).choose 4 : ℝ) = ((k + 1).ascFactorial 4 : ℝ) := by
        exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose k 4).symm
      _ = _ := by
        simp only [show 4 = Nat.succ 3 by rfl, show 3 = Nat.succ 2 by rfl,
          show 2 = Nat.succ 1 by rfl, show 1 = Nat.succ 0 by rfl,
          Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Nat.cast_zero]
        ring
  rw [hchoose]
  calc
    (((k : ℝ) + 2) * (k + 1)) ^ 2 =
        (((k : ℝ) + 1) * (k + 2)) * ((k + 1) * (k + 2)) := by ring
    _ ≤ (((k : ℝ) + 1) * (k + 2)) * ((k + 3) * (k + 4)) := by gcongr <;> linarith
    _ = _ := by ring

theorem sum_shifted_second_derivative_sq_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) :
    (∑ k ∈ Finset.range N, ((((k : ℝ) + 2) * (k + 1)) * x ^ k) ^ 2) ≤ 24 / (1 - x) ^ 5 := by
  have hnorm : ‖x‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hx₁
  have hsum := sum_le_hasSum (Finset.range N)
    (fun k _ ↦ mul_nonneg (Nat.cast_nonneg ((k + 4).choose 4)) (pow_nonneg hx k))
    (hasSum_choose_mul_geometric_of_norm_lt_one 4 hnorm)
  calc
    (∑ k ∈ Finset.range N, ((((k : ℝ) + 2) * (k + 1)) * x ^ k) ^ 2) ≤
        ∑ k ∈ Finset.range N, 24 * ((k + 4).choose 4 : ℝ) * x ^ k := by
      apply Finset.sum_le_sum
      intro k _
      have hp₀ : 0 ≤ x ^ k := pow_nonneg hx k
      have hp₁ : x ^ k ≤ 1 := pow_le_one₀ hx hx₁.le
      have hp : (x ^ k) ^ 2 ≤ x ^ k := by nlinarith
      rw [mul_pow]
      exact mul_le_mul (derivative_weight_choose_bound k) hp (sq_nonneg _) (by positivity)
    _ = 24 * ∑ k ∈ Finset.range N, ((k + 4).choose 4 : ℝ) * x ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 24 * (1 / (1 - x) ^ (4 + 1)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

theorem polynomial_second_derivative_moment_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) :
    (∫ ε, ((polynomial ε n).derivative.derivative.eval x) ^ 2 ∂sequenceLaw) ≤
      24 / (1 - x) ^ 5 := by
  rw [integral_polynomial_second_derivative_sq]
  rcases n with _ | n
  · norm_num
    positivity
  rcases n with _ | n
  · norm_num [Finset.sum_range_succ]
    positivity
  have heq : (∑ k ∈ Finset.range (n + 1 + 1 + 1),
      ((k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2)) ^ 2) =
      ∑ k ∈ Finset.range (n + 1), ((((k : ℝ) + 2) * (k + 1)) * x ^ k) ^ 2 := by
    have hfirst : (∑ k ∈ Finset.range 2, ((k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2)) ^ 2) = 0 := by
      norm_num [Finset.sum_range_succ]
    rw [show n + 1 + 1 + 1 = 2 + (n + 1) by omega, Finset.sum_range_add, hfirst, zero_add]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [show 2 + k - 1 = k + 1 by omega, show 2 + k - 2 = k by omega]
    push_cast
    ring
  rw [heq]
  exact sum_shifted_second_derivative_sq_le (n + 1) hx hx₁

end Erdos521
