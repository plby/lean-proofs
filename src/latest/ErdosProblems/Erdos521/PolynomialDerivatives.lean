/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Deterministic derivative bounds used to pass from small balls to root repulsion.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Model
import Mathlib

namespace Erdos521

open scoped BigOperators

theorem polynomial_derivative_eval (ε : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (polynomial ε n).derivative.eval x =
      ∑ k ∈ Finset.range (n + 1), ε k * (k : ℝ) * x ^ (k - 1) := by
  simp only [polynomial, Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem polynomial_second_derivative_eval (ε : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (polynomial ε n).derivative.derivative.eval x =
      ∑ k ∈ Finset.range (n + 1), ε k * (k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2) := by
  simp only [polynomial, Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Nat.sub_sub, show (1 : ℕ) + 1 = 2 by rfl]

theorem polynomial_second_derivative_abs_le (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1)
    (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(polynomial ε n).derivative.derivative.eval x| ≤ (n + 1 : ℝ) ^ 3 := by
  rw [polynomial_second_derivative_eval]
  calc
    |∑ k ∈ Finset.range (n + 1), ε k * (k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2)| ≤
        ∑ k ∈ Finset.range (n + 1), |ε k * (k : ℝ) * (k - 1 : ℕ) * x ^ (k - 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range (n + 1), (n + 1 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkNat : k ≤ n + 1 := (Finset.mem_range.mp hk).le
      have hk' : (k : ℝ) ≤ n + 1 := by exact_mod_cast hkNat
      have hk'' : ((k - 1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.sub_le k 1).trans hkNat
      have hp : |x| ^ (k - 2) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
      simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k - 1))]
      calc
        |ε k| * (k : ℝ) * (k - 1 : ℕ) * |x| ^ (k - 2) ≤
            1 * (n + 1 : ℝ) * (n + 1) * 1 := by gcongr; exact hε k
        _ = _ := by ring
    _ = _ := by simp; ring

theorem polynomial_derivative_lipschitz (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1)
    (n : ℕ) {x y : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |(polynomial ε n).derivative.eval y - (polynomial ε n).derivative.eval x| ≤
      (n + 1 : ℝ) ^ 3 * |y - x| := by
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := (n + 1 : ℝ) ^ 3)
    (fun z _ ↦ ((polynomial ε n).derivative.hasDerivAt z).hasDerivWithinAt)
    (fun z hz ↦ ?_) hx hy
  · simpa only [Real.norm_eq_abs] using h
  · simpa only [Real.norm_eq_abs] using polynomial_second_derivative_abs_le ε hε n (abs_le.mpr hz)

/-- If the polynomial and its derivative are small at one point, then the
polynomial is small at nearby grid points. -/
theorem polynomial_value_le_of_small_value_derivative (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1)
    (n : ℕ) {x y η ρ : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hxy : |y - x| ≤ ρ)
    (hvalue : |(polynomial ε n).eval x| ≤ η)
    (hderiv : |(polynomial ε n).derivative.eval x| ≤ η) :
    |(polynomial ε n).eval y| ≤ η + ρ * (η + (n + 1 : ℝ) ^ 3 * ρ) := by
  let s := Set.Icc (-1 : ℝ) 1 ∩ Metric.closedBall x ρ
  have hs : Convex ℝ s := (convex_Icc _ _).inter (convex_closedBall x ρ)
  have hxs : x ∈ s := ⟨hx, by simpa only [Metric.mem_closedBall, dist_self] using hρ⟩
  have hys : y ∈ s := ⟨hy, by simpa only [Metric.mem_closedBall, Real.dist_eq] using hxy⟩
  have hbound (t : ℝ) (ht : t ∈ s) :
      ‖(polynomial ε n).derivative.eval t‖ ≤ η + (n + 1 : ℝ) ^ 3 * ρ := by
    have htx : |t - x| ≤ ρ := by simpa only [Metric.mem_closedBall, Real.dist_eq] using ht.2
    have hlip := polynomial_derivative_lipschitz ε hε n hx ht.1
    have hmul := mul_le_mul_of_nonneg_left htx (by positivity : 0 ≤ (n + 1 : ℝ) ^ 3)
    have htri := norm_add_le
      ((polynomial ε n).derivative.eval t - (polynomial ε n).derivative.eval x)
      ((polynomial ε n).derivative.eval x)
    rw [sub_add_cancel] at htri
    simp only [Real.norm_eq_abs] at htri ⊢
    linarith
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ ((polynomial ε n).hasDerivAt t).hasDerivWithinAt) hbound hxs hys
  simp only [Real.norm_eq_abs] at h
  have hmul := mul_le_mul_of_nonneg_left hxy
    (by positivity : 0 ≤ η + (n + 1 : ℝ) ^ 3 * ρ)
  have htri := norm_add_le ((polynomial ε n).eval y - (polynomial ε n).eval x)
    ((polynomial ε n).eval x)
  rw [sub_add_cancel] at htri
  simp only [Real.norm_eq_abs] at htri
  nlinarith

end Erdos521
