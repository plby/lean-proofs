/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueMoments

/-! # Finite real-weight concentration for the random sieve -/

namespace Erdos4b.FGKMT

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem finite_centered_second_moment (μ X : Ω → ℝ) (b : ℝ)
    (hμ : ∑ a, μ a = 1) :
    (∑ a, μ a * (X a - b) ^ 2) = (∑ a, μ a * X a ^ 2) - 2 * b * (∑ a, μ a * X a) + b ^ 2 := by
  calc
    _ = (∑ a, μ a * X a ^ 2) - 2 * b * (∑ a, μ a * X a) + b ^ 2 * (∑ a, μ a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = _ := by rw [hμ, mul_one]

theorem finite_square_tail_le (μ X : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (b : ℝ) {r : ℝ} (hr : 0 < r) :
    (∑ a, if r ≤ |X a - b| then μ a else 0) ≤ (∑ a, μ a * (X a - b) ^ 2) / r ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _ha
  by_cases htail : r ≤ |X a - b|
  · rw [if_pos htail]
    have hs := (sq_le_sq₀ hr.le (abs_nonneg (X a - b))).mpr htail
    rw [sq_abs] at hs
    exact mul_le_mul_of_nonneg_left hs (hμ a)
  · rw [if_neg htail, zero_mul]
    exact mul_nonneg (hμ a) (sq_nonneg _)

theorem finite_approx_mean_variance_bound (μ X : Ω → ℝ) (hμ : ∑ a, μ a = 1)
    {s e d : ℝ} (hs : 0 ≤ s)
    (hmean : |(∑ a, μ a * X a) - s| ≤ e * s)
    (hsecond : (∑ a, μ a * X a ^ 2) ≤ (1 + e) * s ^ 2 + d) :
    (∑ a, μ a * (X a - s) ^ 2) ≤ 3 * e * s ^ 2 + d := by
  rw [finite_centered_second_moment μ X s hμ]
  have hlo := (abs_le.mp hmean).1
  have hscaled := mul_le_mul_of_nonneg_left hlo hs
  nlinarith

theorem finite_concentration_of_moments (μ X : Ω → ℝ)
    (hμ0 : ∀ a, 0 ≤ μ a) (hμ : ∑ a, μ a = 1)
    {s e d r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hmean : |(∑ a, μ a * X a) - s| ≤ e * s)
    (hsecond : (∑ a, μ a * X a ^ 2) ≤ (1 + e) * s ^ 2 + d) :
    (∑ a, if r * s ≤ |X a - s| then μ a else 0) ≤
      (3 * e * s ^ 2 + d) / (r * s) ^ 2 := by
  exact (finite_square_tail_le μ X hμ0 s (mul_pos hr hs)).trans
    (div_le_div_of_nonneg_right (finite_approx_mean_variance_bound μ X hμ hs.le hmean hsecond)
      (sq_nonneg _))

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.finite_centered_second_moment
#print axioms Erdos4b.FGKMT.finite_concentration_of_moments
