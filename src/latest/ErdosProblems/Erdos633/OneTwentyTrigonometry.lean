import ErdosProblems.Erdos633.SixtyTrigonometry

/-!
# Rational normalized sides for a 120-degree tile

The half-angle tangent supplies both positive rational sides and the exact
sine and cosine formulas used by the two remaining outer angle criteria.
-/

namespace Erdos633

theorem sin_sixty_difference_ratio (θ : ℝ) :
    Real.sin (Real.pi / 3 - θ) / Real.sin (Real.pi / 3) =
      Real.cos θ - (1 / 3) * (Real.sqrt 3 * Real.sin θ) := by
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hroot0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp
  linear_combination Real.sin θ * hroot

theorem oneTwenty_rational_trigonometric_parameters (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 3) (q : ℚ)
    (hq : (q : ℝ) = Real.sqrt 3 * Real.tan (α / 2)) :
    ∃ a b : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + a * b + b ^ 2 = 1 ∧
      Real.sin α = Real.sin (Real.pi / 3) * (a : ℝ) ∧
      Real.sin (Real.pi / 3 - α) = Real.sin (Real.pi / 3) * (b : ℝ) ∧
      Real.cos α = ((a : ℝ) + 2 * b) / 2 ∧
      Real.cos (Real.pi / 3 - α) = (2 * (a : ℝ) + b) / 2 := by
  have hαπ : α < Real.pi := by linarith [Real.pi_pos]
  obtain ⟨hcos, hsin⟩ := scaled_half_tangent_formulas α q hα0 hαπ hq
  let a : ℚ := 4 * q / (3 + q ^ 2)
  let b : ℚ := (3 - q ^ 2 - 2 * q) / (3 + q ^ 2)
  have ht : 0 < Real.sin (Real.pi / 3) := by
    rw [Real.sin_pi_div_three]
    positivity
  have ht0 := ne_of_gt ht
  have hA : Real.sin α / Real.sin (Real.pi / 3) = (a : ℝ) := by
    rw [sin_over_sin_sixty, hsin]
    dsimp [a]
    push_cast
    ring
  have hB : Real.sin (Real.pi / 3 - α) / Real.sin (Real.pi / 3) = (b : ℝ) := by
    rw [sin_sixty_difference_ratio, hcos, hsin]
    dsimp [b]
    push_cast
    ring
  have haR : (0 : ℝ) < a := by
    rw [← hA]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hα0 hαπ) ht
  have hbR : (0 : ℝ) < b := by
    rw [← hB]
    apply div_pos _ ht
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hc : a ^ 2 + a * b + b ^ 2 = 1 := by
    have hd : 3 + q ^ 2 ≠ 0 := by positivity
    dsimp [a, b]
    field_simp
    ring
  have hsA : Real.sin α = Real.sin (Real.pi / 3) * (a : ℝ) := by
    simpa only [mul_comm] using (div_eq_iff ht0).mp hA
  have hsB : Real.sin (Real.pi / 3 - α) = Real.sin (Real.pi / 3) * (b : ℝ) := by
    simpa only [mul_comm] using (div_eq_iff ht0).mp hB
  have hcA : Real.cos α = ((a : ℝ) + 2 * b) / 2 := by
    rw [hcos]
    dsimp [a, b]
    push_cast
    ring
  refine ⟨a, b, by exact_mod_cast haR, by exact_mod_cast hbR, hc, hsA, hsB, hcA, ?_⟩
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, hcA, hsA,
    Real.sin_pi_div_three]
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (a : ℝ) / 4 * hroot

theorem oneTwenty_sin_three (α a b : ℝ)
    (hsin : Real.sin α = Real.sin (Real.pi / 3) * a)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1) :
    Real.sin (3 * α) = Real.sin α * (3 * b * (a + b)) := by
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsquare : 4 * Real.sin α ^ 2 = 3 * a ^ 2 := by
    rw [hsin, Real.sin_pi_div_three]
    linear_combination a ^ 2 * hroot
  rw [Real.sin_three_mul]
  linear_combination -Real.sin α * hsquare - 3 * Real.sin α * hconic

theorem oneTwenty_sin_sixty_add (α a b : ℝ)
    (hsin : Real.sin α = Real.sin (Real.pi / 3) * a)
    (hcos : Real.cos α = (a + 2 * b) / 2) :
    Real.sin (Real.pi / 3 + α) = Real.sin (Real.pi / 3) * (a + b) := by
  rw [Real.sin_add, Real.cos_pi_div_three, hsin, hcos]
  ring

end Erdos633
