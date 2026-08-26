import ErdosProblems.Erdos633.TriangleAngles

/-!
# Trigonometry of the relation `3α + 2β = π`

The parameter is `s = 2 sin(α/2)`. These identities connect the actual
Euclidean angles to the side ratios of the U and V constructions.
-/

namespace Erdos633

theorem groupOne_parameter_range (α s : ℝ) (hα0 : 0 < α) (hα1 : α < Real.pi / 3)
    (hs : s = 2 * Real.sin (α / 2)) : 0 < s ∧ s < 1 := by
  have hp := Real.pi_pos
  have hsin := Real.sin_pos_of_pos_of_lt_pi (show 0 < α / 2 by linarith)
    (show α / 2 < Real.pi by linarith)
  have hlt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ α / 2 by linarith)
    (show Real.pi / 6 ≤ Real.pi / 2 by linarith)
    (show α / 2 < Real.pi / 6 by linarith)
  rw [Real.sin_pi_div_six] at hlt
  constructor <;> linarith

theorem groupOne_cos (α s : ℝ) (hs : s = 2 * Real.sin (α / 2)) :
    2 * Real.cos α = 2 - s ^ 2 := by
  have hc := Real.cos_two_mul_eq_one_sub (α / 2)
  rw [show 2 * (α / 2) = α by ring] at hc
  rw [hs]
  nlinarith

theorem groupOne_sin_two (α s : ℝ) (hs : s = 2 * Real.sin (α / 2)) :
    Real.sin (2 * α) = Real.sin α * (2 - s ^ 2) := by
  rw [Real.sin_two_mul]
  calc
    2 * Real.sin α * Real.cos α = Real.sin α * (2 * Real.cos α) := by ring
    _ = _ := by rw [groupOne_cos α s hs]

theorem groupOne_sin_three (α s : ℝ) (hs : s = 2 * Real.sin (α / 2)) :
    Real.sin (3 * α) = Real.sin α * ((1 - s ^ 2) * (3 - s ^ 2)) := by
  have hc : Real.cos α = 1 - s ^ 2 / 2 := by linarith [groupOne_cos α s hs]
  calc
    Real.sin (3 * α) = Real.sin α * (4 * Real.cos α ^ 2 - 1) := by
      rw [Real.sin_three_mul]
      linear_combination -4 * Real.sin α * Real.sin_sq_add_cos_sq α
    _ = _ := by rw [hc]; ring

theorem groupOne_sin_sum (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    Real.sin (α + β) = Real.cos (α / 2) := by
  rw [show α + β = Real.pi / 2 - α / 2 by linarith, Real.sin_pi_div_two_sub]

theorem groupOne_sin_beta (α β s : ℝ) (h : 3 * α + 2 * β = Real.pi)
    (hs : s = 2 * Real.sin (α / 2)) :
    Real.sin β = Real.cos (α / 2) * (1 - s ^ 2) := by
  rw [show β = Real.pi / 2 - 3 * (α / 2) by linarith,
    Real.sin_pi_div_two_sub, Real.cos_three_mul, hs]
  linear_combination 4 * Real.cos (α / 2) * Real.sin_sq_add_cos_sq (α / 2)

theorem groupOne_sin_two_half (α s : ℝ) (hs : s = 2 * Real.sin (α / 2)) :
    Real.sin (2 * α) = Real.cos (α / 2) * (s * (2 - s ^ 2)) := by
  rw [groupOne_sin_two α s hs]
  have hsin : Real.sin α = s * Real.cos (α / 2) := by
    rw [hs, ← Real.sin_two_mul, show 2 * (α / 2) = α by ring]
  rw [hsin]
  ring

end Erdos633
