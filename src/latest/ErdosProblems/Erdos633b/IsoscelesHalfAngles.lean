import ErdosProblems.Erdos633b.CaseOne

/-! The actual median half of an isosceles triangle is right, with the
original base angle and half the original apex angle. -/

namespace Erdos633b.Triangle

theorem isosceles_legs_of_base_angles (T : Triangle) (h : T.angle 0 = T.angle 1) :
    dist (T.points 2) (T.points 0) = dist (T.points 2) (T.points 1) := by
  have hs := T.sine_law 0 1
  rw [h] at hs
  have hp := Real.sin_pos_of_pos_of_lt_pi (T.angle_pos 1) (T.angle_lt_pi 1)
  have he : T.side 1 = T.side 0 := mul_left_cancel₀ hp.ne' hs
  exact he.trans (dist_comm _ _)

theorem firstHalf_angle_one (T : Triangle) : T.firstHalf.angle 1 = T.angle 0 := by
  change EuclideanGeometry.angle (T.firstHalf.points 2) (T.firstHalf.points 1)
    (T.firstHalf.points 0) = EuclideanGeometry.angle (T.points 1) (T.points 0) (T.points 2)
  rw [T.firstHalf_points]
  change EuclideanGeometry.angle (midpoint ℝ (T.points 0) (T.points 1)) (T.points 0)
    (T.points 2) = _
  have hne : T.points 0 ≠ T.points 1 := T.independent.injective.ne (by decide)
  exact (sbtw_midpoint_of_ne ℝ hne).angle_eq_left (T.points 2)

theorem firstHalf_angle_two_of_isosceles (T : Triangle) (h : T.angle 0 = T.angle 1) :
    T.firstHalf.angle 2 = Real.pi / 2 := by
  change EuclideanGeometry.angle (T.firstHalf.points 0) (T.firstHalf.points 2)
    (T.firstHalf.points 1) = Real.pi / 2
  rw [T.firstHalf_points]
  exact EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq
    (T.isosceles_legs_of_base_angles h)

theorem firstHalf_angle_zero_of_isosceles (T : Triangle) (h : T.angle 0 = T.angle 1) :
    T.firstHalf.angle 0 = Real.pi / 2 - T.angle 0 := by
  have hs := T.firstHalf.angle_sum
  rw [T.firstHalf_angle_one, T.firstHalf_angle_two_of_isosceles h] at hs
  linarith

theorem angles_le_pi_half_of_right (T : Triangle) (h : T.angle 2 = Real.pi / 2)
    (j : Fin 3) : T.angle j ≤ Real.pi / 2 := by
  have hs := T.angle_sum
  have h0 := T.angle_pos 0
  have h1 := T.angle_pos 1
  fin_cases j
  · change T.angle 0 ≤ Real.pi / 2
    linarith
  · change T.angle 1 ≤ Real.pi / 2
    linarith
  · change T.angle 2 ≤ Real.pi / 2
    exact h.le

end Erdos633b.Triangle
