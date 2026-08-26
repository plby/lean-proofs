import ErdosProblems.Erdos633b.RationalSides

/-! Sine-law scaling at one common angle, and the triple-angle identity
used for the remaining non-reptiling shapes. -/

namespace Erdos633b

theorem sin_three_mul_eq (a : ℝ) : Real.sin (3 * a) = 3 * Real.sin a - 4 * Real.sin a ^ 3 := by
  rw [show 3 * a = 2 * a + a by ring, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination 4 * Real.sin a * Real.sin_sq_add_cos_sq a

namespace Triangle

theorem normalized_sides_from_common_angle (S T : Triangle) (h0 : T.angle 0 = S.angle 0)
    (j : Fin 3) : T.side j / S.side 2 =
      (T.side 0 / S.side 0) * (Real.sin (T.angle j) / Real.sin (S.angle 2)) := by
  have hs0 : Real.sin (S.angle 0) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 0) (S.angle_lt_pi 0)).ne'
  calc
    _ = (T.side 0 / S.side 0) * (S.side 0 / S.side 2) * (T.side j / T.side 0) := by
      field_simp [(S.side_pos 0).ne', (S.side_pos 2).ne', (T.side_pos 0).ne']
    _ = (T.side 0 / S.side 0) * (Real.sin (S.angle 0) / Real.sin (S.angle 2)) *
        (Real.sin (T.angle j) / Real.sin (S.angle 0)) := by
      rw [S.side_ratio_eq_sine_ratio, T.side_ratio_eq_sine_ratio, h0]
    _ = _ := by field_simp [hs0]

theorem common_angle_side_zero_scale (S T : Triangle) :
    T.side 0 / S.side 2 = (T.side 0 / S.side 0) * (S.side 0 / S.side 2) := by
  field_simp [(S.side_pos 0).ne', (S.side_pos 2).ne']

end Triangle
end Erdos633b
