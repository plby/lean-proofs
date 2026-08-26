import ErdosProblems.Erdos633b.GroupTwoDoubleMetric

/-! Exact side ratios for the group-2 shape with an outer sixty-degree
angle and an undoubled alpha angle. -/

namespace Erdos633b.Triangle

theorem groupTwoSixty_side_ratios (S T : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = S.angle 0 + S.angle 1)
    (h2 : T.angle 2 = S.angle 0 + 2 * S.angle 1) :
    T.side 0 / T.side 1 = S.side 0 / S.side 2 ∧
      T.side 2 / T.side 1 = S.side 0 / S.side 2 + S.side 1 / S.side 2 := by
  have hsum : S.angle 0 + S.angle 1 = Real.pi / 3 := by linarith [S.angle_sum]
  have hsin3 : Real.sin (Real.pi / 3) = Real.sin (S.angle 2) := by
    rw [hg, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
  have hsin : Real.sin (T.angle 1) = Real.sin (S.angle 2) := by rw [h1, hsum, hsin3]
  have ht2 : T.angle 2 = Real.pi / 3 + S.angle 1 := by rw [h2]; linarith
  constructor
  · rw [T.side_ratio_eq_sine_ratio, S.side_ratio_eq_sine_ratio, h0, hsin]
  · rw [T.side_ratio_eq_sine_ratio, ht2, Real.sin_add, Real.cos_pi_div_three, hsin3, hsin]
    calc
      _ = (2 * Real.cos (S.angle 1) + S.side 1 / S.side 2) / 2 := by
        rw [S.side_ratio_eq_sine_ratio]
        have hs := (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 2) (S.angle_lt_pi 2)).ne'
        field_simp [hs]
      _ = _ := by rw [(S.groupTwo_cosine_coordinates hg).2]; ring

theorem groupTwoSixty_normalized_sides (S T : Triangle)
    (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = S.angle 0 + S.angle 1)
    (h2 : T.angle 2 = S.angle 0 + 2 * S.angle 1) :
    T.side 0 / S.side 2 = (T.side 1 / S.side 2) * (S.side 0 / S.side 2) ∧
      T.side 2 / S.side 2 = (T.side 1 / S.side 2) *
        (S.side 0 / S.side 2 + S.side 1 / S.side 2) := by
  obtain ⟨hX, hZ⟩ := S.groupTwoSixty_side_ratios T hg h0 h1 h2
  constructor
  · rw [← hX]
    field_simp [(T.side_pos 1).ne', (S.side_pos 2).ne']
  · rw [← hZ]
    field_simp [(T.side_pos 1).ne', (S.side_pos 2).ne']

end Erdos633b.Triangle
