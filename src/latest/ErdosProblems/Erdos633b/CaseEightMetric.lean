import ErdosProblems.Erdos633b.GroupTwoDoubleMetric
import ErdosProblems.Erdos633b.SharedAngleMetric
import ErdosProblems.Erdos633b.SharedAngleArea

/-! Exact side and area formulas for case (8), before rationality is known. -/

namespace Erdos633b
namespace Triangle

theorem groupTwo_sine_add_sixty (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    Real.sin (Real.pi / 3 + S.angle 0) / Real.sin (S.angle 2) =
      S.side 0 / S.side 2 + S.side 1 / S.side 2 := by
  have hsin3 : Real.sin (Real.pi / 3) = Real.sin (S.angle 2) := by
    rw [hg, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
  rw [Real.sin_add, Real.cos_pi_div_three, hsin3]
  calc
    _ = (2 * Real.cos (S.angle 0) + S.side 0 / S.side 2) / 2 := by
      rw [S.side_ratio_eq_sine_ratio]
      have hs := (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 2) (S.angle_lt_pi 2)).ne'
      field_simp [hs]
    _ = _ := by rw [(S.groupTwo_cosine_coordinates hg).1]; ring

theorem caseEight_normalized_sides (S T : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = 2 * S.angle 1)
    (h2 : T.angle 2 = 2 * S.angle 0 + S.angle 1) :
    T.side 0 / S.side 2 = (T.side 0 / S.side 0) * (S.side 0 / S.side 2) ∧
      T.side 1 / S.side 2 = (T.side 0 / S.side 0) * ((S.side 1 / S.side 2) *
        (2 * (S.side 0 / S.side 2) + S.side 1 / S.side 2)) ∧
      T.side 2 / S.side 2 = (T.side 0 / S.side 0) *
        (S.side 0 / S.side 2 + S.side 1 / S.side 2) := by
  refine ⟨S.common_angle_side_zero_scale T, ?_, ?_⟩
  · rw [S.normalized_sides_from_common_angle T h0 1, h1, Real.sin_two_mul,
      ← (S.groupTwo_cosine_coordinates hg).2, S.side_ratio_eq_sine_ratio 1 2]
    ring
  · have ht2 : T.angle 2 = Real.pi / 3 + S.angle 0 := by linarith [S.angle_sum]
    rw [S.normalized_sides_from_common_angle T h0 2, ht2, S.groupTwo_sine_add_sixty hg]

end Triangle
namespace Tiling

theorem caseEight_area_scale {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    (n : ℝ) = (T.side 0 / d.tile.side 0) ^ 2 *
      (2 * (d.tile.side 0 / d.tile.side 2) + d.tile.side 1 / d.tile.side 2) *
      (d.tile.side 0 / d.tile.side 2 + d.tile.side 1 / d.tile.side 2) := by
  obtain ⟨_, hY, hZ⟩ := d.tile.caseEight_normalized_sides T hg h0 h1 h2
  rw [d.normalized_count_of_shared_angle h0, hY, hZ]
  field_simp [(d.tile.side_pos 0).ne', (d.tile.side_pos 1).ne', (d.tile.side_pos 2).ne']

end Tiling
end Erdos633b
