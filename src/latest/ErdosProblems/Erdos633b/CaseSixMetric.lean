import ErdosProblems.Erdos633b.SharedAngleMetric
import ErdosProblems.Erdos633b.SharedAngleArea
import ErdosProblems.Erdos633b.CaseSevenMetric

/-! Exact real-parameter side and area formulas for case (6). -/

namespace Erdos633b
namespace Triangle

theorem groupOne_cosine_parameter (S : Triangle) :
    2 * Real.cos (S.angle 0) = 2 - (2 * Real.sin (S.angle 0 / 2)) ^ 2 := by
  have h : Real.cos (S.angle 0) = 2 * Real.cos (S.angle 0 / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (S.angle 0 / 2) using 1
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq (S.angle 0 / 2)]

theorem groupOne_sine_gamma_sq (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi) :
    Real.sin (S.angle 2) ^ 2 = 1 - (2 * Real.sin (S.angle 0 / 2)) ^ 2 / 4 := by
  have hg : S.angle 2 = Real.pi / 2 + S.angle 0 / 2 := by linarith [S.angle_sum]
  rw [hg, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  nlinarith [Real.sin_sq_add_cos_sq (S.angle 0 / 2)]

theorem groupOne_triple_sine_ratio (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi) :
    Real.sin (3 * S.angle 0) / Real.sin (S.angle 2) =
      (2 * Real.sin (S.angle 0 / 2)) * (1 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) *
        (3 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) := by
  let s := 2 * Real.sin (S.angle 0 / 2)
  have hs := (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 2) (S.angle_lt_pi 2)).ne'
  have ha : Real.sin (S.angle 0) = s * Real.sin (S.angle 2) := by
    apply (div_eq_iff hs).mp
    rw [← S.side_ratio_eq_sine_ratio]
    exact (S.groupOne_side_ratios hrel).1
  change _ = s * (1 - s ^ 2) * (3 - s ^ 2)
  calc
    _ = 3 * s - 4 * s ^ 3 * Real.sin (S.angle 2) ^ 2 := by
      rw [sin_three_mul_eq, ha]
      field_simp [hs]
    _ = _ := by rw [S.groupOne_sine_gamma_sq hrel]; dsimp only [s]; ring

theorem caseSix_normalized_sides (S T : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = 2 * S.angle 0)
    (h2 : T.angle 2 = 2 * S.angle 1) :
    T.side 1 / S.side 2 = (T.side 0 / S.side 2) * (2 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) ∧
      T.side 2 / S.side 2 = (T.side 0 / S.side 2) *
        (1 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) * (3 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) := by
  have hX := S.common_angle_side_zero_scale T
  have ha := (S.groupOne_side_ratios hrel).1
  constructor
  · rw [S.normalized_sides_from_common_angle T h0 1, h1, Real.sin_two_mul, hX,
      ← S.groupOne_cosine_parameter, S.side_ratio_eq_sine_ratio 0 2]
    ring
  · have ht2 : T.angle 2 = Real.pi - 3 * S.angle 0 := by linarith
    rw [S.normalized_sides_from_common_angle T h0 2, ht2, Real.sin_pi_sub,
      S.groupOne_triple_sine_ratio hrel, hX, ha]
    ring

end Triangle
namespace Tiling

theorem caseSix_area_scale {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    (n : ℝ) = (T.side 0 / d.tile.side 2) ^ 2 *
      (2 - (2 * Real.sin (d.tile.angle 0 / 2)) ^ 2) *
      (3 - (2 * Real.sin (d.tile.angle 0 / 2)) ^ 2) := by
  obtain ⟨hY, hZ⟩ := d.tile.caseSix_normalized_sides T hrel h0 h1 h2
  have hb := (d.tile.groupOne_side_ratios hrel).2
  rw [d.normalized_count_of_shared_angle h0, hY, hZ, hb]
  have hp : 0 < 1 - (2 * Real.sin (d.tile.angle 0 / 2)) ^ 2 := by
    rw [← hb]
    exact div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  apply (div_eq_iff hp.ne').mpr
  ring

end Tiling
end Erdos633b
