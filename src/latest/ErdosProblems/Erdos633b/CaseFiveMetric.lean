import ErdosProblems.Erdos633b.CaseEightMetric

/-! Exact side and area formulas for case (5), with real side ratios. -/

namespace Erdos633b
namespace Triangle

theorem groupTwo_sine_gamma_sq (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    Real.sin (S.angle 2) ^ 2 = 3 / 4 := by
  rw [hg, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_three]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem groupTwo_triple_sine_ratio (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    Real.sin (3 * S.angle 0) / Real.sin (S.angle 2) =
      3 * (S.side 0 / S.side 2) * (1 - (S.side 0 / S.side 2) ^ 2) := by
  have hc := S.groupTwo_sine_gamma_sq hg
  have hs := (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 2) (S.angle_lt_pi 2)).ne'
  rw [sin_three_mul_eq, S.side_ratio_eq_sine_ratio]
  field_simp [hs]
  linear_combination -4 * Real.sin (S.angle 0) ^ 3 * hc

theorem caseFive_normalized_sides (S T : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = 2 * S.angle 0)
    (h2 : T.angle 2 = 3 * S.angle 1) :
    T.side 1 / S.side 2 = (T.side 0 / S.side 2) *
        (S.side 0 / S.side 2 + 2 * (S.side 1 / S.side 2)) ∧
      T.side 2 / S.side 2 = 3 * (T.side 0 / S.side 2) * (1 - (S.side 0 / S.side 2) ^ 2) := by
  have hX := S.common_angle_side_zero_scale T
  constructor
  · rw [S.normalized_sides_from_common_angle T h0 1, h1, Real.sin_two_mul]
    calc
      _ = ((T.side 0 / S.side 0) * (S.side 0 / S.side 2)) *
          (S.side 0 / S.side 2 + 2 * (S.side 1 / S.side 2)) := by
        rw [← (S.groupTwo_cosine_coordinates hg).1, S.side_ratio_eq_sine_ratio 0 2]
        ring
      _ = _ := by rw [← hX]
  · have ht2 : T.angle 2 = Real.pi - 3 * S.angle 0 := by linarith [S.angle_sum]
    rw [S.normalized_sides_from_common_angle T h0 2, ht2, Real.sin_pi_sub,
      S.groupTwo_triple_sine_ratio hg, hX]
    ring

end Triangle
namespace Tiling

theorem caseFive_area_scale {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    (n : ℝ) = 3 * (T.side 0 / d.tile.side 2) ^ 2 *
      (d.tile.side 0 / d.tile.side 2 + 2 * (d.tile.side 1 / d.tile.side 2)) *
      (d.tile.side 0 / d.tile.side 2 + d.tile.side 1 / d.tile.side 2) := by
  obtain ⟨hY, hZ⟩ := d.tile.caseFive_normalized_sides T hg h0 h1 h2
  rw [d.normalized_count_of_shared_angle h0, hY, hZ]
  let x := d.tile.side 0 / d.tile.side 2
  let y := d.tile.side 1 / d.tile.side 2
  let k := T.side 0 / d.tile.side 2
  have hy : y ≠ 0 := div_ne_zero (d.tile.side_pos 1).ne' (d.tile.side_pos 2).ne'
  have hc : x ^ 2 + x * y + y ^ 2 = 1 := d.tile.groupTwo_normalized_conic hg
  change (k * (x + 2 * y) * (3 * k * (1 - x ^ 2))) / y =
    3 * k ^ 2 * (x + 2 * y) * (x + y)
  apply (div_eq_iff hy).mpr
  linear_combination -(3 * k ^ 2 * (x + 2 * y)) * hc

end Tiling
end Erdos633b
