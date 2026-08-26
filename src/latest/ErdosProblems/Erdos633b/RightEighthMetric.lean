import ErdosProblems.Erdos633b.RightMetricCommon
import ErdosProblems.Erdos633b.RightEighthAlgebra

/-! The actual scalene outer shape (pi/8, pi/4, 5pi/8) cannot be tiled by
a reference triangle with angles (pi/8, 3pi/8, pi/2). -/

namespace Erdos633b.Tiling

theorem right_eighth_ordered_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 8)
    (h0 : T.angle 0 = Real.pi / 8) (h1 : T.angle 1 = Real.pi / 4)
    (h2 : T.angle 2 = 5 * Real.pi / 8) : False := by
  have hcommon : T.angle 0 = d.tile.angle 0 := h0.trans hα.symm
  let L := T.side 0 / d.tile.side 0
  let Y := T.side 1 / d.tile.side 2
  let b := Real.cos (Real.pi / 8)
  have hb : 0 < b := by
    dsimp only [b]
    rw [← hα, ← (d.right_normalized_tile_sides hright).2]
    exact div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  have hY : Y = L * (Real.sqrt 2 / 2) := by
    dsimp only [Y, L]
    rw [d.right_shared_angle_normalized_sides hright hcommon, h1, Real.sin_pi_div_four]
  have hZ : T.side 2 / d.tile.side 2 = L * b := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h2,
      show 5 * Real.pi / 8 = Real.pi / 2 + Real.pi / 8 by ring, Real.sin_add,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp only [one_mul, zero_mul, add_zero, L, b]
  have harea : (n : ℝ) * b = Y * (L * b) := by
    simpa only [hα, hZ, b, Y] using d.right_shared_angle_area hright hcommon
  have hn : (n : ℝ) = Y * L := by
    apply mul_right_cancel₀ hb.ne'
    simpa only [mul_assoc] using harea
  have he : Y ^ 2 = (n : ℝ) / 2 * Real.sqrt 2 := by
    rw [hn, hY]
    ring
  have hboundary := d.right_normalized_boundary hright 1
  rw [hα] at hboundary
  apply eighth_boundary_square_impossible n d.positive (d.boundarySideCount 1)
  rw [← hboundary]
  exact he

end Erdos633b.Tiling
