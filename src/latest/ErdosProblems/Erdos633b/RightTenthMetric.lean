import ErdosProblems.Erdos633b.SharedRightAngleArea
import ErdosProblems.Erdos633b.RightTenthSignObstructions
import ErdosProblems.Erdos633b.RightTenthDoubleObstruction

/-! All three non-reptiling scalene shapes allowed by pi/10 corner weights
are excluded using actual boundary counts and the area of the dissection. -/

namespace Erdos633b.Tiling

theorem right_tenth_boundary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 10)
    (i : Fin 3) : T.side i / d.tile.side 2 =
      RightTenth.original.boundary (d.boundarySideCount i) := by
  simpa only [hα, RightTenth.Pair.boundary, RightTenth.original] using
    d.right_normalized_boundary hright i

theorem right_tenth_third_sixth_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 10)
    (h0 : T.angle 0 = Real.pi / 10) (h1 : T.angle 1 = 3 * (Real.pi / 10))
    (h2 : T.angle 2 = 6 * (Real.pi / 10)) : False := by
  have hcommon : T.angle 0 = d.tile.angle 0 := h0.trans hα.symm
  let a := Real.sin (Real.pi / 10)
  let b := Real.cos (Real.pi / 10)
  let L := T.side 0 / d.tile.side 0
  have hX : T.side 0 / d.tile.side 2 = L * a := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h0]
  have hY : T.side 1 / d.tile.side 2 = L * (a + 1 / 2) := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h1, tenth_sine_triple]
  have hZ : T.side 2 / d.tile.side 2 = L * b := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h2, tenth_sine_six]
  have hN : (n : ℝ) = L ^ 2 * (a + 1 / 2) := by
    apply mul_right_cancel₀ tenth_cosine_pos.ne'
    calc
      _ = (T.side 1 / d.tile.side 2) * (T.side 2 / d.tile.side 2) := by
        simpa only [hα] using d.right_shared_angle_area hright hcommon
      _ = _ := by rw [hY, hZ]; dsimp only [b]; ring
  apply RightTenth.original.third_sixth_impossible tenth_sine_pos tenth_sine_lt_half
    n d.positive (d.boundarySideCount 0)
  change (n : ℝ) * a ^ 2 =
    (RightTenth.original.boundary (d.boundarySideCount 0)) ^ 2 * (a + 1 / 2)
  rw [← d.right_tenth_boundary hright hα, hX, hN]
  ring

theorem right_tenth_double_seventh_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 10)
    (h0 : T.angle 0 = Real.pi / 10) (h1 : T.angle 1 = 2 * (Real.pi / 10))
    (h2 : T.angle 2 = 7 * (Real.pi / 10)) : False := by
  have hcommon : T.angle 0 = d.tile.angle 0 := h0.trans hα.symm
  let a := Real.sin (Real.pi / 10)
  let b := Real.cos (Real.pi / 10)
  let L := T.side 0 / d.tile.side 0
  have hX : T.side 0 / d.tile.side 2 = L * a := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h0]
  have hY : T.side 1 / d.tile.side 2 = L * (2 * a * b) := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h1, Real.sin_two_mul]
  have hZ : T.side 2 / d.tile.side 2 = L * (a + 1 / 2) := by
    rw [d.right_shared_angle_normalized_sides hright hcommon, h2, tenth_sine_seven]
  have hN : (n : ℝ) = L ^ 2 / 2 := by
    apply mul_right_cancel₀ tenth_cosine_pos.ne'
    calc
      _ = (T.side 1 / d.tile.side 2) * (T.side 2 / d.tile.side 2) := by
        simpa only [hα] using d.right_shared_angle_area hright hcommon
      _ = _ := by
        rw [hY, hZ]
        dsimp only [a, b]
        linear_combination L ^ 2 * Real.cos (Real.pi / 10) / 2 * tenth_sine_quadratic
  apply RightTenth.original.double_seventh_impossible tenth_sine_pos tenth_sine_lt_half
    tenth_cosine_pos n d.positive (d.boundarySideCount 0) (d.boundarySideCount 1)
  · change (RightTenth.original.boundary (d.boundarySideCount 0)) ^ 2 = 2 * n * a ^ 2
    rw [← d.right_tenth_boundary hright hα, hX, hN]
    ring
  · change RightTenth.original.boundary (d.boundarySideCount 1) =
      2 * b * RightTenth.original.boundary (d.boundarySideCount 0)
    rw [← d.right_tenth_boundary hright hα, ← d.right_tenth_boundary hright hα, hY, hX]
    ring

theorem right_tenth_second_third_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 10)
    (h0 : T.angle 0 = 2 * (Real.pi / 10)) (h1 : T.angle 1 = 3 * (Real.pi / 10))
    (h2 : T.angle 2 = Real.pi / 2) : False := by
  let a := Real.sin (Real.pi / 10)
  let b := Real.cos (Real.pi / 10)
  let Z := T.side 2 / d.tile.side 2
  have hX : T.side 0 / d.tile.side 2 = Z * (2 * a * b) := by
    rw [d.normalized_sides_of_outer_right h2, h0, Real.sin_two_mul]
  have hY : T.side 1 / d.tile.side 2 = Z * (a + 1 / 2) := by
    rw [d.normalized_sides_of_outer_right h2, h1, tenth_sine_triple]
  have hN : (n : ℝ) = 2 * Z ^ 2 * (a + 1 / 2) := by
    apply mul_right_cancel₀ (mul_pos tenth_sine_pos tenth_cosine_pos).ne'
    calc
      _ = (T.side 0 / d.tile.side 2) * (T.side 1 / d.tile.side 2) := by
        simpa only [hα, mul_assoc] using d.normalized_area_of_both_right hright h2
      _ = _ := by rw [hX, hY]; dsimp only [a, b]; ring
  apply RightTenth.original.second_third_impossible tenth_sine_pos tenth_sine_lt_half
    n d.positive (d.boundarySideCount 2)
  change (n : ℝ) = 2 * (RightTenth.original.boundary (d.boundarySideCount 2)) ^ 2 * (a + 1 / 2)
  rw [← d.right_tenth_boundary hright hα]
  exact hN

end Erdos633b.Tiling
