import ErdosProblems.Erdos633b.SharedAngleArea
import ErdosProblems.Erdos633b.SharedAngleMetric
import ErdosProblems.Erdos633b.ReptilingRightTrace

/-! Normalized boundary and sine-law equations for actual tilings by a right
triangle. The boundary coefficients count geometric boundary edges. -/

namespace Erdos633b.Tiling

theorem right_normalized_tile_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) :
    d.tile.side 0 / d.tile.side 2 = Real.sin (d.tile.angle 0) ∧
      d.tile.side 1 / d.tile.side 2 = Real.cos (d.tile.angle 0) := by
  obtain ⟨hs, hc⟩ := d.tile.right_sine_cosine_sides hright
  exact ⟨(div_eq_iff (d.tile.side_pos 2).ne').mpr hs.symm,
    (div_eq_iff (d.tile.side_pos 2).ne').mpr hc.symm⟩

theorem right_normalized_boundary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (i : Fin 3) :
    T.side i / d.tile.side 2 =
      (d.boundarySideCount i 0 : ℝ) * Real.sin (d.tile.angle 0) +
      d.boundarySideCount i 1 * Real.cos (d.tile.angle 0) + d.boundarySideCount i 2 := by
  obtain ⟨hs, hc⟩ := d.right_normalized_tile_sides hright
  rw [d.side_eq_three_counts i]
  rw [add_div, add_div, mul_div_assoc, mul_div_assoc, mul_div_assoc, hs, hc,
    div_self (d.tile.side_pos 2).ne', mul_one]

theorem right_shared_angle_normalized_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (h0 : T.angle 0 = d.tile.angle 0)
    (j : Fin 3) : T.side j / d.tile.side 2 =
      (T.side 0 / d.tile.side 0) * Real.sin (T.angle j) := by
  rw [d.tile.normalized_sides_from_common_angle T h0 j, hright,
    Real.sin_pi_div_two, div_one]

theorem right_shared_angle_area {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (h0 : T.angle 0 = d.tile.angle 0) :
    (n : ℝ) * Real.cos (d.tile.angle 0) =
      (T.side 1 / d.tile.side 2) * (T.side 2 / d.tile.side 2) := by
  have hc := (d.right_normalized_tile_sides hright).2
  have he := d.normalized_count_of_shared_angle h0
  rw [hc] at he
  have hp : 0 < Real.cos (d.tile.angle 0) := by
    rw [← hc]
    exact div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  exact (eq_div_iff hp.ne').mp he

end Erdos633b.Tiling
