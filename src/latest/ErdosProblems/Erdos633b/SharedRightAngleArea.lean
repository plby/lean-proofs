import ErdosProblems.Erdos633b.RightMetricCommon
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Area and sine-law equations for two actual triangles sharing the right
angle at index two. -/

namespace Erdos633b.Tiling

theorem count_of_shared_angle_two {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : T.angle 2 = d.tile.angle 2) :
    (n : ℝ) = T.side 0 * T.side 1 / (d.tile.side 0 * d.tile.side 1) := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let d' := (d.reindexTile e).reindexOuter e
  have h0 : Triangle.angle (T.reindex e) 0 = d'.tile.angle 0 := by
    simpa [d', e, Tiling.reindexOuter, Tiling.reindexTile, Triangle.angle_reindex] using h2
  have he := d'.count_of_shared_angle h0
  simpa [d', e, Tiling.reindexOuter, Tiling.reindexTile, Triangle.side_reindex,
    Equiv.swap_apply_def, mul_comm] using he

theorem normalized_area_of_both_right {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hT : T.angle 2 = Real.pi / 2) :
    (n : ℝ) * Real.sin (d.tile.angle 0) * Real.cos (d.tile.angle 0) =
      (T.side 0 / d.tile.side 2) * (T.side 1 / d.tile.side 2) := by
  obtain ⟨ha, hb⟩ := d.right_normalized_tile_sides hright
  rw [← ha, ← hb, d.count_of_shared_angle_two (hT.trans hright.symm)]
  field_simp [(d.tile.side_pos 0).ne', (d.tile.side_pos 1).ne', (d.tile.side_pos 2).ne']

theorem normalized_sides_of_outer_right {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hT : T.angle 2 = Real.pi / 2) (j : Fin 3) :
    T.side j / d.tile.side 2 = (T.side 2 / d.tile.side 2) * Real.sin (T.angle j) := by
  have hs := T.sine_law j 2
  rw [hT, Real.sin_pi_div_two, one_mul] at hs
  rw [← hs]
  ring

end Erdos633b.Tiling
