import ErdosProblems.Erdos633b.FewCornerAngles
import ErdosProblems.Erdos633b.VeryObtuseInventory
import ErdosProblems.Erdos633b.CornerReindex
import ErdosProblems.Erdos633b.ReptilingNecessity
import ErdosProblems.Erdos633b.SixShapeNecessity

/-! A tile with an angle greater than 120 degrees can tile a scalene
triangle only by reptiling. No commensurability premise is required. -/

namespace Erdos633b.Tiling

theorem reptiling_of_very_obtuse_missing_middle {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hlarge : 2 * Real.pi / 3 < d.tile.angle 2) (h1 : d.cornerColumnCount 1 = 0)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  have h2 := d.corner_column_one_of_very_obtuse 2 hlarge
  have h0 := d.other_column_le_three_of_very_obtuse hlarge h1
  apply d.reptiling_of_corner_total_le_four hscalene
  simp only [Fin.sum_univ_three, h1, h2]
  omega

theorem reptiling_of_very_obtuse_last {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hlarge : 2 * Real.pi / 3 < d.tile.angle 2)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  by_cases hrep : ReptilingAngles d.tile T
  · exact hrep
  obtain ⟨j, hj⟩ := d.exists_zero_corner_column_of_not_permuted hrep
  fin_cases j
  · change d.cornerColumnCount 0 = 0 at hj
    let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    have hl : 2 * Real.pi / 3 < (d.reindexTile e).tile.angle 2 := by
      change 2 * Real.pi / 3 < Triangle.angle (d.tile.reindex e) 2
      simpa [Triangle.angle_reindex, e, Equiv.swap_apply_def] using hlarge
    have h1 : (d.reindexTile e).cornerColumnCount 1 = 0 := by
      simpa only [d.cornerColumnCount_reindexTile, e, Equiv.symm_swap,
        Equiv.swap_apply_right] using hj
    have hh := (d.reindexTile e).reptiling_of_very_obtuse_missing_middle hl h1 hscalene
    exact reptilingAngles_of_reindex_tile d.tile T e hh
  · exact d.reptiling_of_very_obtuse_missing_middle hlarge hj hscalene
  · have h2 := d.corner_column_one_of_very_obtuse 2 hlarge
    change d.cornerColumnCount 2 = 0 at hj
    omega

theorem reptiling_of_very_obtuse_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hlarge : 2 * Real.pi / 3 < d.tile.angle j)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 j
  have hl : 2 * Real.pi / 3 < (d.reindexTile e).tile.angle 2 := by
    change 2 * Real.pi / 3 < Triangle.angle (d.tile.reindex e) 2
    simpa only [Triangle.angle_reindex, e, Equiv.symm_swap,
      Equiv.swap_apply_left] using hlarge
  have hh := (d.reindexTile e).reptiling_of_very_obtuse_last hl hscalene
  exact reptilingAngles_of_reindex_tile d.tile T e hh

theorem very_obtuse_tile_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (j : Fin 3) (hlarge : 2 * Real.pi / 3 < d.tile.angle j) :
    EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · exact d.reptiling_necessary hn (d.reptiling_of_very_obtuse_tile j hlarge hscalene)
  · exact eightCases_of_not_injective_angles T hscalene

theorem tile_angle_le_two_pi_thirds_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) (j : Fin 3) :
    d.tile.angle j ≤ 2 * Real.pi / 3 := by
  by_contra h
  exact hnot (d.very_obtuse_tile_necessary hn j (lt_of_not_ge h))

end Erdos633b.Tiling
