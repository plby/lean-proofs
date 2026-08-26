import ErdosProblems.Erdos633b.RightSmallExclusions
import ErdosProblems.Erdos633b.RightEighthRigidity
import ErdosProblems.Erdos633b.RightTenthRigidity
import ErdosProblems.Erdos633b.ReptilingNecessity
import ErdosProblems.Erdos633b.SixShapeNecessity

/-! Full rigidity and eight-case necessity for every ordering of a right
reference tile. No rational-angle hypothesis or special tile-count premise
is used for the rigidity theorem. -/

namespace Erdos633b.Tiling

theorem right_isosceles_scalene_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (heq : d.tile.angle 0 = d.tile.angle 1)
    (hscalene : Function.Injective T.angle) : False := by
  have hα : d.tile.angle 0 = Real.pi / 4 := by linarith [d.tile.angle_sum]
  have hβ : d.tile.angle 1 = Real.pi / 4 := heq.symm.trans hα
  obtain ⟨c, hrow, hp, hs⟩ := d.integer_corner_weights 4 (by norm_num) ![1, 1, 2] (by
    intro j
    fin_cases j <;> norm_num
    · change d.tile.angle 0 = Real.pi / 4
      exact hα
    · change d.tile.angle 1 = Real.pi / 4
      exact hβ
    · change d.tile.angle 2 = (2 : ℝ) * (Real.pi / 4)
      linarith [hright])
  have hinj : Function.Injective c := by
    intro i j hij
    apply hscalene
    rw [hrow i, hrow j, hij]
  have hb := three_distinct_positive_sum_ge_six c hp hinj
  omega

theorem reptiling_of_ordered_right_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hαβ : d.tile.angle 0 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  by_contra hrep
  rcases d.right_angle_two_candidates hright hαβ hscalene hrep with h8 | h10
  · exact hrep (d.right_eighth_reptiling hright h8 hscalene)
  · exact hrep (d.right_tenth_reptiling hright h10 hscalene)

theorem reptiling_of_right_tile_last {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  rcases lt_trichotomy (d.tile.angle 0) (d.tile.angle 1) with hlt | heq | hgt
  · exact d.reptiling_of_ordered_right_tile hright hlt hscalene
  · exact False.elim (d.right_isosceles_scalene_impossible hright heq hscalene)
  · let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    have hr : (d.reindexTile e).tile.angle 2 = Real.pi / 2 := by
      change Triangle.angle (d.tile.reindex e) 2 = Real.pi / 2
      simpa [Triangle.angle_reindex, e, Equiv.swap_apply_def] using hright
    have h01 : (d.reindexTile e).tile.angle 0 < (d.reindexTile e).tile.angle 1 := by
      change Triangle.angle (d.tile.reindex e) 0 < Triangle.angle (d.tile.reindex e) 1
      simpa [Triangle.angle_reindex, e] using hgt
    exact reptilingAngles_of_reindex_tile d.tile T e
      ((d.reindexTile e).reptiling_of_ordered_right_tile hr h01 hscalene)

theorem reptiling_of_right_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hright : d.tile.angle j = Real.pi / 2)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 j
  have hr : (d.reindexTile e).tile.angle 2 = Real.pi / 2 := by
    change Triangle.angle (d.tile.reindex e) 2 = Real.pi / 2
    simpa only [Triangle.angle_reindex, e, Equiv.symm_swap, Equiv.swap_apply_left] using hright
  exact reptilingAngles_of_reindex_tile d.tile T e
    ((d.reindexTile e).reptiling_of_right_tile_last hr hscalene)

theorem right_tile_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (j : Fin 3) (hright : d.tile.angle j = Real.pi / 2) :
    EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · exact d.reptiling_necessary hn (d.reptiling_of_right_tile j hright hscalene)
  · exact eightCases_of_not_injective_angles T hscalene

theorem tile_angle_ne_pi_half_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) (j : Fin 3) :
    d.tile.angle j ≠ Real.pi / 2 := by
  intro h
  exact hnot (d.right_tile_necessary hn j h)

end Erdos633b.Tiling
