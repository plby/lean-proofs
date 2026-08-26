import ErdosProblems.Erdos633b.LargeMiddleInventory
import ErdosProblems.Erdos633b.GroupOneCornerNecessity
import ErdosProblems.Erdos633b.NonrightLocalRelations

/-! A denominator-independent necessary-direction theorem when the
middle reference angle exceeds two fifths of pi, and a sharper remaining domain. -/

namespace Erdos633b.Tiling

theorem large_middle_tile_ordered_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hβ : 2 * Real.pi / 5 < d.tile.angle 1) : EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · by_cases hrep : ReptilingAngles d.tile T
    · exact d.reptiling_necessary hn hrep
    · obtain ⟨hP, hQ, hR⟩ := d.large_middle_groupOne_columns h01 h12 hβ hscalene hrep
      exact d.groupOne_corner_columns_necessary hn hscalene hP hQ hR
  · exact eightCases_of_not_injective_angles T hscalene

theorem large_middle_tile_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (e : Equiv.Perm (Fin 3))
    (h01 : Triangle.angle (d.tile.reindex e) 0 < Triangle.angle (d.tile.reindex e) 1)
    (h12 : Triangle.angle (d.tile.reindex e) 1 < Triangle.angle (d.tile.reindex e) 2)
    (hβ : 2 * Real.pi / 5 < Triangle.angle (d.tile.reindex e) 1) : EightCases T :=
  (d.reindexTile e).large_middle_tile_ordered_necessary hn h01 h12 hβ

theorem middle_angle_le_two_pi_fifths_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    d.tile.angle 1 ≤ 2 * Real.pi / 5 := by
  by_contra h
  exact hnot (d.large_middle_tile_ordered_necessary hn h01 h12 (lt_of_not_ge h))

theorem counterexample_ordered_small_middle {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e : Equiv.Perm (Fin 3),
      let S : Triangle := d.tile.reindex e
      S.angle 0 < S.angle 1 ∧ S.angle 1 < S.angle 2 ∧
        S.angle 1 ≤ 2 * Real.pi / 5 ∧
        S.angle 2 ≤ 2 * Real.pi / 3 ∧ S.angle 2 ≠ Real.pi / 2 ∧
        (∀ i, IsRational (S.angle i / Real.pi)) ∧
        OrderedNonrightLocalRelation (S.angle 0) (S.angle 1) := by
  obtain ⟨e, h01, h12, hγ, hne, hrat, hrel⟩ := d.counterexample_ordered_relations hn hnot
  exact ⟨e, h01, h12,
    (d.reindexTile e).middle_angle_le_two_pi_fifths_of_counterexample hn hnot h01 h12,
    hγ, hne, hrat, hrel⟩

end Erdos633b.Tiling
