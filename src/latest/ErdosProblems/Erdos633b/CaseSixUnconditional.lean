import ErdosProblems.Erdos633b.GroupOneFirstSmallOrders
import ErdosProblems.Erdos633b.TileIncommensurableNecessity

/-! Unconditional necessity for the first group-1 outer shape, with
both rational and irrational reference-angle regimes and every labeling. -/

namespace Erdos633b.Tiling

theorem caseSix_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) : EightCases T := by
  by_cases hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)
  · have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
      have ht := T.angle_sum
      rw [h0, h1, h2] at ht
      linarith
    rcases d.groupOne_first_commensurable_angle_cases hrat h0 h1 h2 with ha | ha | ha
    · refine ⟨Equiv.swap 1 2, Or.inl ?_⟩
      change T.angle 0 = T.angle 2
      linarith
    · refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
      change T.angle 0 = Real.pi / 6 ∧ T.angle 2 = Real.pi / 2 ∧
        T.angle 1 = Real.pi / 3
      exact ⟨by linarith, by linarith, by linarith⟩
    · apply d.reptiling_equal_angles_necessary hn
      intro i
      fin_cases i
      · exact h0.symm
      · change d.tile.angle 1 = T.angle 1
        linarith
      · change d.tile.angle 2 = T.angle 2
        linarith [d.tile.angle_sum]
  · exact d.incommensurable_tile_necessary hn hrat

theorem caseSix_necessary_unconditional_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h2 : Triangle.angle (T.reindex f) 2 = 2 * Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  exact d'.caseSix_necessary_unconditional hn h0 h1 h2

end Erdos633b.Tiling
