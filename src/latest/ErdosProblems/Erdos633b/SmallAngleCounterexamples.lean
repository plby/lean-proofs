import ErdosProblems.Erdos633b.SmallAngleCornerLimits

/-! The seven small-angle local relations all force a 120-degree tile
in a hypothetical nonsquare counterexample. -/

namespace Erdos633b.Tiling

theorem small_angle_counterexample_forces_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hsmall : d.tile.angle 0 < Real.pi / 21) : d.tile.angle 2 = 2 * Real.pi / 3 := by
  have hrel : SmallAngleLocalRelation (d.tile.angle 0) (d.tile.angle 1) := by
    rcases d.counterexample_small_relation_or_bounded_corners hn hnot h01 h12 with hs | hb
    · exact hs
    · exact False.elim (not_le_of_gt hsmall hb.1)
  obtain ⟨t, ht, he⟩ := hrel
  simp only [smallAngleRelationTriples, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply d.small_angle_thirds_forces_two_pi_thirds hn hnot h01 h12 hsmall 0
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    exact he
  · exfalso
    apply d.small_angle_fifths_impossible hn hnot h01 h12 hsmall 0
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    exact he
  · apply d.small_angle_thirds_forces_two_pi_thirds hn hnot h01 h12 hsmall 1
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    linarith
  · exfalso
    apply d.small_angle_fifths_impossible hn hnot h01 h12 hsmall (-1)
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    linarith
  · apply d.small_angle_thirds_forces_two_pi_thirds hn hnot h01 h12 hsmall (-(1 / 2))
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    linarith
  · apply d.small_angle_thirds_forces_two_pi_thirds hn hnot h01 h12 hsmall (-2)
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    linarith
  · norm_num at he
    linarith [d.tile.angle_sum]

theorem angle_lower_of_counterexample_not_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≠ 2 * Real.pi / 3) : Real.pi / 21 ≤ d.tile.angle 0 := by
  by_contra h
  exact hγ (d.small_angle_counterexample_forces_two_pi_thirds hn hnot h01 h12 (lt_of_not_ge h))

theorem corner_local_determinant_ne_zero_of_not_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγne : d.tile.angle 2 ≠ 2 * Real.pi / 3)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (he : (t.1 : ℝ) * d.tile.angle 0 + (t.2.1 : ℝ) * d.tile.angle 1 =
      (t.2.2 : ℝ) * Real.pi) :
    cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
      (d.cornerColumnCount 2) t ≠ 0 := by
  intro hd
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hP := d.ordered_smallest_column_pos h01 h12 hγ hscalene hrep
  have htotal := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at htotal
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_local_zero_numerators _ _ _ d.tile.angle_sum _ _ _ hc t he hd
  obtain ⟨hR, hR1⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hRv : d.cornerColumnCount 2 = 0 ∨ d.cornerColumnCount 2 = 1 := by omega
  rcases hRv with hR0 | hRone
  · rw [hR0] at hd ha hb htotal
    rcases corner_local_degenerate_zero _ _ (by omega) (by omega) t ht hd ha hb with h | h | h
    · exact hnot (d.groupOne_corner_columns_necessary hn hscalene h.1 h.2 hR0)
    · exact hnot (d.groupOne_swapped_corner_columns_necessary hn hscalene h.2.1 h.2.2 hR0)
    · rw [h.1] at he
      norm_num at he
      exact hγne (by linarith [d.tile.angle_sum])
  · obtain ⟨hQ0, hP4⟩ := hR1 hRone
    rw [hRone, hQ0] at hd ha hb
    exact corner_local_degenerate_one_impossible _ hP4 t ht hd ha hb

end Erdos633b.Tiling
