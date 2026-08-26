import ErdosProblems.Erdos633b.AngleDeterminant

/-! Kernel-checked degeneracies of the integral corner/local determinant.
Only the group-1 and group-2 corner totals survive the finite relation list. -/

namespace Erdos633b

theorem corner_local_degenerate_zero (P Q : ℕ) (hP : 1 ≤ P) (htotal : 5 ≤ P + Q)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (hd : cornerLocalDeterminant P Q 0 t = 0)
    (ha : cornerLocalAlphaNumerator P Q 0 t = 0)
    (hb : cornerLocalBetaNumerator P Q 0 t = 0) :
    (P = 3 ∧ Q = 2) ∨ (t = (2, 3, 1) ∧ P = 2 ∧ Q = 3) ∨
      (t = (3, 3, 1) ∧ P = 3 ∧ Q = 3) := by
  have ht := (Finset.mem_erase.mp ht).2
  simp only [orderedRelationTriples, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals norm_num [cornerLocalDeterminant, cornerLocalAlphaNumerator,
    cornerLocalBetaNumerator, Prod.mk.injEq] at * <;> omega

theorem corner_local_degenerate_one_impossible (P : ℕ) (hP : 4 ≤ P)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (hd : cornerLocalDeterminant P 0 1 t = 0)
    (ha : cornerLocalAlphaNumerator P 0 1 t = 0)
    (hb : cornerLocalBetaNumerator P 0 1 t = 0) : False := by
  have ht := (Finset.mem_erase.mp ht).2
  simp only [orderedRelationTriples, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals norm_num [cornerLocalDeterminant, cornerLocalAlphaNumerator,
    cornerLocalBetaNumerator] at * <;> omega

namespace Tiling

theorem corner_local_determinant_ne_zero_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (hne : t ∉ smallAngleRelationTriples)
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
    · exact hne (h.1 ▸ (by decide : (2, 3, 1) ∈ smallAngleRelationTriples))
    · exact hne (h.1 ▸ (by decide : (3, 3, 1) ∈ smallAngleRelationTriples))
  · obtain ⟨hQ0, hP4⟩ := hR1 hRone
    rw [hRone, hQ0] at hd ha hb
    exact corner_local_degenerate_one_impossible _ hP4 t ht hd ha hb

end Tiling
end Erdos633b
