import ErdosProblems.Erdos633b.GroupTwoPhaseLists
import ErdosProblems.Erdos633b.GroupTwoFinitePhaseExclusions
import ErdosProblems.Erdos633b.GroupTwoFourthUnconditional

/-! Unconditional nonsquare necessity for all four group-2 outer shapes.
The rational phases are exhausted by exact degree, residue, boundary and
area proofs, and the irrational tile branch is already proved. -/

namespace Erdos633b.Tiling

theorem groupTwo_first_necessary_commensurable {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) : EightCases T := by
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_first_phase_cases hrat hg h0 h1 h2
  simp only [groupTwoPhasePairs1, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num only [Nat.cast_one, Nat.cast_ofNat] at ha
  · apply eightCases_of_not_injective_angles T
    intro hi
    have he : T.angle 0 = T.angle 2 := by linarith [d.tile.angle_sum]
    exact (by decide : (0 : Fin 3) ≠ 2) (hi he)
  · apply eightCases_of_not_injective_angles T
    intro hi
    have he : T.angle 1 = T.angle 2 := by linarith [d.tile.angle_sum]
    exact (by decide : (1 : Fin 3) ≠ 2) (hi he)
  · refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
    change T.angle 0 = Real.pi / 6 ∧ T.angle 2 = Real.pi / 2 ∧ T.angle 1 = Real.pi / 3
    exact ⟨by linarith [d.tile.angle_sum], by linarith [d.tile.angle_sum],
      by linarith [d.tile.angle_sum]⟩
  · exact False.elim (d.groupTwo_phase_exclusion_15_2_1 hg h0 h1 h2 ha)
  · apply d.reptiling_equal_angles_necessary hn
    intro i
    fin_cases i
    · exact h0.symm
    · change d.tile.angle 1 = T.angle 1
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = T.angle 2
      linarith [d.tile.angle_sum]
  · exact False.elim (d.groupTwo_phase_exclusion_20_1_1 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_phase_exclusion_20_3_1 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_phase_exclusion_30_1_1 hg h0 h1 h2 ha)

theorem groupTwo_first_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) : EightCases T := by
  by_cases hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)
  · exact d.groupTwo_first_necessary_commensurable hn hrat hg h0 h1 h2
  · exact d.incommensurable_tile_necessary hn hrat

theorem groupTwo_first_necessary_unconditional_reindex {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (e f : Equiv.Perm (Fin 3))
    (hg : Triangle.angle (d.tile.reindex e) 2 = 2 * Real.pi / 3)
    (h0 : Triangle.angle (T.reindex f) 0 =
      Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 =
      2 * Triangle.angle (d.tile.reindex e) 0)
    (h2 : Triangle.angle (T.reindex f) 2 =
      3 * Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  exact d'.groupTwo_first_necessary_unconditional hn hg h0 h1 h2

theorem groupTwo_second_necessary_commensurable {T : Triangle} {n : ℕ} (d : Tiling T n)
    (_hn : ¬ IsSquare n) (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) : EightCases T := by
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_second_phase_cases hrat hg h0 h1 h2
  simp only [groupTwoPhasePairs2, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num only [Nat.cast_one, Nat.cast_ofNat] at ha
  · apply eightCases_of_not_injective_angles T
    intro hi
    have he : T.angle 0 = T.angle 1 := by linarith [d.tile.angle_sum]
    exact (by decide : (0 : Fin 3) ≠ 1) (hi he)
  · refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
    change T.angle 0 = Real.pi / 6 ∧ T.angle 2 = Real.pi / 2 ∧ T.angle 1 = Real.pi / 3
    exact ⟨by linarith [d.tile.angle_sum], by linarith [d.tile.angle_sum],
      by linarith [d.tile.angle_sum]⟩
  · exact False.elim (d.groupTwo_phase_exclusion_15_2_2 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_phase_exclusion_16_1_2 hg h0 h1 h2 ha)
  · apply eightCases_of_not_injective_angles T
    intro hi
    have he : T.angle 1 = T.angle 2 := by linarith [d.tile.angle_sum]
    exact (by decide : (1 : Fin 3) ≠ 2) (hi he)
  · exact False.elim (d.groupTwo_phase_exclusion_24_1_2 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_phase_exclusion_30_1_2 hg h0 h1 h2 ha)

theorem groupTwo_second_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) : EightCases T := by
  by_cases hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)
  · exact d.groupTwo_second_necessary_commensurable hn hrat hg h0 h1 h2
  · exact d.incommensurable_tile_necessary hn hrat

theorem groupTwo_second_necessary_unconditional_reindex {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (e f : Equiv.Perm (Fin 3))
    (hg : Triangle.angle (d.tile.reindex e) 2 = 2 * Real.pi / 3)
    (h0 : Triangle.angle (T.reindex f) 0 =
      Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 =
      2 * Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      2 * Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  exact d'.groupTwo_second_necessary_unconditional hn hg h0 h1 h2

theorem groupTwo_third_necessary_commensurable {T : Triangle} {n : ℕ} (d : Tiling T n)
    (_hn : ¬ IsSquare n) (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) : EightCases T := by
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_third_phase_cases hrat hg h0 h1 h2
  simp only [groupTwoPhasePairs3, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num only [Nat.cast_one, Nat.cast_ofNat] at ha
  · exact False.elim (d.groupTwo_phase_exclusion_8_1_3 hg h0 h1 h2 ha)
  · refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
    change T.angle 0 = Real.pi / 6 ∧ T.angle 2 = Real.pi / 2 ∧ T.angle 1 = Real.pi / 3
    exact ⟨by linarith [d.tile.angle_sum], by linarith [d.tile.angle_sum],
      by linarith [d.tile.angle_sum]⟩
  · exact False.elim (d.groupTwo_phase_exclusion_20_1_3 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_phase_exclusion_20_3_3 hg h0 h1 h2 ha)

theorem groupTwo_third_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) : EightCases T := by
  by_cases hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)
  · exact d.groupTwo_third_necessary_commensurable hn hrat hg h0 h1 h2
  · exact d.incommensurable_tile_necessary hn hrat

theorem groupTwo_third_necessary_unconditional_reindex {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (e f : Equiv.Perm (Fin 3))
    (hg : Triangle.angle (d.tile.reindex e) 2 = 2 * Real.pi / 3)
    (h0 : Triangle.angle (T.reindex f) 0 =
      Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      Triangle.angle (d.tile.reindex e) 0 + 2 * Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  exact d'.groupTwo_third_necessary_unconditional hn hg h0 h1 h2

theorem groupTwo_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hs : GroupTwoShape d.tile T) : EightCases T := by
  obtain ⟨hg, hs⟩ := hs
  rcases hs with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact d.groupTwo_first_necessary_unconditional hn hg h0 h1 h2
  · exact d.groupTwo_second_necessary_unconditional hn hg h0 h1 h2
  · exact d.groupTwo_third_necessary_unconditional hn hg h0 h1 h2
  · exact d.groupTwo_fourth_necessary_unconditional hn hg h0 h1 h2

end Erdos633b.Tiling
