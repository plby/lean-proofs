import ErdosProblems.Erdos633b.Boundary30DoubleExclusion
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions4
import ErdosProblems.Erdos633b.SmallPrimitivePhases
import ErdosProblems.Erdos633b.TileIncommensurableNecessity

/-! Rational tilings in the fourth group-2 shape force an equilateral
outer triangle. Combining with the proved irrational-tile theorem gives
unconditional nonsquare necessity for this shape and every labeling. -/

namespace Erdos633b.Tiling

theorem groupTwo_fourth_not_phase_15 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : d.tile.angle 0 ≠ 2 * Real.pi * 2 / 15 := by
  intro hα
  apply d.boundary30Double_impossible
  · intro i
    fin_cases i
    · change d.tile.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  · intro i
    fin_cases i
    · change T.angle 0 = ((8 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((5 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_fourth_not_phase_30 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : d.tile.angle 0 ≠ 2 * Real.pi * 1 / 30 := by
  intro hα
  have hs0 : (Equiv.swap (0 : Fin 3) 1) ((fun i : Fin 3 => i) ⟨0, by decide⟩) = 1 := by decide
  have hs1 : (Equiv.swap (0 : Fin 3) 1) ((fun i : Fin 3 => i) ⟨1, by decide⟩) = 0 := by decide
  let d' := (d.reindexTile (Equiv.swap 0 1)).reindexOuter (Equiv.swap 0 1)
  apply d'.boundary30Double_impossible
  · intro i
    change Triangle.angle (d.tile.reindex (Equiv.swap 0 1)) i =
      (boundary30DoubleTileWeights i : ℝ) * (Real.pi / 15)
    rw [Triangle.angle_reindex, Equiv.symm_swap]
    fin_cases i
    · rw [hs0]
      change d.tile.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · rw [hs1]
      change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  · intro i
    change Triangle.angle (T.reindex (Equiv.swap 0 1)) i =
      (boundary30DoubleOuterWeights i : ℝ) * (Real.pi / 15)
    rw [Triangle.angle_reindex, Equiv.symm_swap]
    fin_cases i
    · rw [hs0]
      change T.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · rw [hs1]
      change T.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      change T.angle 2 = ((5 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_fourth_commensurable_equilateral {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    T.angle 0 = Real.pi / 3 ∧ T.angle 1 = Real.pi / 3 ∧ T.angle 2 = Real.pi / 3 := by
  have hs : GroupTwoShape d.tile T := ⟨hg, Or.inr (Or.inr (Or.inr ⟨h0, h1, h2⟩))⟩
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_primitive_phase_cases hrat hs
  simp only [smallPrimitivePhases, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num only [Nat.cast_ofNat, Nat.cast_one] at ha
  · exact False.elim (d.groupTwo_residue_exclusion_7_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_8_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_9_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_10_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_11_1_4 hg h0 h1 h2 ha)
  · exact ⟨by linarith [d.tile.angle_sum], by linarith [d.tile.angle_sum],
      by linarith [d.tile.angle_sum]⟩
  · exact False.elim (d.groupTwo_residue_exclusion_13_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_13_2_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_14_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_15_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_fourth_not_phase_15 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_16_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_18_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_20_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_20_3_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_21_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_21_2_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_22_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_22_3_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_24_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_26_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_26_3_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_28_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_28_3_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_fourth_not_phase_30 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_36_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_36_5_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_42_1_4 hg h0 h1 h2 ha)
  · exact False.elim (d.groupTwo_residue_exclusion_42_5_4 hg h0 h1 h2 ha)

theorem groupTwo_fourth_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : EightCases T := by
  by_cases hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)
  · have he := d.groupTwo_fourth_commensurable_equilateral hrat hg h0 h1 h2
    refine ⟨Equiv.refl _, Or.inl ?_⟩
    change T.angle 0 = T.angle 1
    exact he.1.trans he.2.1.symm
  · exact d.incommensurable_tile_necessary hn hrat

theorem groupTwo_fourth_necessary_unconditional_reindex {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (e f : Equiv.Perm (Fin 3))
    (hg : Triangle.angle (d.tile.reindex e) 2 = 2 * Real.pi / 3)
    (h0 : Triangle.angle (T.reindex f) 0 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 = 2 * Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  exact d'.groupTwo_fourth_necessary_unconditional hn hg h0 h1 h2

end Erdos633b.Tiling
