import StackExchange.Puzzling139335.ExteriorContact.Square
import StackExchange.Puzzling139335.JordanSubarc
import Wikipedia.SchoenfliesTheorem.ModelCurve

/-!
# Ordered bottom-side points on the square boundary

The bottom segment between the first and third of four ordered points is
one arc of a cut pair. The second point belongs only to that arc, while
the fourth belongs only to the complementary arc.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- Every point of the closed bottom side lies on the square boundary. -/
theorem bottom_mem_frontier {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Schoenflies.Plane.mk x 0 ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_snd
  · norm_num [squareCenter]
  · change |x - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith

/-- A segment between ordered bottom-side points is contained in the
square boundary. -/
theorem bottom_segment_subset_frontier {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    segment ℝ (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk c 0) ⊆
      frontier unitSquare := by
  intro p hp
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hac] at hp
  have heq : p = Schoenflies.Plane.mk (p 0) 0 := by
    ext i
    fin_cases i
    · rfl
    · exact hp.1
  rw [heq]
  exact bottom_mem_frontier (ha.trans hp.2.1) (hp.2.2.trans hc)

/-- Four strictly ordered bottom-side points alternate between the two
boundary arcs cut out by the first and third points. -/
theorem bottom_alternating_cutPair {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1) :
    ∃ A B, Schoenflies.IsCutPair (frontier unitSquare)
      (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk c 0) A B ∧
      Schoenflies.Plane.mk b 0 ∈ A ∧ Schoenflies.Plane.mk b 0 ∉ B ∧
      Schoenflies.Plane.mk d 0 ∈ B ∧ Schoenflies.Plane.mk d 0 ∉ A := by
  have hac : a < c := hab.trans hbc
  have hne : Schoenflies.Plane.mk a 0 ≠ Schoenflies.Plane.mk c 0 := by
    intro heq
    exact (ne_of_lt hac) (congrArg (fun p : Plane => p 0) heq)
  obtain ⟨B, hcut⟩ :=
    isJordanCurve_frontier_unitSquare.exists_cutPair_of_subset_arc
      (Schoenflies.isArcBetween_segment hne)
      (bottom_segment_subset_frontier ha hac.le (hcd.le.trans hd))
  have hbA : Schoenflies.Plane.mk b 0 ∈
      segment ℝ (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk c 0) := by
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hac.le]
    exact ⟨rfl, hab.le, hbc.le⟩
  have hbB : Schoenflies.Plane.mk b 0 ∉ B := by
    intro hb
    have hends := hcut.inter_eq ▸ (show Schoenflies.Plane.mk b 0 ∈
      segment ℝ (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk c 0) ∩ B
      from ⟨hbA, hb⟩)
    simp only [mem_insert_iff, mem_singleton_iff] at hends
    rcases hends with hba | hbc'
    · exact (ne_of_gt hab) (congrArg (fun p : Plane => p 0) hba)
    · exact (ne_of_lt hbc) (congrArg (fun p : Plane => p 0) hbc')
  have hdA : Schoenflies.Plane.mk d 0 ∉
      segment ℝ (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk c 0) := by
    intro hmem
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hac.le] at hmem
    exact (not_le_of_gt hcd) hmem.2.2
  have hdB : Schoenflies.Plane.mk d 0 ∈ B := by
    have hmem := bottom_mem_frontier (ha.trans (hac.trans hcd).le) hd
    rw [← hcut.union_eq] at hmem
    exact hmem.resolve_left hdA
  exact ⟨_, B, hcut, hbA, hbB, hdB, hdA⟩

/-- Every point of the closed top side lies on the square boundary. -/
theorem top_mem_frontier {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Schoenflies.Plane.mk x 1 ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_snd
  · norm_num [squareCenter]
  · change |x - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith

/-- Every point of the closed left side lies on the square boundary. -/
theorem left_mem_frontier {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Schoenflies.Plane.mk 0 y ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
  · norm_num [squareCenter]
  · change |y - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith

private def bottomLeftArc (a : ℝ) : Set Plane :=
  segment ℝ (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk 0 0) ∪
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 1)

private theorem bottomLeftArc_isArc (a : ℝ) :
    Schoenflies.IsArcBetween (bottomLeftArc a)
      (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk 0 1) := by
  have hleft : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 0 1 := by
    intro heq
    have := congrArg (fun p : Plane => p 1) heq
    norm_num at this
  by_cases ha : a = 0
  · subst a
    simpa [bottomLeftArc, Set.insert_eq_of_mem
      (left_mem_segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 1))]
      using Schoenflies.isArcBetween_segment hleft
  have hbottom : Schoenflies.Plane.mk a 0 ≠ Schoenflies.Plane.mk 0 0 := by
    intro heq
    exact ha (congrArg (fun p : Plane => p 0) heq)
  apply (Schoenflies.isArcBetween_segment hbottom).concatenate
    (Schoenflies.isArcBetween_segment hleft)
  intro p hp hq
  have hp0 := (Schoenflies.mem_segment_vert.mp hq).1
  have hp1 := (Schoenflies.mem_segment_horiz.mp hp).1
  ext i
  fin_cases i
  · exact hp0
  · exact hp1

/-- Oppositely ordered bottom and top points alternate between the two
boundary arcs cut out by the outer pair. -/
theorem opposing_alternating_cutPair {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hd : 0 ≤ d) (hdc : d < c) (hc : c ≤ 1) :
    ∃ A B, Schoenflies.IsCutPair (frontier unitSquare)
      (Schoenflies.Plane.mk a 0) (Schoenflies.Plane.mk c 1) A B ∧
      Schoenflies.Plane.mk d 1 ∈ A ∧ Schoenflies.Plane.mk d 1 ∉ B ∧
      Schoenflies.Plane.mk b 0 ∈ B ∧ Schoenflies.Plane.mk b 0 ∉ A := by
  have hc0 : 0 < c := hd.trans_lt hdc
  have htop : Schoenflies.Plane.mk 0 1 ≠ Schoenflies.Plane.mk c 1 := by
    intro heq
    exact (ne_of_lt hc0) (congrArg (fun p : Plane => p 0) heq)
  have hmeet : bottomLeftArc a ∩
      segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk c 1) =
      {Schoenflies.Plane.mk 0 1} := by
    apply subset_antisymm
    · rintro p ⟨hp, hq⟩
      have hp1 := (Schoenflies.mem_segment_horiz.mp hq).1
      rcases hp with hp | hp
      · have hp0 := (Schoenflies.mem_segment_horiz.mp hp).1
        exact False.elim (by linarith)
      · have hp0 := (Schoenflies.mem_segment_vert.mp hp).1
        apply mem_singleton_iff.mpr
        ext i
        fin_cases i
        · exact hp0
        · exact hp1
    · intro p hp
      obtain rfl := mem_singleton_iff.mp hp
      exact ⟨Or.inr (right_mem_segment _ _ _), left_mem_segment _ _ _⟩
  have hA := (bottomLeftArc_isArc a).concatenate
    (Schoenflies.isArcBetween_segment htop)
    (fun p hp hq => mem_singleton_iff.mp (hmeet ▸ (show p ∈ _ ∩ _ from ⟨hp, hq⟩)))
  have hsub : bottomLeftArc a ∪
      segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk c 1) ⊆
      frontier unitSquare := by
    rintro p (hp | hp)
    · rcases hp with hp | hp
      · have hbottom := bottom_segment_subset_frontier (le_refl (0 : ℝ)) ha
          (hab.le.trans hb)
        rw [segment_symm] at hp
        exact hbottom hp
      · rw [Schoenflies.mem_segment_vert, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
          at hp
        have heq : p = Schoenflies.Plane.mk 0 (p 1) := by
          ext i
          fin_cases i
          · exact hp.1
          · rfl
        rw [heq]
        exact left_mem_frontier hp.2.1 hp.2.2
    · rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hc0.le] at hp
      have heq : p = Schoenflies.Plane.mk (p 0) 1 := by
        ext i
        fin_cases i
        · rfl
        · exact hp.1
      rw [heq]
      exact top_mem_frontier hp.2.1 (hp.2.2.trans hc)
  obtain ⟨B, hcut⟩ :=
    isJordanCurve_frontier_unitSquare.exists_cutPair_of_subset_arc hA hsub
  have hdA : Schoenflies.Plane.mk d 1 ∈ bottomLeftArc a ∪
      segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk c 1) := by
    right
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hc0.le]
    exact ⟨rfl, hd, hdc.le⟩
  have hdB : Schoenflies.Plane.mk d 1 ∉ B := by
    intro hmem
    have hends := hcut.inter_eq ▸ (show Schoenflies.Plane.mk d 1 ∈
      (bottomLeftArc a ∪
        segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk c 1)) ∩ B
      from ⟨hdA, hmem⟩)
    simp only [mem_insert_iff, mem_singleton_iff] at hends
    rcases hends with hda | hdc'
    · have := congrArg (fun p : Plane => p 1) hda
      norm_num at this
    · exact (ne_of_lt hdc) (congrArg (fun p : Plane => p 0) hdc')
  have hbA : Schoenflies.Plane.mk b 0 ∉ bottomLeftArc a ∪
      segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk c 1) := by
    rintro (hmem | hmem)
    · rcases hmem with hmem | hmem
      · rw [Schoenflies.mem_segment_horiz, segment_symm ℝ a 0, segment_eq_Icc ha]
          at hmem
        exact (not_le_of_gt hab) hmem.2.2
      · have hb0 := (Schoenflies.mem_segment_vert.mp hmem).1
        exact (ne_of_gt (ha.trans_lt hab)) hb0
    · have := (Schoenflies.mem_segment_horiz.mp hmem).1
      norm_num at this
  have hbB : Schoenflies.Plane.mk b 0 ∈ B := by
    have hmem := bottom_mem_frontier (ha.trans hab.le) hb
    rw [← hcut.union_eq] at hmem
    exact hmem.resolve_left hbA
  exact ⟨_, B, hcut, hdA, hdB, hbB, hbA⟩

end Puzzling139335.RectangularHull
