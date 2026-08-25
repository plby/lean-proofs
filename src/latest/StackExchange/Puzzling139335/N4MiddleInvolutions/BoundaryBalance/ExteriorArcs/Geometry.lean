import StackExchange.Puzzling139335.ExteriorContact.Square
import StackExchange.Puzzling139335.JordanTransport
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import Wikipedia.SchoenfliesTheorem.ModelCurve

/-! The three consecutive square-side segments making up an outer contact arc. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

/-- The lower outer arc, traversed down the left side, along the base,
and up the right side. -/
def lowerOuterArc (a b : ℝ) : Set Plane :=
  (segment ℝ (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0) ∪
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0)) ∪
    segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 b)

/-- The upper outer arc, obtained by reflection in the horizontal midline. -/
noncomputable def upperOuterArc (a b : ℝ) : Set Plane :=
  ReflectionSeparation.horizontal '' lowerOuterArc a b

/-- Membership in the lower outer arc is membership in one of its three sides. -/
theorem mem_lowerOuterArc_iff {a b : ℝ} {p : Plane} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p ∈ lowerOuterArc a b ↔
      (p 0 = 0 ∧ p 1 ∈ Icc 0 a) ∨
      (p 1 = 0 ∧ p 0 ∈ Icc 0 1) ∨
      (p 0 = 1 ∧ p 1 ∈ Icc 0 b) := by
  simp only [lowerOuterArc, mem_union, Schoenflies.mem_segment_vert,
    Schoenflies.mem_segment_horiz, segment_symm ℝ a 0, segment_eq_Icc ha,
    segment_eq_Icc hb, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num), or_assoc]

/-- The lower outer arc has the specified endpoints when both vertical legs
have positive length. -/
theorem lowerOuterArc_isArcBetween {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Schoenflies.IsArcBetween (lowerOuterArc a b)
      (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 1 b) := by
  have hleft : Schoenflies.Plane.mk 0 a ≠ Schoenflies.Plane.mk 0 0 := by
    intro heq
    exact (ne_of_gt ha) (congrArg (fun z : Plane => z 1) heq)
  have hbase : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 1 0 := by
    intro heq
    have h := congrArg (fun z : Plane => z 0) heq
    norm_num at h
  have hright : Schoenflies.Plane.mk 1 0 ≠ Schoenflies.Plane.mk 1 b := by
    intro heq
    exact (ne_of_lt hb) (congrArg (fun z : Plane => z 1) heq)
  have hmeetAB : ∀ z ∈ segment ℝ (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0),
      z ∈ segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) →
      z = Schoenflies.Plane.mk 0 0 := by
    intro z hzA hzB
    have hz0 := (Schoenflies.mem_segment_vert.mp hzA).1
    have hz1 := (Schoenflies.mem_segment_horiz.mp hzB).1
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hmeetC : ∀ z ∈
      segment ℝ (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0) ∪
        segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0),
      z ∈ segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 b) →
      z = Schoenflies.Plane.mk 1 0 := by
    intro z hzAB hzC
    have hz0 := (Schoenflies.mem_segment_vert.mp hzC).1
    rcases hzAB with hzA | hzB
    · have hz0' := (Schoenflies.mem_segment_vert.mp hzA).1
      exact False.elim (by linarith)
    · have hz1 := (Schoenflies.mem_segment_horiz.mp hzB).1
      ext i
      fin_cases i
      · exact hz0
      · exact hz1
  exact ((Schoenflies.isArcBetween_segment hleft).concatenate
    (Schoenflies.isArcBetween_segment hbase) hmeetAB).concatenate
      (Schoenflies.isArcBetween_segment hright) hmeetC

/-- The bottom-left corner belongs to every lower outer arc. -/
theorem bottom_left_mem_lowerOuterArc (a b : ℝ) :
    Schoenflies.Plane.mk 0 0 ∈ lowerOuterArc a b :=
  Or.inl (Or.inr (left_mem_segment ℝ _ _))

/-- The bottom-right corner belongs to every lower outer arc. -/
theorem bottom_right_mem_lowerOuterArc (a b : ℝ) :
    Schoenflies.Plane.mk 1 0 ∈ lowerOuterArc a b :=
  Or.inl (Or.inr (right_mem_segment ℝ _ _))

/-- The entire square base belongs to every lower outer arc. -/
theorem bottom_segment_subset_lowerOuterArc (a b : ℝ) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆
      lowerOuterArc a b := by
  intro p hp
  exact Or.inl (Or.inr hp)

/-- If both leg heights lie in the unit interval, the lower outer arc is
contained in the square frontier. -/
theorem lowerOuterArc_subset_frontier_unitSquare {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    lowerOuterArc a b ⊆ frontier unitSquare := by
  intro p hp
  rw [unitSquare_eq_closedSquare]
  rcases (mem_lowerOuterArc_iff ha hb).mp hp with hleft | hbase | hright
  · apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
    · change |p 0 - (1 / 2 : ℝ)| = 1 / 2
      rw [hleft.1]
      norm_num
    · change |p 1 - (1 / 2 : ℝ)| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith [hleft.2.1, hleft.2.2]
  · apply Schoenflies.Plane.mem_frontier_closedSquare_of_snd
    · change |p 1 - (1 / 2 : ℝ)| = 1 / 2
      rw [hbase.1]
      norm_num
    · change |p 0 - (1 / 2 : ℝ)| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith [hbase.2.1, hbase.2.2]
  · apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
    · change |p 0 - (1 / 2 : ℝ)| = 1 / 2
      rw [hright.1]
      norm_num
    · change |p 1 - (1 / 2 : ℝ)| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith [hright.2.1, hright.2.2]

private theorem horizontal_mk (x y : ℝ) :
    ReflectionSeparation.horizontal (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (1 - y) := by
  ext i
  fin_cases i <;> simp

/-- Horizontal reflection gives the upper arc and its explicit endpoints. -/
theorem upperOuterArc_isArcBetween {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Schoenflies.IsArcBetween (upperOuterArc a b)
      (Schoenflies.Plane.mk 0 (1 - a)) (Schoenflies.Plane.mk 1 (1 - b)) := by
  have h := (lowerOuterArc_isArcBetween ha hb).image_homeomorph
    ReflectionSeparation.horizontal.toHomeomorph
  change Schoenflies.IsArcBetween (upperOuterArc a b)
    (ReflectionSeparation.horizontal (Schoenflies.Plane.mk 0 a))
    (ReflectionSeparation.horizontal (Schoenflies.Plane.mk 1 b)) at h
  simpa only [horizontal_mk] using h

/-- The upper reflected arc also lies on the square frontier. -/
theorem upperOuterArc_subset_frontier_unitSquare {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    upperOuterArc a b ⊆ frontier unitSquare := by
  have hfront : ReflectionSeparation.horizontal '' frontier unitSquare =
      frontier unitSquare :=
    (ReflectionSeparation.horizontal.toHomeomorph.image_frontier unitSquare).trans
      (congrArg frontier ReflectionSeparation.horizontal_image_unitSquare)
  rw [← hfront]
  exact image_mono (lowerOuterArc_subset_frontier_unitSquare ha hb ha1 hb1)

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
