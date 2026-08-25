import StackExchange.Puzzling139335.ExteriorContact.Square
import Wikipedia.SchoenfliesTheorem.ModelCurve

/-!
# Two straight boundary segments at each square corner

The adjacent horizontal and vertical sides of the unit square are nontrivial
segments meeting only at their common corner.
-/

open Set

namespace Puzzling139335

private theorem horizontal_side_subset_frontier {x u y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hy : y = 0 ∨ y = 1) :
    segment ℝ (Schoenflies.Plane.mk x y) (Schoenflies.Plane.mk u y) ⊆
      frontier unitSquare := by
  intro p hp
  obtain ⟨hp1, hp0⟩ := Schoenflies.mem_segment_horiz.mp hp
  have hb : p 0 ∈ Icc (0 : ℝ) 1 := (convex_Icc (0 : ℝ) 1).segment_subset hx hu hp0
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_snd
  · rw [hp1]
    rcases hy with rfl | rfl <;> norm_num [squareCenter]
  · change |p 0 - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]

private theorem vertical_side_subset_frontier {x y v : ℝ}
    (hx : x = 0 ∨ x = 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    segment ℝ (Schoenflies.Plane.mk x y) (Schoenflies.Plane.mk x v) ⊆
      frontier unitSquare := by
  intro p hp
  obtain ⟨hp0, hp1⟩ := Schoenflies.mem_segment_vert.mp hp
  have hb : p 1 ∈ Icc (0 : ℝ) 1 := (convex_Icc (0 : ℝ) 1).segment_subset hy hv hp1
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
  · rw [hp0]
    rcases hx with rfl | rfl <;> norm_num [squareCenter]
  · change |p 1 - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]

private theorem horizontal_vertical_segments_inter (x y u v : ℝ) :
    segment ℝ (Schoenflies.Plane.mk x y) (Schoenflies.Plane.mk u y) ∩
      segment ℝ (Schoenflies.Plane.mk x y) (Schoenflies.Plane.mk x v) =
        {Schoenflies.Plane.mk x y} := by
  apply subset_antisymm
  · rintro p ⟨hp, hq⟩
    apply mem_singleton_iff.mpr
    ext i
    fin_cases i
    · exact (Schoenflies.mem_segment_vert.mp hq).1
    · exact (Schoenflies.mem_segment_horiz.mp hp).1
  · rintro p rfl
    exact ⟨left_mem_segment _ _ _, left_mem_segment _ _ _⟩

private theorem two_straight_segments_of_coordinates (x y : ℝ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    ∃ a b : Plane,
      a ≠ Schoenflies.Plane.mk x y ∧ b ≠ Schoenflies.Plane.mk x y ∧
      segment ℝ (Schoenflies.Plane.mk x y) a ⊆ frontier unitSquare ∧
      segment ℝ (Schoenflies.Plane.mk x y) b ⊆ frontier unitSquare ∧
      segment ℝ (Schoenflies.Plane.mk x y) a ∩
        segment ℝ (Schoenflies.Plane.mk x y) b = {Schoenflies.Plane.mk x y} := by
  refine ⟨Schoenflies.Plane.mk (1 - x) y, Schoenflies.Plane.mk x (1 - y),
    ?_, ?_, ?_, ?_, horizontal_vertical_segments_inter x y (1 - x) (1 - y)⟩
  · intro heq
    have h := congrArg (fun p : Plane => p 0) heq
    rcases hx with rfl | rfl <;> norm_num at h
  · intro heq
    have h := congrArg (fun p : Plane => p 1) heq
    rcases hy with rfl | rfl <;> norm_num at h
  · apply horizontal_side_subset_frontier _ _ hy
    · rcases hx with rfl | rfl <;> norm_num
    · rcases hx with rfl | rfl <;> norm_num
  · apply vertical_side_subset_frontier hx
    · rcases hy with rfl | rfl <;> norm_num
    · rcases hy with rfl | rfl <;> norm_num

/-- Each square corner is the unique common point of two nontrivial straight
segments in the square boundary. -/
theorem square_corner_two_straight_segments (c : Fin 4) :
    ∃ a b : Plane, a ≠ corner c ∧ b ≠ corner c ∧
      segment ℝ (corner c) a ⊆ frontier unitSquare ∧
      segment ℝ (corner c) b ⊆ frontier unitSquare ∧
      segment ℝ (corner c) a ∩ segment ℝ (corner c) b = {corner c} := by
  have hp : corner c = Schoenflies.Plane.mk (corner c 0) (corner c 1) := by
    ext i
    fin_cases i <;> rfl
  have hx : corner c 0 = 0 ∨ corner c 0 = 1 := by
    by_cases h : c = 1 ∨ c = 2 <;> simp [corner, h]
  have hy : corner c 1 = 0 ∨ corner c 1 = 1 := by
    by_cases h : c = 2 ∨ c = 3 <;> simp [corner, h]
  simpa only [← hp] using two_straight_segments_of_coordinates (corner c 0) (corner c 1) hx hy

end Puzzling139335
