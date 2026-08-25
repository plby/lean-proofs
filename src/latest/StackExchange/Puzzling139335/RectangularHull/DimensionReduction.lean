import StackExchange.Puzzling139335.RectangularHull.SmallHulls
import StackExchange.Puzzling139335.SquareGeometry

/-!
# A remaining rectangular hull has one unit edge

Corner coverage bounds both intrinsic edge lengths by one. The small-hull
case excludes two strict inequalities, and the diameter-pair theorem excludes
two equalities. Interchanging the frame edges leaves a common `1 × h` hull,
where `0 < h < 1`.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem CommonFrames.edge_lengths_le_one {d : SquareDissection} (F : CommonFrames d)
    (i : Fin 4) : ‖(F.frame i).first‖ ≤ 1 ∧ ‖(F.frame i).second‖ ≤ 1 := by
  obtain ⟨j, hj⟩ := d.exists_piece_mem (corner_mem_unitSquare 0)
  have hAxis := (F.frame j).axisAligned_of_piece_corner (F.hull_eq j) (d.piece_subset j) hj
  have hb := (F.frame j).box_bounds_in_square (F.carrier_subset_square j)
  have hboth : ‖(F.frame j).first‖ ≤ 1 ∧ ‖(F.frame j).second‖ ≤ 1 := by
    rcases (F.frame j).axisBox_side_lengths hAxis with h | h
    all_goals constructor <;> linarith [h.1, h.2, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  simpa only [F.first_length_eq i j, F.second_length_eq i j] using hboth

theorem Frame.opposite_vertices_dist_sq (R : Frame) :
    dist R.origin (R.origin + R.first + R.second) ^ 2 =
      ‖R.first‖ ^ 2 + ‖R.second‖ ^ 2 := by
  rw [dist_eq_norm]
  have hdiff : R.origin - (R.origin + R.first + R.second) = -(R.first + R.second) := by abel
  rw [hdiff, norm_neg, norm_add_sq_real, R.orthogonal]
  ring

theorem CommonFrames.not_both_unit {d : SquareDissection} (F : CommonFrames d)
    (hc : d.HasProtectedCenter) (i : Fin 4)
    (hf : ‖(F.frame i).first‖ = 1) (hs : ‖(F.frame i).second‖ = 1) : False := by
  have hv := (F.frame i).vertices_subset_of_convexHull_eq (F.hull_eq i)
  apply d.no_diameter_pair hc i (hv (F.frame i).origin_mem_vertices)
    (hv (F.frame i).both_mem_vertices)
  rw [(F.frame i).opposite_vertices_dist_sq, hf, hs]
  norm_num

theorem CommonFrames.one_edge_unit {d : SquareDissection} (F : CommonFrames d)
    (hc : d.HasProtectedCenter) :
    ‖(F.frame 0).first‖ = 1 ∨ ‖(F.frame 0).second‖ = 1 := by
  have hb := F.edge_lengths_le_one 0
  by_cases hf : ‖(F.frame 0).first‖ = 1
  · exact Or.inl hf
  · right
    by_contra hs
    exact F.no_protectedCenter_of_small (lt_of_le_of_ne hb.1 hf)
      (lt_of_le_of_ne hb.2 hs) hc

def Frame.swap (R : Frame) : Frame where
  origin := R.origin
  first := R.second
  second := R.first
  first_ne_zero := R.second_ne_zero
  second_ne_zero := R.first_ne_zero
  orthogonal := by rw [real_inner_comm]; exact R.orthogonal

@[simp] theorem Frame.swap_first (R : Frame) : R.swap.first = R.second := rfl

@[simp] theorem Frame.swap_second (R : Frame) : R.swap.second = R.first := rfl

theorem Frame.swap_vertices (R : Frame) : R.swap.vertices = R.vertices := by
  have h : R.origin + R.second + R.first = R.origin + R.first + R.second := by abel
  ext x
  simp only [vertices, swap, mem_insert_iff, mem_singleton_iff, h]
  tauto

@[simp] theorem Frame.swap_carrier (R : Frame) : R.swap.carrier = R.carrier := by
  rw [carrier, swap_vertices]
  rfl

def CommonFrames.swap {d : SquareDissection} (F : CommonFrames d) : CommonFrames d where
  frame i := (F.frame i).swap
  hull_eq i := by simpa only [Frame.swap_carrier] using F.hull_eq i
  first_length_eq i j := F.second_length_eq i j
  second_length_eq i j := F.first_length_eq i j

/-- The common hulls of a putative counterexample can be represented by
frames whose first edge has length one and whose second edge has a common
strictly smaller positive length. -/
theorem exists_unit_edge_frames {d : SquareDissection} (F : CommonFrames d)
    (hc : d.HasProtectedCenter) :
    ∃ G : CommonFrames d, ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      (∀ i, ‖(G.frame i).first‖ = 1) ∧ (∀ i, ‖(G.frame i).second‖ = h) := by
  rcases F.one_edge_unit hc with hf | hs
  · refine ⟨F, ‖(F.frame 0).second‖, norm_pos_iff.mpr (F.frame 0).second_ne_zero, ?_, ?_, ?_⟩
    · exact lt_of_le_of_ne (F.edge_lengths_le_one 0).2
        (fun hs => F.not_both_unit hc 0 hf hs)
    · intro i
      exact (F.first_length_eq i 0).trans hf
    · exact fun i => F.second_length_eq i 0
  · refine ⟨F.swap, ‖(F.frame 0).first‖, norm_pos_iff.mpr (F.frame 0).first_ne_zero, ?_, ?_, ?_⟩
    · exact lt_of_le_of_ne (F.edge_lengths_le_one 0).1
        (fun hf => F.not_both_unit hc 0 hf hs)
    · intro i
      exact (F.second_length_eq i 0).trans hs
    · exact fun i => F.first_length_eq i 0

end Puzzling139335.RectangularHull
