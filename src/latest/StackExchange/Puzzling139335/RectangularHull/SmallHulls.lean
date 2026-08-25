import StackExchange.Puzzling139335.RectangularHull.AxisBox
import StackExchange.Puzzling139335.RectangularHull.Congruence
import StackExchange.Puzzling139335.RectangularHull.Bands

/-!
# Rectangular hulls with both edge lengths less than one

Four corners and four pieces first force every piece to own one corner.
The protected piece then forces both common edge lengths to exceed one
half. Actual rectangle vertices at the two bottom corners alternate,
contradicting the Jordan-region interlacing theorem.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem Frame.box_bounds_in_square (R : Frame) (hS : R.carrier ⊆ unitSquare) :
    0 ≤ R.boxLeft ∧ R.boxRight ≤ 1 ∧ 0 ≤ R.boxBottom ∧ R.boxTop ≤ 1 := by
  have ho := hS (R.vertices_subset_carrier R.origin_mem_vertices)
  have hd := hS (R.vertices_subset_carrier R.both_mem_vertices)
  exact ⟨le_min ho.1.1 hd.1.1, max_le ho.1.2 hd.1.2,
    le_min ho.2.1 hd.2.1, max_le ho.2.2 hd.2.2⟩

theorem small_box_corner_unique {l r b t : ℝ} (hw : r - l < 1) (hh : t - b < 1)
    {j k : Fin 4} (hj : corner j ∈ closedAxisBox l r b t)
    (hk : corner k ∈ closedAxisBox l r b t) : j = k := by
  fin_cases j <;> fin_cases k
  all_goals first | rfl | skip
  all_goals
    norm_num [closedAxisBox, corner, Fin.ext_iff] at hj hk
    rcases hj with ⟨⟨hj0, hj1⟩, ⟨hj2, hj3⟩⟩
    rcases hk with ⟨⟨hk0, hk1⟩, ⟨hk2, hk3⟩⟩
    exfalso
    linarith

theorem Frame.corner_unique_of_lengths_lt_one (R : Frame)
    (hS : R.carrier ⊆ unitSquare) (hf : ‖R.first‖ < 1) (hs : ‖R.second‖ < 1)
    {j k : Fin 4} (hj : corner j ∈ R.carrier) (hk : corner k ∈ R.carrier) : j = k := by
  have hAxis := R.axisAligned_of_corner_mem hS hj
  have hwidth : R.boxRight - R.boxLeft < 1 := by
    rcases R.axisBox_side_lengths hAxis with h | h <;> linarith [h.1]
  have hheight : R.boxTop - R.boxBottom < 1 := by
    rcases R.axisBox_side_lengths hAxis with h | h <;> linarith [h.2]
  rw [R.carrier_eq_closedAxisBox hAxis] at hj hk
  exact small_box_corner_unique hwidth hheight hj hk

theorem CommonFrames.carrier_subset_square {d : SquareDissection} (F : CommonFrames d)
    (i : Fin 4) : (F.frame i).carrier ⊆ unitSquare := by
  rw [← F.hull_eq i]
  exact convexHull_min (d.piece_subset i) convex_unitSquare

theorem CommonFrames.piece_subset_carrier {d : SquareDissection} (F : CommonFrames d)
    (i : Fin 4) : d.piece i ⊆ (F.frame i).carrier :=
  (F.frame i).subset_carrier_of_convexHull_eq (F.hull_eq i)

theorem CommonFrames.every_piece_cornered_of_small {d : SquareDissection}
    (F : CommonFrames d) (hf : ‖(F.frame 0).first‖ < 1)
    (hs : ‖(F.frame 0).second‖ < 1) :
    ∀ i : Fin 4, ∃ j : Fin 4, corner j ∈ d.piece i := by
  classical
  choose owner howner using fun j => d.exists_piece_mem (corner_mem_unitSquare j)
  have hinj : Function.Injective owner := by
    intro j k hjk
    apply (F.frame (owner j)).corner_unique_of_lengths_lt_one (F.carrier_subset_square _)
      (by simpa only [F.first_length_eq (owner j) 0] using hf)
      (by simpa only [F.second_length_eq (owner j) 0] using hs)
    · exact F.piece_subset_carrier _ (howner j)
    · exact F.piece_subset_carrier _ (hjk.symm ▸ howner k)
  have hsurj : Function.Surjective owner := Finite.surjective_of_injective hinj
  intro i
  obtain ⟨j, rfl⟩ := hsurj i
  exact ⟨j, howner j⟩

private theorem span_gt_half_of_corner_and_center {l r z : ℝ}
    (hz : z = 0 ∨ z = 1) (hmem : z ∈ Icc l r)
    (hl : l < 1 / 2) (hr : 1 / 2 < r) : 1 / 2 < r - l := by
  rcases hz with rfl | rfl
  · linarith [hmem.1]
  · linarith [hmem.2]

theorem Frame.lengths_gt_half_of_corner_and_center (R : Frame)
    (hS : R.carrier ⊆ unitSquare) {j : Fin 4} (hj : corner j ∈ R.carrier)
    (hcenter : squareCenter ∈ interior R.carrier) :
    1 / 2 < ‖R.first‖ ∧ 1 / 2 < ‖R.second‖ := by
  have hAxis := R.axisAligned_of_corner_mem hS hj
  have hc := (R.mem_interior_carrier_iff hAxis).mp hcenter
  rw [R.carrier_eq_closedAxisBox hAxis] at hj
  have hx : corner j 0 = 0 ∨ corner j 0 = 1 := by
    by_cases h : j = 1 ∨ j = 2 <;> simp [corner, h]
  have hy : corner j 1 = 0 ∨ corner j 1 = 1 := by
    by_cases h : j = 2 ∨ j = 3 <;> simp [corner, h]
  have hw := span_gt_half_of_corner_and_center hx hj.1 hc.1 hc.2.1
  have hh := span_gt_half_of_corner_and_center hy hj.2 hc.2.2.1 hc.2.2.2
  rcases R.axisBox_side_lengths hAxis with h | h <;> constructor <;> linarith [h.1, h.2]

/-- The complete small-rectangle-hull obstruction, for the actual four
Jordan pieces and their actual common congruence frames. -/
theorem CommonFrames.no_protectedCenter_of_small {d : SquareDissection}
    (F : CommonFrames d) (hf : ‖(F.frame 0).first‖ < 1)
    (hs : ‖(F.frame 0).second‖ < 1) : ¬ d.HasProtectedCenter := by
  rintro ⟨k, hk⟩
  obtain ⟨q, hq⟩ := F.every_piece_cornered_of_small hf hs k
  have hlong := (F.frame k).lengths_gt_half_of_corner_and_center
    (F.carrier_subset_square k) (F.piece_subset_carrier k hq)
    (interior_mono (F.piece_subset_carrier k) hk)
  have hlengths (i : Fin 4) :
      1 / 2 < ‖(F.frame i).first‖ ∧ 1 / 2 < ‖(F.frame i).second‖ := by
    simpa only [F.first_length_eq i k, F.second_length_eq i k] using hlong
  have hsmall (i : Fin 4) : ‖(F.frame i).first‖ < 1 ∧ ‖(F.frame i).second‖ < 1 := by
    simpa only [F.first_length_eq i 0, F.second_length_eq i 0] using And.intro hf hs
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare 0)
  obtain ⟨j, hj⟩ := d.exists_piece_mem (corner_mem_unitSquare 1)
  have hij : i ≠ j := by
    intro h
    have heq := (F.frame i).corner_unique_of_lengths_lt_one
      (F.carrier_subset_square i) (hsmall i).1 (hsmall i).2
      (F.piece_subset_carrier i hi) (F.piece_subset_carrier i (h.symm ▸ hj))
    norm_num at heq
  have hiAxis := (F.frame i).axisAligned_of_piece_corner (F.hull_eq i) (d.piece_subset i) hi
  have hjAxis := (F.frame j).axisAligned_of_piece_corner (F.hull_eq j) (d.piece_subset j) hj
  have hiBox := F.piece_subset_carrier i hi
  have hjBox := F.piece_subset_carrier j hj
  rw [(F.frame i).carrier_eq_closedAxisBox hiAxis] at hiBox
  rw [(F.frame j).carrier_eq_closedAxisBox hjAxis] at hjBox
  have hib := (F.frame i).box_bounds_in_square (F.carrier_subset_square i)
  have hjb := (F.frame j).box_bounds_in_square (F.carrier_subset_square j)
  have hil : (F.frame i).boxLeft = 0 := by
    have : (F.frame i).boxLeft ≤ 0 := hiBox.1.1
    linarith [hib.1]
  have hiy : (F.frame i).boxBottom = 0 := by
    have : (F.frame i).boxBottom ≤ 0 := hiBox.2.1
    linarith [hib.2.2.1]
  have hjr : (F.frame j).boxRight = 1 := by
    have : 1 ≤ (F.frame j).boxRight := hjBox.1.2
    linarith [hjb.2.1]
  have hjy : (F.frame j).boxBottom = 0 := by
    have : (F.frame j).boxBottom ≤ 0 := hjBox.2.1
    linarith [hjb.2.2.1]
  have hir : (1 / 2 : ℝ) < (F.frame i).boxRight ∧ (F.frame i).boxRight < 1 := by
    rcases (F.frame i).axisBox_side_lengths hiAxis with h | h
    all_goals constructor <;> linarith [h.1, (hlengths i).1, (hlengths i).2,
      (hsmall i).1, (hsmall i).2]
  have hjl : 0 < (F.frame j).boxLeft ∧ (F.frame j).boxLeft < 1 / 2 := by
    rcases (F.frame j).axisBox_side_lengths hjAxis with h | h
    all_goals constructor <;> linarith [h.1, (hlengths j).1, (hlengths j).2,
      (hsmall j).1, (hsmall j).2]
  have hiPoint : Schoenflies.Plane.mk (F.frame i).boxRight 0 ∈ d.piece i := by
    have hv := (F.frame i).axisBoxVertices_subset_of_convexHull_eq hiAxis (F.hull_eq i)
    apply hv
    simp [axisBoxVertices, Schoenflies.Plane.mk, hiy]
  have hjPoint : Schoenflies.Plane.mk (F.frame j).boxLeft 0 ∈ d.piece j := by
    have hv := (F.frame j).axisBoxVertices_subset_of_convexHull_eq hjAxis (F.hull_eq j)
    apply hv
    simp [axisBoxVertices, Schoenflies.Plane.mk, hjy]
  have horder := bottom_corner_contact_order d hij hjl.1 hir.2
    (by simpa [corner, Schoenflies.Plane.mk] using hi) hiPoint hjPoint
    (by simpa [corner, Schoenflies.Plane.mk] using hj)
  linarith [hir.1, hjl.2]

end Puzzling139335.RectangularHull
