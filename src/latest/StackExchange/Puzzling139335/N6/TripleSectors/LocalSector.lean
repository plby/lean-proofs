import StackExchange.Puzzling139335.N6.TripleSectors.LocalSector.Topology
import StackExchange.Puzzling139335.N6.TripleSectors.LocalSector.Coordinates
import StackExchange.Puzzling139335.BoundaryGerm
import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.StraightBranchCount.TwoRays

/-!
# Actual two-ray germs fill the intervening sector

For a Jordan region contained in the square's corner quadrant, a frontier
germ made of two distinct straight rays has precisely the smaller intervening
sector as its local interior.  The sector conclusion is proved from the
actual boundary germ and quadrant containment.
-/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.LocalSector

noncomputable section

/-- The strictly positive sector between the ordered rays through `a` and `b`.
The order is intended to satisfy `0 < det a b`. -/
def openSector (a b : Plane) : Set Plane :=
  {x | 0 < det a x ∧ 0 < det x b}

/-- An oriented pair of actual first-quadrant boundary rays fills the sector
between them near its vertex. -/
theorem interior_eq_openSector_of_two_rays
    {P : Set Plane} (hP : IsJordanRegion P)
    (hquadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1)
    {a b : Plane} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hb0 : 0 ≤ b 0) (hb1 : 0 ≤ b 1)
    (hdet : 0 < det a b)
    (hgerm : SameBoundaryGerm (frontier P)
      (segment ℝ 0 a ∪ segment ℝ 0 b) 0) :
    ∃ r > 0, ball (0 : Plane) r ∩ interior P = ball (0 : Plane) r ∩ openSector a b := by
  obtain ⟨r, hr, heq⟩ := hgerm
  have hzfront : (0 : Plane) ∈ frontier P := by
    have hz : (0 : Plane) ∈ ball (0 : Plane) r ∩
        (segment ℝ 0 a ∪ segment ℝ 0 b) :=
      ⟨mem_ball_self hr, Or.inl (left_mem_segment ℝ 0 a)⟩
    exact ((Set.ext_iff.mp heq 0).mpr hz).2
  have hzP : (0 : Plane) ∈ P := by
    have hz := frontier_subset_closure hzfront
    rwa [hP.isClosed.closure_eq] at hz
  have hzero : (0 : Plane) ∈ closure (interior P) := by
    rwa [hP.closure_interior]
  have hfront : ∀ x ∈ ball (0 : Plane) r, x ∈ frontier P →
      0 ≤ leftForm a x ∧ 0 ≤ rightForm b x ∧
        (leftForm a x = 0 ∨ rightForm b x = 0) := by
    intro x hx hxf
    have hxseg := ((Set.ext_iff.mp heq x).mp ⟨hx, hxf⟩).2
    exact forms_of_mem_segment_union hdet.le hxseg
  obtain ⟨hfneg, hgneg, hellneg⟩ := negative_direction hdet ha hb ha0 ha1 hb0 hb1
  have hout : ∀ t : ℝ, 0 < t → t • (-a - b) ∉ P := by
    intro t ht htP
    have hcoords := hquadrant (t • (-a - b)) htP
    have hnonneg : 0 ≤ coordSum (t • (-a - b)) := by
      rw [coordSum_apply]
      exact add_nonneg hcoords.1 hcoords.2
    have hneg : coordSum (t • (-a - b)) < 0 := by
      rw [map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg ht hellneg
    exact (not_lt_of_ge hnonneg) hneg
  refine ⟨r, hr, ?_⟩
  simpa only [openSector, leftForm_apply, rightForm_apply] using
    interior_eq_positive_sector_of_local_frontier (leftForm a) (rightForm b)
      (leftForm_surjective hdet.ne') (rightForm_surjective hdet.ne')
      hzero hr hfront hfneg hgneg hout

/-- Distinct nonzero first-quadrant boundary branches admit a unique angular
ordering, and the local interior is their open sector in that order. -/
theorem local_openSector_of_two_rays
    {P : Set Plane} (hP : IsJordanRegion P)
    (hquadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1)
    {a b : Plane} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hb0 : 0 ≤ b 0) (hb1 : 0 ≤ b 1)
    (hinter : segment ℝ 0 a ∩ segment ℝ 0 b = {0})
    (hgerm : SameBoundaryGerm (frontier P)
      (segment ℝ 0 a ∪ segment ℝ 0 b) 0) :
    (0 < det a b ∧ ∃ r > 0,
      ball (0 : Plane) r ∩ interior P = ball (0 : Plane) r ∩ openSector a b) ∨
    (0 < det b a ∧ ∃ r > 0,
      ball (0 : Plane) r ∩ interior P = ball (0 : Plane) r ∩ openSector b a) := by
  have hne := det_ne_zero_of_segments_inter_singleton ha hb ha0 ha1 hb0 hb1 hinter
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right
    have hreverse : 0 < det b a := by
      change 0 < SegmentCrossing.det b a
      rw [SegmentCrossing.det_swap]
      exact neg_pos.mpr hlt
    refine ⟨hreverse, ?_⟩
    apply interior_eq_openSector_of_two_rays hP hquadrant hb ha hb0 hb1 ha0 ha1 hreverse
    simpa only [union_comm] using hgerm
  · exact Or.inl ⟨hgt,
      interior_eq_openSector_of_two_rays hP hquadrant ha hb ha0 ha1 hb0 hb1 hgt hgerm⟩

/-- Two straight local branches of the actual Jordan boundary yield an
ordered pair of actual segments and a filled local sector. -/
theorem exists_local_openSector_of_straightBranchCount
    {P : Set Plane} (hP : IsJordanRegion P)
    (hquadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1)
    (hcount : HasStraightBranchCount (frontier P) 0 2) :
    ∃ a b : Plane, a ≠ 0 ∧ b ≠ 0 ∧
      (0 ≤ a 0 ∧ 0 ≤ a 1) ∧ (0 ≤ b 0 ∧ 0 ≤ b 1) ∧ 0 < det a b ∧
      segment ℝ 0 a ⊆ frontier P ∧ segment ℝ 0 b ⊆ frontier P ∧
      segment ℝ 0 a ∩ segment ℝ 0 b = {0} ∧
      SameBoundaryGerm (frontier P) (segment ℝ 0 a ∪ segment ℝ 0 b) 0 ∧
      ∃ r > 0, ball (0 : Plane) r ∩ interior P =
        ball (0 : Plane) r ∩ openSector a b := by
  obtain ⟨a, b, ha, hb, haSeg, hbSeg, hinter, hgerm⟩ := hcount.exists_two_segments
  have haP : a ∈ P := by
    have h := frontier_subset_closure (haSeg (right_mem_segment ℝ 0 a))
    rwa [hP.isClosed.closure_eq] at h
  have hbP : b ∈ P := by
    have h := frontier_subset_closure (hbSeg (right_mem_segment ℝ 0 b))
    rwa [hP.isClosed.closure_eq] at h
  have hacoord := hquadrant a haP
  have hbcoord := hquadrant b hbP
  rcases local_openSector_of_two_rays hP hquadrant ha hb hacoord.1 hacoord.2
      hbcoord.1 hbcoord.2 hinter hgerm with ⟨hdet, hsector⟩ | ⟨hdet, hsector⟩
  · exact ⟨a, b, ha, hb, hacoord, hbcoord, hdet, haSeg, hbSeg, hinter, hgerm, hsector⟩
  · refine ⟨b, a, hb, ha, hbcoord, hacoord, hdet, hbSeg, haSeg, ?_, ?_, hsector⟩
    · simpa only [inter_comm] using hinter
    · simpa only [union_comm] using hgerm

end

end Puzzling139335.N6.TripleSectors.LocalSector
