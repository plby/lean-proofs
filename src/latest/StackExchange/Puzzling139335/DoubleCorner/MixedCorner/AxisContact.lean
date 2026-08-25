import StackExchange.Puzzling139335.DoubleCorner.RotationBoundary
import StackExchange.Puzzling139335.DoubleCorner.Triod
import StackExchange.Puzzling139335.DoubleCorner.MixedCorner.SmallArc

/-!
# Outer-axis contact at a corner shared by two Jordan pieces

If the first piece misses both outer axes away from the corner, the second
piece contains short segments of both axes.  A small actual frontier arc
of the first piece then lies inside the square and is also a branch of the
second piece.  These three branches contradict the Jordan property.  The
Jordan curve itself supplies the small arc, without a straightness assumption.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner.MixedCorner

noncomputable section

open PlaneIsometries

private theorem bottom_segment_properties {x : Plane}
    (hx : x ∈ segment ℝ 0 (!₂[1, 0] : Plane)) :
    x ∈ unitSquare ∧ x 1 = 0 := by
  rcases hx with ⟨a, b, ha, hb, hab, rfl⟩
  have hb1 : b ≤ 1 := by linarith
  simp [unitSquare, hb, hb1]

private theorem left_segment_properties {x : Plane}
    (hx : x ∈ segment ℝ 0 (!₂[0, 1] : Plane)) :
    x ∈ unitSquare ∧ x 0 = 0 := by
  rcases hx with ⟨a, b, ha, hb, hab, rfl⟩
  have hb1 : b ≤ 1 := by linarith
  simp [unitSquare, hb, hb1]

private theorem axis_segment_subset_frontier_other
    {P Q : Set Plane} (hQclosed : IsClosed Q) (hQsub : Q ⊆ unitSquare)
    (hnoaxis : ∀ x ∈ P, x ≠ 0 → x 0 ≠ 0 ∧ x 1 ≠ 0)
    {ε : ℝ} (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q)
    {a : Plane} (ha : a ≠ 0)
    (hball : segment ℝ 0 a ⊆ ball 0 ε)
    (hsub : segment ℝ 0 a ⊆ unitSquare)
    (haxis : ∀ x ∈ segment ℝ 0 a, x 0 = 0 ∨ x 1 = 0) :
    segment ℝ 0 a ⊆ frontier Q := by
  have hOpenQ : openSegment ℝ 0 a ⊆ Q := by
    intro x hx
    have hxseg : x ∈ segment ℝ 0 a := openSegment_subset_segment ℝ 0 a hx
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      exact ha (left_mem_openSegment_iff.mp hx).symm
    rcases hcover ⟨hball hxseg, hsub hxseg⟩ with hxP | hxQ
    · obtain ⟨hne0, hne1⟩ := hnoaxis x hxP hxne
      exact False.elim ((haxis x hxseg).elim hne0 hne1)
    · exact hxQ
  have hsegQ : segment ℝ 0 a ⊆ Q :=
    segment_subset_closure_openSegment.trans (closure_minimal hOpenQ hQclosed)
  intro x hx
  rw [hQclosed.frontier_eq]
  refine ⟨hsegQ hx, ?_⟩
  intro hxint
  have hxcoords := SquareSymmetry.interior_unitSquare_coordinates (interior_mono hQsub hxint)
  rcases haxis x hx with hx0 | hx1
  · exact (ne_of_gt hxcoords.1.1) hx0
  · exact (ne_of_gt hxcoords.2.1) hx1

/-- Any sufficiently short actual frontier arc at a corner shared by two
Jordan pieces forces contact with one outer axis. -/
theorem exists_axis_contact_of_small_frontier_arc
    {P Q A : Set Plane} {v : Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q)
    (hbranch : Schoenflies.IsArcBetween A 0 v)
    (hbranchFront : A ⊆ frontier P) (hbranchBall : A ⊆ ball 0 (min ε 1)) :
    ∃ x ∈ P, x ≠ 0 ∧ (x 0 = 0 ∨ x 1 = 0) := by
  classical
  by_contra hnone
  have hnoaxis (x : Plane) (hx : x ∈ P) (hxne : x ≠ 0) :
      x 0 ≠ 0 ∧ x 1 ≠ 0 := by
    constructor
    · exact fun h => hnone ⟨x, hx, hxne, Or.inl h⟩
    · exact fun h => hnone ⟨x, hx, hxne, Or.inr h⟩
  have hbottom : (!₂[1, 0] : Plane) ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Plane => x 0) h
    norm_num at h0
  have hleft : (!₂[0, 1] : Plane) ≠ 0 := by
    intro h
    have h1 := congrArg (fun x : Plane => x 1) h
    norm_num at h1
  obtain ⟨a, ha, haSeg⟩ := exists_initial_segment_subset_ball hbottom hε
  obtain ⟨b, hb, hbSeg⟩ := exists_initial_segment_subset_ball hleft hε
  have haFront : segment ℝ 0 a ⊆ frontier Q := by
    apply axis_segment_subset_frontier_other hQ.isClosed hQsub hnoaxis hcover ha
    · exact fun x hx => (haSeg hx).2
    · exact fun x hx => (bottom_segment_properties (haSeg hx).1).1
    · exact fun x hx => Or.inr (bottom_segment_properties (haSeg hx).1).2
  have hbFront : segment ℝ 0 b ⊆ frontier Q := by
    apply axis_segment_subset_frontier_other hQ.isClosed hQsub hnoaxis hcover hb
    · exact fun x hx => (hbSeg hx).2
    · exact fun x hx => (left_segment_properties (hbSeg hx).1).1
    · exact fun x hx => Or.inl (left_segment_properties (hbSeg hx).1).2
  have hzeroQ : (0 : Plane) ∈ frontier Q := haFront (left_mem_segment ℝ 0 a)
  have hbranchP : A ⊆ P := by
    intro x hx
    exact hP.isClosed.closure_eq ▸ (hbranchFront hx).1
  have hcover' : ball (0 : Plane) ε ∩ unitSquare ⊆ Q ∪ P := by
    simpa only [union_comm] using hcover
  have hbranchFrontQ : A ⊆ frontier Q := by
    intro x hx
    by_cases hx0 : x = 0
    · exact hx0 ▸ hzeroQ
    have hxP := hbranchP hx
    have hxS := hPsub hxP
    have hxne := hnoaxis x hxP hx0
    have hxint : x ∈ interior unitSquare :=
      interior_unitSquare_of_pos_of_mem_ball_one
        (lt_of_le_of_ne hxS.1.1 hxne.1.symm)
        (lt_of_le_of_ne hxS.2.1 hxne.2.symm)
        (ball_subset_ball (min_le_right ε 1) (hbranchBall hx))
    exact frontier_switch_of_local_cover hQ.isClosed hP.isClosed
      (hP.disjoint_interior_left hdis.symm) hcover'
      (ball_subset_ball (min_le_left ε 1) (hbranchBall hx)) hxint (hbranchFront hx)
  apply hQ.frontier_isJordanCurve.no_three_endpoint_arcs
    (Schoenflies.isArcBetween_segment ha.symm) (Schoenflies.isArcBetween_segment hb.symm)
    hbranch haFront hbFront hbranchFrontQ
  · intro x hx
    apply mem_singleton_iff.mpr
    exact plane_ext (left_segment_properties (hbSeg hx.2).1).2
      (bottom_segment_properties (haSeg hx.1).1).2
  · intro x hx
    apply mem_singleton_iff.mpr
    by_contra hx0
    exact (hnoaxis x (hbranchP hx.2) hx0).2
      (bottom_segment_properties (haSeg hx.1).1).2
  · intro x hx
    apply mem_singleton_iff.mpr
    by_contra hx0
    exact (hnoaxis x (hbranchP hx.2) hx0).1
      (left_segment_properties (hbSeg hx.1).1).2

/-- At a corner covered locally by two Jordan pieces, an actual straight
boundary branch forces the first piece to contain a nonzero point of one
outer axis.  No polygonal or sector assumption occurs in this statement. -/
theorem exists_axis_contact_of_straight_frontier
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hstraight : IsStraightAt (frontier P) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    ∃ x ∈ P, x ≠ 0 ∧ (x 0 = 0 ∨ x 1 = 0) := by
  obtain ⟨w, hw, hwFront⟩ := hstraight
  obtain ⟨c, hc, hcSeg⟩ := exists_initial_segment_subset_ball hw (lt_min hε zero_lt_one)
  exact exists_axis_contact_of_small_frontier_arc hP hQ hPsub hQsub hdis hε hcover
    (Schoenflies.isArcBetween_segment hc.symm)
    (fun x hx => hwFront (hcSeg hx).1) (fun x hx => (hcSeg hx).2)

/-- Every Jordan piece incident at a corner covered locally by two Jordan
pieces has an actual nonzero contact with an outer axis.  The small frontier
arc is supplied by the Jordan property, so no straightness is required. -/
theorem exists_axis_contact_of_mem_zero
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) (hzero : (0 : Plane) ∈ P)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    ∃ x ∈ P, x ≠ 0 ∧ (x 0 = 0 ∨ x 1 = 0) := by
  have hzeroFront : (0 : Plane) ∈ frontier P := by
    rw [hP.isClosed.frontier_eq]
    refine ⟨hzero, ?_⟩
    intro hzeroInt
    have hcoords := SquareSymmetry.interior_unitSquare_coordinates
      (interior_mono hPsub hzeroInt)
    have hbad : (0 : ℝ) < 0 := by simpa using hcoords.1.1
    exact (lt_irrefl 0) hbad
  obtain ⟨v, A, hA, hAsub⟩ :=
    hP.frontier_isJordanCurve.exists_small_arc hzeroFront (lt_min hε zero_lt_one)
  exact exists_axis_contact_of_small_frontier_arc hP hQ hPsub hQsub hdis hε hcover
    hA (fun x hx => (hAsub hx).1) (fun x hx => (hAsub hx).2)

end

end Puzzling139335.DoubleCorner.MixedCorner
