import StackExchange.Puzzling139335.SegmentCrossing.Jordan

/-!
# Uniqueness along a segment on a common supporting line

If two Jordan regions lie on the same side of a line and have disjoint
interiors, an open segment of that line contained in one region cannot
meet the other region.
-/

open Set Metric

namespace Puzzling139335.N5

open SegmentCrossing

/-- A Jordan region in a closed half-space has strict-side interior points
arbitrarily close to each of its points. -/
theorem exists_interior_strict_support_in_ball
    {P : Set Plane} {x : Plane} {c r : ℝ} (hP : IsJordanRegion P)
    (f : Plane →L[ℝ] ℝ) (hf : Function.Surjective f)
    (hsupport : ∀ y ∈ P, c ≤ f y) (hx : x ∈ P) (hr : 0 < r) :
    ∃ y ∈ ball x r, c < f y ∧ y ∈ interior P := by
  have hxcl : x ∈ closure (interior P) := by
    rwa [hP.closure_interior]
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.mp hxcl r hr
  have hV : (ball x r ∩ interior P).Nonempty :=
    ⟨z, by simpa only [Metric.mem_ball, dist_comm] using hzx, hz⟩
  obtain ⟨y, hy, hne⟩ := exists_linear_ne_on_open f hf
    (isOpen_ball.inter isOpen_interior) hV c
  exact ⟨y, hy.1,
    lt_of_le_of_ne (hsupport y (interior_subset hy.2)) hne.symm, hy.2⟩

/-- The supporting half-space determines which local half-ball is interior
along a whole actual segment of a Jordan region. -/
theorem supporting_segment_hasInteriorHalfBall
    {P : Set Plane} {A B x : Plane} {c : ℝ} (hP : IsJordanRegion P)
    (f : Plane →L[ℝ] ℝ) (hf : Function.Surjective f)
    (hsupport : ∀ y ∈ P, c ≤ f y) (hAB : A ≠ B)
    (hseg : segment ℝ A B ⊆ P) (hA : f A = c) (hB : f B = c)
    (hx : x ∈ segment ℝ A B \ {A, B}) : HasInteriorHalfBall P x f := by
  have hneg : Function.Surjective (-f) := by
    intro t
    obtain ⟨y, hy⟩ := hf (-t)
    refine ⟨y, ?_⟩
    change -(f y) = t
    rw [hy, neg_neg]
  have hfront : segment ℝ A B ⊆ frontier P := by
    apply segment_subset_frontier_of_linear_support (-f) hneg (c := -c)
    · intro y hy
      change -(f y) ≤ -c
      exact neg_le_neg (hsupport y hy)
    · exact hseg
    · change -(f A) = -c
      rw [hA]
    · change -(f B) = -c
      rw [hB]
  have hfab : f A = f B := hA.trans hB.symm
  have hfx : f x = c := (linearForm_eq_on_segment f hfab hx.1).trans hA
  obtain ⟨r, hr, hball⟩ := hP.frontier_isJordanCurve.exists_ball_inter_subset_arc
    (Schoenflies.isArcBetween_segment hAB) hfront hx
  apply hasInteriorHalfBall_of_local_frontier_of_witness hr
  · intro y hyball hyfront
    exact (linearForm_eq_on_segment f hfab (hball ⟨hyball, hyfront⟩)).trans
      (linearForm_eq_on_segment f hfab hx.1).symm
  · obtain ⟨y, hyball, hyf, hyP⟩ :=
      exists_interior_strict_support_in_ball hP f hf hsupport (hseg hx.1) hr
    exact ⟨y, hyball, by rwa [hfx], hyP⟩

/-- Interior points of a full supporting segment cannot belong to another
Jordan region on the same side of its line with disjoint interior. -/
theorem segment_interior_not_mem_of_same_supporting_halfspace
    {P Q : Set Plane} {A B x : Plane} {c : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (f : Plane →L[ℝ] ℝ) (hf : Function.Surjective f)
    (hPside : ∀ y ∈ P, c ≤ f y) (hQside : ∀ y ∈ Q, c ≤ f y)
    (hdis : Disjoint (interior P) (interior Q))
    (hAB : A ≠ B) (hseg : segment ℝ A B ⊆ P) (hA : f A = c) (hB : f B = c)
    (hx : x ∈ segment ℝ A B \ {A, B}) : x ∉ Q := by
  intro hxQ
  obtain ⟨r, hr, hhalf⟩ :=
    supporting_segment_hasInteriorHalfBall hP f hf hPside hAB hseg hA hB hx
  obtain ⟨y, hyball, hyf, hyQ⟩ :=
    exists_interior_strict_support_in_ball hQ f hf hQside hxQ hr
  have hfx : f x = c :=
    (linearForm_eq_on_segment f (hA.trans hB.symm) hx.1).trans hA
  have hyP : y ∈ interior P := hhalf ⟨hyball, by rwa [hfx]⟩
  exact Set.disjoint_left.mp hdis hyP hyQ

/-- The `openSegment` formulation of supporting-side uniqueness. -/
theorem openSegment_not_mem_of_same_supporting_halfspace
    {P Q : Set Plane} {A B x : Plane} {c : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (f : Plane →L[ℝ] ℝ) (hf : Function.Surjective f)
    (hPside : ∀ y ∈ P, c ≤ f y) (hQside : ∀ y ∈ Q, c ≤ f y)
    (hdis : Disjoint (interior P) (interior Q))
    (hAB : A ≠ B) (hseg : segment ℝ A B ⊆ P) (hA : f A = c) (hB : f B = c)
    (hx : x ∈ openSegment ℝ A B) : x ∉ Q :=
  segment_interior_not_mem_of_same_supporting_halfspace hP hQ f hf hPside hQside
    hdis hAB hseg hA hB (mem_segment_sdiff_pair_of_mem_openSegment hAB hx)

end Puzzling139335.N5
