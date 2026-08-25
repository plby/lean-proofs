import StackExchange.Puzzling139335.SegmentCrossing.Collar
import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.JordanSubarc
import Wikipedia.SchoenfliesTheorem.Polygonal

/-! Actual straight subsegments of a Jordan boundary have local interior sides. -/

open Set

namespace Puzzling139335.SegmentCrossing

theorem linearForm_eq_on_segment (f : Plane →L[ℝ] ℝ) {A B y : Plane}
    (hAB : f A = f B) (hy : y ∈ segment ℝ A B) : f y = f A := by
  obtain ⟨a, b, _, _, hab, rfl⟩ := hy
  simp only [map_add, map_smul, smul_eq_mul]
  rw [← hAB, ← add_mul, hab, one_mul]

/-- An actual point on a nonconstant supporting level is a frontier point. -/
theorem mem_frontier_of_linear_support
    {P : Set Plane} {x : Plane} {c : ℝ} (f : Plane →L[ℝ] ℝ)
    (hf : Function.Surjective f) (hsupport : ∀ y ∈ P, f y ≤ c)
    (hx : x ∈ P) (hfx : f x = c) : x ∈ frontier P := by
  apply (mem_frontier_iff_notMem_interior hx).mpr
  intro hxi
  have hint := interior_mono (show P ⊆ f ⁻¹' Iic c from hsupport) hxi
  rw [f.interior_preimage hf, interior_Iic] at hint
  exact (ne_of_lt hint) hfx

/-- This explicitly requires the whole segment to belong to the region;
membership of its endpoints, or of a convex-hull chord, is insufficient. -/
theorem segment_subset_frontier_of_linear_support
    {P : Set Plane} {A B : Plane} {c : ℝ} (f : Plane →L[ℝ] ℝ)
    (hf : Function.Surjective f) (hsupport : ∀ y ∈ P, f y ≤ c)
    (hseg : segment ℝ A B ⊆ P) (hA : f A = c) (hB : f B = c) :
    segment ℝ A B ⊆ frontier P := by
  intro y hy
  exact mem_frontier_of_linear_support f hf hsupport (hseg hy)
    ((linearForm_eq_on_segment f (hA.trans hB.symm) hy).trans hA)

theorem mem_segment_sdiff_pair_of_mem_openSegment {A B x : Plane}
    (hAB : A ≠ B) (hx : x ∈ openSegment ℝ A B) :
    x ∈ segment ℝ A B \ {A, B} := by
  refine ⟨openSegment_subset_segment ℝ A B hx, ?_⟩
  intro hends
  simp only [mem_insert_iff, mem_singleton_iff] at hends
  rcases hends with rfl | rfl
  · exact hAB (left_mem_openSegment_iff.mp hx)
  · exact hAB (right_mem_openSegment_iff.mp hx)

/-- An actual nondegenerate segment of a Jordan frontier has an interior
half-ball on one of the two sides of its line at every interior point. -/
theorem jordan_segment_hasInteriorHalfBall_or_neg
    {P : Set Plane} {A B x : Plane} (hP : IsJordanRegion P)
    (hAB : A ≠ B) (hseg : segment ℝ A B ⊆ frontier P)
    (hx : x ∈ openSegment ℝ A B)
    (f : Plane →L[ℝ] ℝ) (hf : Function.Surjective f) (hfab : f A = f B) :
    HasInteriorHalfBall P x f ∨ HasInteriorHalfBall P x (-f) := by
  have hxseg := openSegment_subset_segment ℝ A B hx
  have hxP : x ∈ P := by
    have hxcl := frontier_subset_closure (hseg hxseg)
    rwa [hP.isClosed.closure_eq] at hxcl
  apply hasInteriorHalfBall_or_neg_of_local_frontier f hf
  · rwa [hP.closure_interior]
  · obtain ⟨r, hr, hball⟩ := hP.frontier_isJordanCurve.exists_ball_inter_subset_arc
      (Schoenflies.isArcBetween_segment hAB) hseg
      (mem_segment_sdiff_pair_of_mem_openSegment hAB hx)
    refine ⟨r, hr, ?_⟩
    intro y hyball hyP
    exact (linearForm_eq_on_segment f hfab (hball ⟨hyball, hyP⟩)).trans
      (linearForm_eq_on_segment f hfab hxseg).symm

end Puzzling139335.SegmentCrossing
