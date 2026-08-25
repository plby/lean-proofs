import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local boundary germs and straight initial segments

The definitions use equality on a genuine neighborhood and actual straight
segments.  They impose no regularity on the rest of the boundary.
-/

open Set Metric

namespace Puzzling139335

/-- Two subsets have the same local germ at a point if they agree in some
positive-radius ball centered there. -/
def SameBoundaryGerm (A B : Set Plane) (v : Plane) : Prop :=
  ∃ r > 0, ball v r ∩ A = ball v r ∩ B

/-- A set has a straight initial branch at `v` if it contains a nondegenerate
straight segment starting at `v`.  For an endpoint of a Jordan arc this is a
property of the local branch, not of its chosen far endpoint. -/
def IsStraightAt (A : Set Plane) (v : Plane) : Prop :=
  ∃ w : Plane, w ≠ v ∧ segment ℝ v w ⊆ A

namespace SameBoundaryGerm

theorem refl (A : Set Plane) (v : Plane) : SameBoundaryGerm A A v :=
  ⟨1, zero_lt_one, rfl⟩

theorem symm {A B : Set Plane} {v : Plane} (h : SameBoundaryGerm A B v) :
    SameBoundaryGerm B A v := by
  obtain ⟨r, hr, heq⟩ := h
  exact ⟨r, hr, heq.symm⟩

theorem trans {A B C : Set Plane} {v : Plane}
    (hAB : SameBoundaryGerm A B v) (hBC : SameBoundaryGerm B C v) :
    SameBoundaryGerm A C v := by
  obtain ⟨r, hr, hAB⟩ := hAB
  obtain ⟨s, hs, hBC⟩ := hBC
  refine ⟨min r s, lt_min hr hs, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hA⟩
    have hxB := (Set.ext_iff.mp hAB x).mp ⟨(ball_subset_ball (min_le_left r s)) hx, hA⟩
    exact ⟨hx, ((Set.ext_iff.mp hBC x).mp
      ⟨(ball_subset_ball (min_le_right r s)) hx, hxB.2⟩).2⟩
  · rintro ⟨hx, hC⟩
    have hxB := (Set.ext_iff.mp hBC x).mpr
      ⟨(ball_subset_ball (min_le_right r s)) hx, hC⟩
    exact ⟨hx, ((Set.ext_iff.mp hAB x).mpr
      ⟨(ball_subset_ball (min_le_left r s)) hx, hxB.2⟩).2⟩

theorem image_affineIsometry {A B : Set Plane} {v : Plane}
    (h : SameBoundaryGerm A B v) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    SameBoundaryGerm (e '' A) (e '' B) (e v) := by
  obtain ⟨r, hr, heq⟩ := h
  refine ⟨r, hr, ?_⟩
  have hball : e '' ball v r = ball (e v) r := e.toIsometryEquiv.image_ball v r
  rw [← hball, ← Set.image_inter e.injective, ← Set.image_inter e.injective, heq]

end SameBoundaryGerm

/-- Every nondegenerate straight segment has a shorter nondegenerate initial
segment contained in any prescribed neighborhood of its initial endpoint. -/
theorem exists_initial_segment_subset_ball {v w : Plane} (hw : w ≠ v)
    {r : ℝ} (hr : 0 < r) :
    ∃ z : Plane, z ≠ v ∧ segment ℝ v z ⊆ segment ℝ v w ∩ ball v r := by
  have hvcl : v ∈ closure (openSegment ℝ v w) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ v w)
  obtain ⟨z, hzball, hzopen⟩ :=
    mem_closure_iff.mp hvcl (ball v r) isOpen_ball (mem_ball_self hr)
  have hzv : z ≠ v := by
    intro h
    subst z
    exact hw (left_mem_openSegment_iff.mp hzopen).symm
  refine ⟨z, hzv, ?_⟩
  exact subset_inter
    ((convex_segment v w).segment_subset (left_mem_segment ℝ v w)
      (openSegment_subset_segment ℝ v w hzopen))
    ((convex_ball v r).segment_subset (mem_ball_self hr) hzball)

namespace IsStraightAt

theorem mono {A B : Set Plane} {v : Plane} (h : IsStraightAt A v) (hAB : A ⊆ B) :
    IsStraightAt B v := by
  obtain ⟨w, hw, hseg⟩ := h
  exact ⟨w, hw, hseg.trans hAB⟩

theorem mem {A : Set Plane} {v : Plane} (h : IsStraightAt A v) : v ∈ A := by
  obtain ⟨w, _, hseg⟩ := h
  exact hseg (left_mem_segment ℝ v w)

theorem image_affineIsometry {A : Set Plane} {v : Plane}
    (h : IsStraightAt A v) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    IsStraightAt (e '' A) (e v) := by
  obtain ⟨w, hw, hseg⟩ := h
  refine ⟨e w, fun heq => hw (e.injective heq), ?_⟩
  have himage : e '' segment ℝ v w = segment ℝ (e v) (e w) :=
    image_segment ℝ e.toAffineMap v w
  rw [← himage]
  exact image_mono hseg

theorem of_sameBoundaryGerm {A B : Set Plane} {v : Plane}
    (h : IsStraightAt A v) (hAB : SameBoundaryGerm A B v) : IsStraightAt B v := by
  obtain ⟨w, hw, hseg⟩ := h
  obtain ⟨r, hr, heq⟩ := hAB
  obtain ⟨z, hz, hzseg⟩ := exists_initial_segment_subset_ball hw hr
  refine ⟨z, hz, ?_⟩
  intro x hx
  have hxy := hzseg hx
  exact ((Set.ext_iff.mp heq x).mp ⟨hxy.2, hseg hxy.1⟩).2

end IsStraightAt

theorem SameBoundaryGerm.isStraightAt_iff {A B : Set Plane} {v : Plane}
    (h : SameBoundaryGerm A B v) : IsStraightAt A v ↔ IsStraightAt B v :=
  ⟨fun hA => hA.of_sameBoundaryGerm h, fun hB => hB.of_sameBoundaryGerm h.symm⟩

theorem isStraightAt_image_affineIsometry_iff (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (A : Set Plane) (v : Plane) : IsStraightAt (e '' A) (e v) ↔ IsStraightAt A v := by
  constructor
  · intro h
    have h' := h.image_affineIsometry e.symm
    simpa only [image_image, e.symm_apply_apply, Function.comp_def, image_id'] using h'
  · exact fun h => h.image_affineIsometry e

end Puzzling139335
