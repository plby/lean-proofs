import Wikipedia.NoExoticSixSphere.RectangularOrthonormalization
import Wikipedia.NoExoticSixSphere.ContinuousProjectionHomotopy
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Orthonormal trivialization of actual projection ranges on a closed disk

Continuous range transport along the disk contraction supplies a full frame.
Rectangular Gram--Schmidt makes it orthonormal without changing any range.
Only the rank at the center is specified; no trivialization is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ProjectionDisk

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {X : Type*} [TopologicalSpace X] {N n : ℕ}

theorem exists_frame_of_rangeFrame (P : X → Vector N →L[ℝ] Vector N)
    (a : ContinuousRangeFrame P (Vector n)) :
    ∃ t : C(X, Space N n), ∀ x, (t x).val.range = (P x).range := by
  let A : X → Vector n →L[ℝ] Vector N :=
    fun x ↦ (P x).range.subtypeL.comp (a.equiv x).toContinuousLinearMap
  have hi (x : X) : Function.Injective (A x) := by
    intro v w h
    apply (a.equiv x).injective
    exact Subtype.ext h
  have hr (x : X) : (A x).range = (P x).range := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact (a.equiv x v).property
    · intro hy
      obtain ⟨v, hv⟩ := (a.equiv x).surjective ⟨y, hy⟩
      exact ⟨v, congrArg Subtype.val hv⟩
  refine ⟨Orthonormalization.map A hi a.continuous, ?_⟩
  intro x
  exact (Orthonormalization.frame_range A hi x).trans (hr x)

def center : Disk (E := Vector 4) := ⟨0, by simp⟩

theorem exists_frame
    (P : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N))
    (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P center).range = n) :
    ∃ t : C(Disk (E := Vector 4), Space N n), ∀ x, (t x).val.range = (P x).range := by
  let H : unitInterval → Disk (E := Vector 4) → Vector N →L[ℝ] Vector N :=
    fun t x ↦ P (DiskBoundary.segment center (t, x))
  have hH (t : unitInterval) (x : Disk (E := Vector 4)) : IsIdempotentElem (H t x) :=
    hP (DiskBoundary.segment center (t, x))
  have hc : Continuous (fun z : unitInterval × Disk (E := Vector 4) ↦ H z.1 z.2) :=
    P.continuous.comp (DiskBoundary.segment center).continuous
  have hzero : H 0 = P := by
    funext x
    exact congrArg P (DiskBoundary.segment_zero center x)
  have hone : H 1 = fun _ ↦ P center := by
    funext x
    exact congrArg P (DiskBoundary.segment_one center x)
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector n) = Module.finrank ℝ (P center).range by
      rw [finrank_euclideanSpace_fin, hr])
  have hb : Nonempty (ContinuousRangeFrame P (Vector n)) := by
    simpa only [hzero] using
      nonempty_continuousRangeFrame_of_homotopy H hH hc 1 0 (P center) hone q
  obtain ⟨b⟩ := hb
  exact exists_frame_of_rangeFrame P b

end NoExoticSixSphere.Stiefel.ProjectionDisk
