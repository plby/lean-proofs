import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyBoundary
import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceInterior
import Wikipedia.SmoothSixDPoincare.FaceAttachmentBoundaryUpdate

/-!
# The actual framed surgery boundary is the exact whole-body boundary update

The removed region is the image of the original open normal disk in the
old boundary. The added region is the entire original positive handle face.
This identifies the constructed boundary subset with the update used by the
literal whole-handle interchange.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

theorem faceInterior_eq_interiorImage : faceInterior A = A.interiorImage :=
  A.interiorImage_eq_chart.symm

variable [TopologicalSpace Y] (i : C(X, Y))

theorem bodyBoundarySet_eq_updateBoundary (hi : Injective i) :
    bodyBoundarySet A i = FaceAttachment.updateBoundary (bodyFaceMap A i)
      (range i) (i '' A.interiorImage) (range (wholeNewFace E F)) := by
  unfold bodyBoundarySet FaceAttachment.updateBoundary
  rw [range_sdiff_image hi, ← faceInterior_eq_interiorImage A]
  apply congrArg₂ (fun S T => S ∪ T)
  · ext z
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨i r.val, ⟨r.val, r.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  · ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨wholeNewFace E F p, ⟨p, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
theorem wholeNewFace_range : range (wholeNewFace E F) =
    {p : WholeHandle E F | ‖p.2.val‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact mem_sphere_zero_iff_norm.mp q.2.property
  · intro hp
    exact ⟨(p.1, ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hp⟩), rfl⟩

end Wikipedia.SmoothSixDPoincare.FramedSurgery
