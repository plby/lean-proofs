import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
import Wikipedia.SmoothSixDPoincare.FaceAttachmentCompact

/-!
# Cap an entire sphere component of a smooth-boundary body

The cap is the actual whole-disk attachment quotient. The remaining
boundary is the open complement of the specified sphere image, with its
original smooth atlas and its exact old-piece inclusion into the quotient.
No smooth structure on the interior of the body is assumed or needed.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace DiskCap

variable (N : Type*) [NormedAddCommGroup N]

def boundary : Set (MorseHandle.UnitDisk N) := {u | ‖u.val‖ = 1}

theorem isClosed_boundary : IsClosed (boundary N) :=
  isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const

def boundaryCoordinates : boundary N ≃ₜ PuncturedHandle.UnitSphere N where
  toFun u := ⟨u.val.val, mem_sphere_zero_iff_norm.mpr u.property⟩
  invFun u := ⟨⟨u.val, sphere_subset_closedBall u.property⟩, mem_sphere_zero_iff_norm.mp u.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end DiskCap

namespace SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U : SmoothBoundaryBody J)
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  (j : C(PuncturedHandle.UnitSphere N, U.boundary)) (hj : IsClosedEmbedding j)
  (hopen : IsOpen (range j))

def capBoundary : TopologicalSpace.Opens U.boundary :=
  ⟨(range j)ᶜ, hj.isClosed_range.isOpen_compl⟩

def capFaceMap : C(DiskCap.boundary N, U.body) :=
  U.inclusion.comp
    (j.comp ⟨DiskCap.boundaryCoordinates N, (DiskCap.boundaryCoordinates N).continuous⟩)

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
include hj in
theorem capFaceMap_injective : Injective (U.capFaceMap j) :=
  U.closedEmbedding.injective.comp (hj.injective.comp (DiskCap.boundaryCoordinates N).injective)

def capInclusion : C(U.capBoundary j hj, FaceAttachment.Space (U.capFaceMap j)) :=
  (FaceAttachment.oldMap (U.capFaceMap j)).comp
    (U.inclusion.comp ⟨Subtype.val, continuous_subtype_val⟩)

include hopen in
theorem capInclusion_isClosedEmbedding : IsClosedEmbedding (U.capInclusion j hj) :=
  (FaceAttachment.oldMap_isClosedEmbedding (U.capFaceMap j) (DiskCap.isClosed_boundary N)
    (U.capFaceMap_injective j hj)).comp
      (U.closedEmbedding.comp hopen.isClosed_compl.isClosedEmbedding_subtypeVal)

def cap : SmoothBoundaryBody J := by
  let _ : CompactSpace (U.capBoundary j hj) :=
    isCompact_iff_compactSpace.mp hopen.isClosed_compl.isCompact
  let _ : T2Space (FaceAttachment.Space (U.capFaceMap j)) :=
    FaceAttachment.t2Space (U.capFaceMap j) (DiskCap.isClosed_boundary N)
      (U.capFaceMap_injective j hj)
  exact ofEmbedding (U.capInclusion j hj) (U.capInclusion_isClosedEmbedding j hj hopen)

theorem cap_inclusion (x : U.capBoundary j hj) :
    (U.cap j hj hopen).inclusion x =
      FaceAttachment.oldMap (U.capFaceMap j) (U.inclusion x.val) := rfl

end SmoothBoundaryBody
end Wikipedia.SmoothSixDPoincare
