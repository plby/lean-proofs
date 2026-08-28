import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalEndEmbedding

/-!
# The actual signed normal framing of the original endpoint embedding

The frame and the change to the embedding's normal model are explicit.
The original-end reflection is retained in this frame, not discarded.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace.OriginalEnd

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def frame (m : M) : TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6) :=
  boundaryUnitFrame A (originalEndBoundaryMap A m)

theorem norm_frame (m : M) (v : TimeGraphFrameSpace (e := e)) : ‖frame A m v‖ = ‖v‖ :=
  norm_boundaryUnitFrame A (originalEndBoundaryMap A m) v

theorem frame_apply (m : M) (v : TimeGraphFrameSpace (e := e)) :
    frame A m v = BlockSum.operator 6 (a.orthonormal m).val
      (StabilizedSpanningDisk.endColumnPermutation (e.ambientDimension - 6)
        (boundaryFrameCoordinates (e := e) (boundaryLastReflection (e := e) v))) := by
  have h := originalEndFrameHomotopy_final A m v
  change boundaryFrameFamily A 1 (originalEndBoundaryMap A m) v = _ at h
  rw [boundaryFrameFamily_one] at h
  exact h

theorem contMDiff_frame :
    ContMDiff (𝓡 6) 𝓘(ℝ, TimeGraphFrameSpace (e := e) →L[ℝ]
      Vector (e.ambientDimension + 6)) ∞ (frame A) := by
  let := boundaryChartedSpace A
  exact (contMDiff_boundaryUnitFrame A).comp (contMDiff_boundaryMap A)

theorem frame_range_projection (m : M) :
    (frame A m).range = ((embedding A).normalProjection m).range := by
  rw [(embedding A).range_normalProjection]
  change (frame A m).range = (ambientDerivative A m).rangeᗮ
  rw [range_ambientDerivative]
  exact boundaryUnitFrame_range A (originalEndBoundaryMap A m)

def rangeFrame : SmoothRangeFrame (𝓡 6) (embedding A).normalProjection
    (TimeGraphFrameSpace (e := e)) := by
  let P := (embedding A).normalProjection
  let L (m : M) : TimeGraphFrameSpace (e := e) →ₗᵢ[ℝ] Vector (e.ambientDimension + 6) :=
    ⟨(frame A m).toLinearMap, norm_frame A m⟩
  let q (m : M) : TimeGraphFrameSpace (e := e) ≃L[ℝ] (P m).range :=
    (LinearEquiv.ofInjective (frame A m).toLinearMap (L m).injective).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.ofEq _ _ (frame_range_projection A m))
  refine ⟨q, ?_⟩
  have he : (fun m : M ↦ (P m).range.subtypeL.comp (q m).toContinuousLinearMap) = frame A := by
    funext m
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact contMDiff_frame A

theorem normalModel_dimension :
    (embedding A).ambientDimension - 6 = ((e.ambientDimension - 6) + 5) + 1 := by
  change (e.ambientDimension + 6) - 6 = ((e.ambientDimension - 6) + 5) + 1
  have hN := e.dimension_le_ambient (f (pole 3))
  omega

def normalModelCoordinates : (embedding A).NormalModel ≃ₗᵢ[ℝ] TimeGraphFrameSpace (e := e) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (normalModel_dimension A))).trans
    (boundaryFrameCoordinates (e := e)).symm

def normalFraming : SmoothRangeFrame (𝓡 6) (embedding A).normalProjection
    (embedding A).NormalModel := by
  refine {
    equiv := fun m ↦ (normalModelCoordinates A).toContinuousLinearEquiv.trans
      ((rangeFrame A).equiv m)
    smooth := ?_ }
  have he : (fun m : M ↦ ((embedding A).normalProjection m).range.subtypeL.comp
      (((normalModelCoordinates A).toContinuousLinearEquiv.trans
        ((rangeFrame A).equiv m)).toContinuousLinearMap)) =
      (fun m ↦ (frame A m).comp (normalModelCoordinates A).toContinuousLinearMap) := by
    funext m
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact (contMDiff_frame A).clm_comp contMDiff_const

theorem normalFraming_ambient (m : M) (v : (embedding A).NormalModel) :
    (normalFraming A).ambient m v = frame A m (normalModelCoordinates A v) := rfl

theorem normalFraming_norm (m : M) (v : (embedding A).NormalModel) :
    ‖(normalFraming A).ambient m v‖ = ‖v‖ := by
  rw [normalFraming_ambient]
  exact (norm_frame A m (normalModelCoordinates A v)).trans ((normalModelCoordinates A).norm_map v)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace.OriginalEnd
