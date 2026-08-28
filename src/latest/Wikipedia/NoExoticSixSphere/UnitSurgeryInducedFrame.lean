import Wikipedia.NoExoticSixSphere.UnitSurgeryInducedEmbedding

/-!
# The actual full normal frame on canonical surgery

Pull back the induced boundary frame through the proved comparison. The
result is smooth in the existing canonical surgery atlas and spans the
normal space of its actual Euclidean embedding. Both end restrictions of
the full boundary diffeomorphism are recorded exactly.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedTrace StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def inducedNormalFrame (p : Target A hR) :
    Vector (((e.ambientDimension - 6) + 5) + 1) →L[ℝ] Vector (e.ambientDimension + 6) :=
  inducedBoundaryFrame A (boundaryPoint A hR p)

theorem inducedNormalFrame_norm (p : Target A hR)
    (w : Vector (((e.ambientDimension - 6) + 5) + 1)) :
    ‖inducedNormalFrame A hR p w‖ = ‖w‖ :=
  inducedBoundaryFrame_norm A (boundaryPoint A hR p) w

theorem contMDiff_inducedNormalFrame : letI := targetChartedSpace A hR;
    ContMDiff (𝓡 6)
      𝓘(ℝ, Vector (((e.ambientDimension - 6) + 5) + 1) →L[ℝ]
        Vector (e.ambientDimension + 6)) ∞ (inducedNormalFrame A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact (contMDiff_inducedBoundaryFrame A).comp (contMDiff_boundaryPoint A hR)

theorem inducedNormalFrame_range (p : Target A hR) :
    (inducedNormalFrame A hR p).range = (ambientDerivative A hR p).rangeᗮ := by
  rw [range_ambientDerivative]
  exact inducedBoundaryFrame_range A (boundaryPoint A hR p)

theorem inducedEmbedding_normalProjection (p : Target A hR) :
    letI := targetChartedSpace A hR;
    (inducedEmbedding A hR).normalProjection p =
      boundaryNormalProjection A (boundaryPoint A hR p) := by
  let := targetChartedSpace A hR
  change (ambientDerivative A hR p).rangeᗮ.starProjection =
    (boundaryAmbientDerivative A (boundaryPoint A hR p)).rangeᗮ.starProjection
  simp only [range_ambientDerivative]

theorem inducedNormalFrame_range_projection (p : Target A hR) :
    letI := targetChartedSpace A hR;
    (inducedNormalFrame A hR p).range = ((inducedEmbedding A hR).normalProjection p).range := by
  let := targetChartedSpace A hR
  rw [(inducedEmbedding A hR).range_normalProjection]
  exact inducedNormalFrame_range A hR p

def inducedRangeFrame : letI := targetChartedSpace A hR;
    SmoothRangeFrame (𝓡 6) (inducedEmbedding A hR).normalProjection
      (Vector (((e.ambientDimension - 6) + 5) + 1)) := by
  let := targetChartedSpace A hR
  let P := (inducedEmbedding A hR).normalProjection
  let q (p : Target A hR) :
      Vector (((e.ambientDimension - 6) + 5) + 1) ≃L[ℝ] (P p).range :=
    (LinearEquiv.ofInjective (inducedNormalFrame A hR p).toLinearMap
      (Stiefel.injective
        ⟨inducedNormalFrame A hR p, inducedNormalFrame_norm A hR p⟩)).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (inducedNormalFrame_range_projection A hR p))
  refine ⟨q, ?_⟩
  have he : (fun p : Target A hR ↦ (P p).range.subtypeL.comp
      (q p).toContinuousLinearMap) = inducedNormalFrame A hR := by
    funext p
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [he]
  exact contMDiff_inducedNormalFrame A hR

theorem inducedRangeFrame_ambient (p : Target A hR) : letI := targetChartedSpace A hR;
    (inducedRangeFrame A hR).ambient p = inducedNormalFrame A hR p := by
  let := targetChartedSpace A hR
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem traceBoundaryDiffeomorph_frame_inl (m : M) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    inducedBoundaryFrame A (traceBoundaryDiffeomorph A hR (Sum.inl m)) =
      (BlockSum.operator 6 (a.orthonormal m).val).comp
        (endColumnPermutation (e.ambientDimension - 6)).toContinuousLinearMap :=
  inducedBoundaryFrame_original_stabilization A m

theorem traceBoundaryDiffeomorph_frame_inr (p : Target A hR) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    inducedBoundaryFrame A (traceBoundaryDiffeomorph A hR (Sum.inr p)) =
      inducedNormalFrame A hR p := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
