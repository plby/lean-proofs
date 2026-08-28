import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalBoundaryFrame
import Wikipedia.NoExoticSixSphere.RoundedTraceInducedBoundaryFrame
import Wikipedia.NoExoticSixSphere.OrthogonalUnitRescaling

/-!
# Full actual endpoint normal spaces and their ordered coordinates

The frame's old columns come first and the outward column comes last. The
fixed coordinate identification is an isometry. The sheared endpoint frame
is a nonzero last-column rescaling, so it spans the full actual normal space.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryFrameCoordinates : TimeGraphFrameSpace (e := e) ≃ₗᵢ[ℝ]
    Vector (((e.ambientDimension - 6) + 5) + 1) :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (Vector ((e.ambientDimension - 6) + 5)))
    EuclideanTailCoordinates.scalar).trans
      (EuclideanTailCoordinates.finAdd ((e.ambientDimension - 6) + 5) 1).symm

theorem boundaryFrameCoordinates_apply (v : TimeGraphFrameSpace (e := e)) :
    boundaryFrameCoordinates (e := e) v =
      EuclideanSpace.finAddEquivProd.symm (v.fst, EuclideanTailCoordinates.scalar v.snd) := rfl

theorem boundaryAppendedFrame_eq (p : Boundary A) :
    OrthogonalUnitExtension.operator (traceNormalFrame A p.val) (outwardNormal A p) =
      (inducedBoundaryFrame A p).comp
        (boundaryFrameCoordinates (e := e)).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change OrthogonalUnitExtension.operator (traceNormalFrame A p.val) (outwardNormal A p) v =
    inducedBoundaryFrame A p (boundaryFrameCoordinates (e := e) v)
  rw [OrthogonalUnitExtension.operator_apply, inducedBoundaryFrame_apply,
    boundaryFrameCoordinates_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem boundaryAppendedFrame_range (p : Boundary A) :
    (OrthogonalUnitExtension.operator (traceNormalFrame A p.val) (outwardNormal A p)).range =
      (boundaryAmbientDerivative A p).rangeᗮ := by
  rw [boundaryAppendedFrame_eq]
  have hr := LinearMap.range_comp_of_range_eq_top (inducedBoundaryFrame A p).toLinearMap
    (boundaryFrameCoordinates (e := e)).toLinearEquiv.range
  exact hr.trans (inducedBoundaryFrame_range A p)

theorem injective_boundaryAppendedFrame (p : Boundary A) :
    Injective
      (OrthogonalUnitExtension.operator (traceNormalFrame A p.val) (outwardNormal A p)) := by
  rw [boundaryAppendedFrame_eq]
  exact (Stiefel.injective ⟨inducedBoundaryFrame A p, inducedBoundaryFrame_norm A p⟩).comp
    (boundaryFrameCoordinates (e := e)).injective

theorem boundaryVerticalFrame_eq_operator (p : Boundary A) :
    boundaryVerticalFrame A p = OrthogonalUnitExtension.operator (traceNormalFrame A p.val)
      (boundaryVerticalScale A p • outwardNormal A p) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [boundaryVerticalFrame_apply, OrthogonalUnitExtension.operator_apply, smul_smul]

theorem boundaryVerticalFrame_range (p : Boundary A) :
    (boundaryVerticalFrame A p).range = (boundaryAmbientDerivative A p).rangeᗮ := by
  rw [boundaryVerticalFrame_eq_operator,
    OrthogonalUnitExtension.range_operator_smul _ _ (boundaryVerticalScale_ne_zero A p),
    boundaryAppendedFrame_range]

theorem injective_boundaryVerticalFrame (p : Boundary A) :
    Injective (boundaryVerticalFrame A p) := by
  intro u v he
  apply injective_verticalFrame A p.val
  apply (timeGraphCoordinates (e := e)).injective
  apply Prod.ext
  · change timeGraphTimeFunctional (e := e) (verticalFrame A p.val u) =
      timeGraphTimeFunctional (e := e) (verticalFrame A p.val v)
    rw [verticalFrame_time_zero_boundary, verticalFrame_time_zero_boundary]
  · exact he

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
