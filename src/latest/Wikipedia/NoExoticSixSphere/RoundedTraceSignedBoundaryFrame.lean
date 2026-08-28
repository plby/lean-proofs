import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalBoundaryRange

/-!
# The signed unit frame at the two actual ends

The last column is outward at the surgery end and inward at the original
end. The old columns and their order remain fixed. The original-end sign
reversal is an explicit last-coordinate reflection.
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

def boundaryUnitScale (p : Boundary A) : ℝ :=
  letI := traceChartedSpace A
  1 - 2 * endCutoff A p.val

theorem contMDiff_boundaryUnitScale : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞ (boundaryUnitScale A) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact contMDiff_const.sub (contMDiff_const.mul
    ((endCutoff A).contMDiff.comp (contMDiff_boundaryInclusion A)))

theorem boundaryUnitScale_other (p : Boundary A) (hp : p.val ∈ otherEnd A) :
    boundaryUnitScale A p = 1 := by
  let := traceChartedSpace A
  rw [boundaryUnitScale, endCutoff_zero A hp]
  ring

theorem boundaryUnitScale_top (p : Boundary A) (hp : p.val ∈ topEnd A) :
    boundaryUnitScale A p = -1 := by
  let := traceChartedSpace A
  rw [boundaryUnitScale, endCutoff_one A hp]
  ring

theorem norm_boundaryUnitScale (p : Boundary A) : ‖boundaryUnitScale A p‖ = 1 := by
  rcases (boundary_iff_mem_ends A p.val).mp p.property with hp | hp
  · rw [boundaryUnitScale_other A p hp, norm_one]
  · rw [boundaryUnitScale_top A p hp, norm_neg, norm_one]

theorem boundaryUnitScale_ne_zero (p : Boundary A) : boundaryUnitScale A p ≠ 0 := by
  intro h
  have hn := norm_boundaryUnitScale A p
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

def boundaryUnitFrame (p : Boundary A) :
    TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6) :=
  OrthogonalUnitExtension.operator (traceNormalFrame A p.val)
    (boundaryUnitScale A p • outwardNormal A p)

theorem contMDiff_boundaryUnitFrame : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, TimeGraphFrameSpace (e := e) →L[ℝ]
      Vector (e.ambientDimension + 6)) ∞ (boundaryUnitFrame A) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact OrthogonalUnitExtension.contMDiff_operator
    ((contMDiff_traceNormalFrame A).comp (contMDiff_boundaryInclusion A))
    ((contMDiff_boundaryUnitScale A).smul (contMDiff_outwardNormal A))

theorem norm_boundaryUnitFrame (p : Boundary A) (v : TimeGraphFrameSpace (e := e)) :
    ‖boundaryUnitFrame A p v‖ = ‖v‖ := by
  apply OrthogonalUnitExtension.norm_operator _ (traceNormalFrame_norm A p.val)
  · rw [norm_smul, norm_boundaryUnitScale, norm_outwardNormal, mul_one]
  · intro w
    rw [real_inner_smul_left, outwardNormal_orthogonal_frame, mul_zero]

theorem boundaryUnitFrame_range (p : Boundary A) :
    (boundaryUnitFrame A p).range = (boundaryAmbientDerivative A p).rangeᗮ := by
  rw [boundaryUnitFrame,
    OrthogonalUnitExtension.range_operator_smul _ _ (boundaryUnitScale_ne_zero A p),
    boundaryAppendedFrame_range]

def boundaryLastReflection : TimeGraphFrameSpace (e := e) ≃ₗᵢ[ℝ] TimeGraphFrameSpace (e := e) :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (Vector ((e.ambientDimension - 6) + 5)))
    (LinearIsometryEquiv.neg ℝ)

theorem boundaryUnitFrame_other (p : Boundary A) (hp : p.val ∈ otherEnd A) :
    boundaryUnitFrame A p = (inducedBoundaryFrame A p).comp
      (boundaryFrameCoordinates (e := e)).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [boundaryUnitFrame, boundaryUnitScale_other A p hp, one_smul, boundaryAppendedFrame_eq]

theorem boundaryUnitFrame_top (p : Boundary A) (hp : p.val ∈ topEnd A) :
    boundaryUnitFrame A p = (inducedBoundaryFrame A p).comp
      ((boundaryLastReflection (e := e)).trans
        (boundaryFrameCoordinates (e := e))).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [boundaryUnitFrame, boundaryUnitScale_top A p hp]
  apply ContinuousLinearMap.ext
  intro v
  change OrthogonalUnitExtension.operator (traceNormalFrame A p.val)
      ((-1 : ℝ) • outwardNormal A p) v =
    ((inducedBoundaryFrame A p).comp
      (boundaryFrameCoordinates (e := e)).toContinuousLinearEquiv.toContinuousLinearMap)
        (boundaryLastReflection (e := e) v)
  rw [← boundaryAppendedFrame_eq, OrthogonalUnitExtension.operator_apply,
    OrthogonalUnitExtension.operator_apply]
  change traceNormalFrame A p.val v.fst + v.snd • ((-1 : ℝ) • outwardNormal A p) =
    traceNormalFrame A p.val v.fst + (-v.snd) • outwardNormal A p
  rw [smul_smul, mul_neg_one]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
