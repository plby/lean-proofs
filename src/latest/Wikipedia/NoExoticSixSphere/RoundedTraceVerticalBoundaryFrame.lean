import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryTimeTangent
import Wikipedia.NoExoticSixSphere.NormalGraphPlaneVerticalShear

/-!
# Exact endpoint normal columns of the actual sheared tube

The old trace normal frame is unchanged. The last spatial column is the
actual outward unit normal times a smooth nonzero scalar, positive at the
surgery end and negative at the original end.
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

def boundaryVerticalScale (p : Boundary A) : ℝ :=
  NormalGraphPlane.verticalCoefficient (outwardNormal A p) (boundaryTimeSlope A p)

theorem contMDiff_boundaryVerticalScale : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞ (boundaryVerticalScale A) := by
  let := boundaryChartedSpace A
  exact NormalGraphPlane.contMDiff_verticalCoefficient (contMDiff_outwardNormal A)
    (contMDiff_boundaryTimeSlope A) (boundaryTimeSlope_ne_zero A)

theorem boundaryVerticalScale_ne_zero (p : Boundary A) : boundaryVerticalScale A p ≠ 0 :=
  NormalGraphPlane.verticalCoefficient_ne_zero _ (boundaryTimeSlope_ne_zero A p)

theorem boundaryVerticalScale_pos_other (p : Boundary A) (hp : p.val ∈ otherEnd A) :
    0 < boundaryVerticalScale A p :=
  NormalGraphPlane.verticalCoefficient_pos _ (bordismTimeDifferential_outward_other A p hp)

theorem boundaryVerticalScale_neg_top (p : Boundary A) (hp : p.val ∈ topEnd A) :
    boundaryVerticalScale A p < 0 :=
  NormalGraphPlane.verticalCoefficient_neg _ (bordismTimeDifferential_outward_top A p hp)

theorem verticalShear_liftedFrame (p : ambientSet A)
    (v : Vector ((e.ambientDimension - 6) + 5)) :
    verticalShear A p (timeGraphLiftedFrame A p v) = timeGraphLiftedFrame A p v := by
  rw [verticalShear_apply]
  have hz : timeGraphTimeFunctional (e := e) (timeGraphLiftedFrame A p v) = 0 := rfl
  rw [hz, zero_smul, sub_zero]

theorem verticalShear_newNormal_boundary (p : Boundary A) :
    verticalShear A p.val (timeGraphNewNormal A p.val) =
      WithLp.toLp 2 ((0 : ℝ), boundaryVerticalScale A p • outwardNormal A p) := by
  rw [verticalShear_apply, timeGraphNewNormal_boundary, cutoffTimeTangent_boundary]
  exact NormalGraphPlane.vertical_normalColumn _ (boundaryTimeSlope_ne_zero A p)

theorem verticalFrame_boundary (p : Boundary A) (v : TimeGraphFrameSpace (e := e)) :
    verticalFrame A p.val v = WithLp.toLp 2 ((0 : ℝ),
      traceNormalFrame A p.val v.fst +
        (v.snd * boundaryVerticalScale A p) • outwardNormal A p) := by
  change verticalShear A p.val (timeGraphFrame A p.val v) = _
  rw [timeGraphFrame_apply, map_add, map_smul, verticalShear_liftedFrame,
    verticalShear_newNormal_boundary]
  apply (timeGraphCoordinates (e := e)).injective
  apply Prod.ext
  · change (0 : ℝ) + v.snd * 0 = 0
    ring
  · change traceNormalFrame A p.val v.fst +
      v.snd • (boundaryVerticalScale A p • outwardNormal A p) = _
    rw [smul_smul]
    rfl

def boundaryVerticalFrame (p : Boundary A) :
    TimeGraphFrameSpace (e := e) →L[ℝ] Vector (e.ambientDimension + 6) :=
  ((ContinuousLinearMap.snd ℝ ℝ (Vector (e.ambientDimension + 6))).comp
    (timeGraphCoordinates (e := e)).toContinuousLinearMap).comp (verticalFrame A p.val)

theorem boundaryVerticalFrame_apply (p : Boundary A) (v : TimeGraphFrameSpace (e := e)) :
    boundaryVerticalFrame A p v = traceNormalFrame A p.val v.fst +
      (v.snd * boundaryVerticalScale A p) • outwardNormal A p := by
  change (timeGraphCoordinates (e := e) (verticalFrame A p.val v)).2 = _
  rw [verticalFrame_boundary]
  rfl

theorem contMDiff_boundaryVerticalFrame : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, TimeGraphFrameSpace (e := e) →L[ℝ]
      Vector (e.ambientDimension + 6)) ∞ (boundaryVerticalFrame A) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact contMDiff_const.clm_comp
    ((contMDiff_verticalFrame A).comp (contMDiff_boundaryInclusion A))

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
