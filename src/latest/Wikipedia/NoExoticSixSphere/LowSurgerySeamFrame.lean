import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryZeroDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseLowEndFrameCoordinates
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendReflection

/-!
# The actual low-surgery normal framing on the retained time-zero seam

The native new-end framing is the original orthonormal frame with the
actual added coordinate axes, up to a fixed isometric column change.
That change retains the negative outward-height sign and the exact column
permutation. The equality holds on an open time neighborhood, hence also
under the original-atlas zero-fiber diffeomorphism.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.LowSurgerySeam

open GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
open FramedAttachingProduct RoundedTrace NativeSurgery

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : Sphere d → M} (A : FramedAttachingProduct e a f)

def columnChange : letI := boundaryChartedSpace A;
    (otherBoundaryEuclideanEmbedding A).NormalModel ≃ₗᵢ[ℝ]
      Vector ((e.ambientDimension - 7) + (1 + (1 + (d + 1)))) := by
  let := boundaryChartedSpace A
  exact ((boundaryNormalModelCoordinates A).trans
    (OrthogonalFrameAppend.lastReflection ((e.ambientDimension - 7) + (1 + (d + 1))))).trans
      (endColumnPermutation d (e.ambientDimension - 7))

theorem framing_retainedBand (T : TimeData A) (p : retainedTimeBand A T) :
    letI := boundaryChartedSpace A;
    ∀ v, (inducedOtherEndNormalFraming A).ambient (retainedTimeMap A T p) v =
      BlockSum.operator (1 + (1 + (d + 1))) (a.orthonormal p.val).val (columnChange A v) := by
  let := boundaryChartedSpace A
  intro v
  rw [inducedOtherEndNormalFraming_ambient, inducedBoundaryFrame_retainedTimeMap,
    OrthogonalFrameAppend.operator_neg, append_heightUnit_eq_block]
  simp only [columnChange, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  congr 1

theorem embedding_retainedBand (T : TimeData A) (p : retainedTimeBand A T) :
    letI := boundaryChartedSpace A;
    (otherBoundaryEuclideanEmbedding A).toFun (retainedTimeMap A T p) =
      appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
        (e.toFun p.val) := by
  let := boundaryChartedSpace A
  exact Wikipedia.HopfProblem.DegreeCollapse.LowHeightCylinder.heightCylinder_zero d e p.val

theorem framing_zero (hR : A.radius = 2) (T : TimeData A) (p : OriginalZero A T) :
    letI := boundaryChartedSpace A;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    ∀ v, (inducedOtherEndNormalFraming A).ambient (zeroDiffeomorph A hR T p).val v =
      BlockSum.operator (1 + (1 + (d + 1))) (a.orthonormal p.val).val (columnChange A v) := by
  let := boundaryChartedSpace A
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  exact framing_retainedBand A T (originalZeroToBand A T p)

end NoExoticSixSphere.LowSurgerySeam
