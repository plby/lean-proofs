import Wikipedia.HopfProblem.DegreeCollapseFramedSevenFilling
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryBoundaryImmersion

/-!
# The actual surgery half is a framed filling of the original zero fiber

Every field is supplied by the existing native construction. In particular,
the normal frame spans the actual half's normal space and the boundary
diffeomorphism uses the original zero-fiber atlas. This packages a supplied
regular-time filling operation; it does not create an initial filling.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def framedFilling : letI := originalZeroAtlas A T;
    FramedSevenFilling (𝓡 6) (OriginalZero A T) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  let := positiveBoundaryAtlas A hR T
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  exact
    { W := PositiveHalf A hR T
      topology := inferInstance
      hausdorff := (isClosedEmbedding_halfAmbientMap A hR T).isEmbedding.t2Space
      secondCountable := (isClosedEmbedding_halfAmbientMap A hR T).isEmbedding.secondCountableTopology
      compact := compactSpace_positiveHalf A hR T
      atlas := positiveHalfChartedSpace A hR T
      manifold := positiveHalf_isManifold A hR T
      ambientDimension := e.ambientDimension + 6
      inclusion := halfAmbientMap A hR T
      closed_embedding := isClosedEmbedding_halfAmbientMap A hR T
      smooth_inclusion := contMDiff_halfAmbientMap A hR T
      injective_differential := injective_halfAmbientDerivative A hR T
      frame := halfNormalFraming A hR T
      boundaryAtlas := positiveBoundaryAtlas A hR T
      boundaryManifold := positiveBoundary_isManifold A hR T
      boundaryDiffeomorph := (zeroDiffeomorph A hR T).trans (positiveBoundaryDiffeomorph A hR T).symm
      smooth_boundaryInclusion := contMDiff_positiveBoundaryInclusion A hR T
      injective_boundaryDifferential := injective_mfderiv_positiveBoundaryInclusion A hR T }

theorem framedFilling_inclusion (p : PositiveHalf A hR T) :
    letI := originalZeroAtlas A T;
    (framedFilling A hR T).inclusion p = halfAmbientMap A hR T p := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
