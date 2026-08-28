import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductEmbedding
import Wikipedia.NoExoticSixSphere.SmoothRangeFrameOfOperator

/-!
# The actual normal frame in the retained Euclidean coordinates

The target coordinate inverse is part of the frame, including its fixed
signs and radius factors. The range is proved to be the normal space of
the actual Euclidean embedding in its proved-compatible atlas.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southPairEuclideanNormalOperator (p : Sphere 3 × Sphere 3) : V 10 →L[ℝ] V 16 :=
  southPairAmbientEuclideanCoordinates.toContinuousLinearMap.comp
    ((southPairNormalFrame.ambient p).comp
      southPairNormalEuclideanCoordinates.symm.toContinuousLinearMap)

theorem contMDiff_southPairEuclideanNormalOperator_product :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 10 →L[ℝ] V 16) ∞
      southPairEuclideanNormalOperator := by
  change ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 10 →L[ℝ] V 16) ∞
    (fun p ↦ southPairAmbientEuclideanCoordinates.toContinuousLinearMap.comp
      ((southPairNormalFrame.ambient p).comp
        southPairNormalEuclideanCoordinates.symm.toContinuousLinearMap))
  exact contMDiff_const.clm_comp (southPairNormalFrame.contMDiff_ambient.clm_comp contMDiff_const)

theorem contMDiff_southPairEuclideanNormalOperator :
    letI := southPairEuclideanAtlas;
    ContMDiff (𝓡 6) 𝓘(ℝ, V 10 →L[ℝ] V 16) ∞ southPairEuclideanNormalOperator := by
  let _ := southPairEuclideanAtlas
  have h := contMDiff_southPairEuclideanNormalOperator_product.comp
    southPairEuclideanToProduct.contMDiff
  exact h

theorem southPairEuclideanNormalOperator_injective (p : Sphere 3 × Sphere 3) :
    Function.Injective (southPairEuclideanNormalOperator p) :=
  southPairAmbientEuclideanCoordinates.injective.comp
    ((southPairNormalFrame.ambient_injective p).comp
      southPairNormalEuclideanCoordinates.symm.injective)

theorem southPairEuclideanNormalOperator_range (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    (southPairEuclideanNormalOperator p).range = southPairEuclideanEmbedding.normalFiber p := by
  let _ := southPairEuclideanAtlas
  have hn : (southPairNormalFrame.ambient p).range =
      (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) southPairAmbient p).rangeᗮ := by
    rw [southPairNormalFrame.ambient_range_eq]
    exact Submodule.range_starProjection _
  have hc : ((southPairNormalFrame.ambient p).comp
      southPairNormalEuclideanCoordinates.symm.toContinuousLinearMap).range =
        (southPairNormalFrame.ambient p).range :=
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr southPairNormalEuclideanCoordinates.symm.surjective)
  change (southPairAmbientEuclideanCoordinates.toLinearEquiv.toLinearMap.comp
    ((southPairNormalFrame.ambient p).comp
      southPairNormalEuclideanCoordinates.symm.toContinuousLinearMap).toLinearMap).range = _
  rw [LinearMap.range_comp, hc, hn, southPairEuclideanEmbedding_normalFiber]

theorem southPairEuclideanNormalOperator_range_projection (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    (southPairEuclideanNormalOperator p).range =
      (southPairEuclideanEmbedding.normalProjection p).range := by
  let _ := southPairEuclideanAtlas
  rw [southPairEuclideanEmbedding.range_normalProjection]
  exact southPairEuclideanNormalOperator_range p

def southPairEuclideanNormalFrame :
    letI := southPairEuclideanAtlas;
    SmoothRangeFrame (𝓡 6) southPairEuclideanEmbedding.normalProjection
      southPairEuclideanEmbedding.NormalModel := by
  let _ := southPairEuclideanAtlas
  exact SmoothRangeFrame.ofOperator southPairEuclideanNormalOperator
    contMDiff_southPairEuclideanNormalOperator southPairEuclideanNormalOperator_injective
      southPairEuclideanNormalOperator_range_projection

theorem southPairEuclideanNormalFrame_ambient (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    southPairEuclideanNormalFrame.ambient p = southPairEuclideanNormalOperator p := by
  let _ := southPairEuclideanAtlas
  exact SmoothRangeFrame.ofOperator_ambient southPairEuclideanNormalOperator
    contMDiff_southPairEuclideanNormalOperator southPairEuclideanNormalOperator_injective
      southPairEuclideanNormalOperator_range_projection p

end NoExoticSixSphere.QuaternionicHopf
