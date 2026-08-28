import Wikipedia.NoExoticSixSphere.QuaternionicHopfDoubledProductFrame
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductAtlas
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductEuclideanCoordinates

/-!
# The actual product representative as a six-dimensional Euclidean embedding

The source has the proved-compatible Euclidean atlas. The ambient map uses
exactly the finite isometry underlying the retained source compactification.
Its tangent and normal spaces are computed from the actual differential.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southPairEuclideanAmbient (p : Sphere 3 × Sphere 3) : V 16 :=
  southPairAmbientEuclideanCoordinates (southPairDoubledAmbient p)

theorem contMDiff_southPairDoubledAmbient_euclidean :
    letI := southPairEuclideanAtlas;
    ContMDiff (𝓡 6) 𝓘(ℝ, SouthPairAmbientModel) ∞ southPairDoubledAmbient := by
  let _ := southPairEuclideanAtlas
  have h := contMDiff_southPairDoubledAmbient.comp southPairEuclideanToProduct.contMDiff
  exact h

theorem contMDiff_southPairEuclideanAmbient :
    letI := southPairEuclideanAtlas; ContMDiff (𝓡 6) (𝓡 16) ∞ southPairEuclideanAmbient := by
  let _ := southPairEuclideanAtlas
  exact southPairAmbientEuclideanCoordinates.toContinuousLinearEquiv.contDiff.contMDiff.comp
    contMDiff_southPairDoubledAmbient_euclidean

theorem southPairEuclideanAmbient_derivative (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    mfderiv (𝓡 6) (𝓡 16) southPairEuclideanAmbient p =
      southPairAmbientEuclideanCoordinates.toContinuousLinearMap.comp
        (NormalFrameOfEquations.ambientDifferential (𝓡 6) southPairDoubledAmbient p) := by
  let _ := southPairEuclideanAtlas
  let L := southPairAmbientEuclideanCoordinates.toContinuousLinearMap
  change mfderiv (𝓡 6) (𝓡 16) (L ∘ southPairDoubledAmbient) p = _
  rw [mfderiv_comp p L.differentiableAt.mdifferentiableAt
    (contMDiff_southPairDoubledAmbient_euclidean.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

theorem southPairEuclideanAmbient_differential_injective (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    Function.Injective (mfderiv (𝓡 6) (𝓡 16) southPairEuclideanAmbient p) := by
  let _ := southPairEuclideanAtlas
  rw [southPairEuclideanAmbient_derivative]
  exact southPairAmbientEuclideanCoordinates.injective.comp
    (southPairEuclidean_differential_injective contMDiff_southPairDoubledAmbient p
      (southPairDoubledAmbient_differential_injective p))

def southPairEuclideanEmbedding :
    letI := southPairEuclideanAtlas; EuclideanEmbedding 6 (Sphere 3 × Sphere 3) := by
  let _ := southPairEuclideanAtlas
  exact {
    ambientDimension := 16
    toFun := southPairEuclideanAmbient
    smooth := contMDiff_southPairEuclideanAmbient
    closedEmbedding := southPairAmbientEuclideanCoordinates.toHomeomorph.isClosedEmbedding.comp
      southPairDoubledAmbient_isClosedEmbedding
    injective_mfderiv := southPairEuclideanAmbient_differential_injective }

theorem southPairEuclideanEmbedding_tangentImage (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    southPairEuclideanEmbedding.tangentImage p =
      (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) southPairAmbient p).range.map
          southPairAmbientEuclideanCoordinates.toLinearEquiv.toLinearMap := by
  let _ := southPairEuclideanAtlas
  change (mfderiv (𝓡 6) (𝓡 16) southPairEuclideanAmbient p).range = _
  rw [southPairEuclideanAmbient_derivative]
  change (southPairAmbientEuclideanCoordinates.toLinearEquiv.toLinearMap.comp
    (NormalFrameOfEquations.ambientDifferential (𝓡 6)
      southPairDoubledAmbient p).toLinearMap).range = _
  rw [LinearMap.range_comp, southPairEuclidean_tangentRange contMDiff_southPairDoubledAmbient,
    southPairDoubledAmbient_tangentRange]

theorem southPairEuclideanEmbedding_normalFiber (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    southPairEuclideanEmbedding.normalFiber p =
      (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) southPairAmbient p).rangeᗮ.map
          southPairAmbientEuclideanCoordinates.toLinearEquiv.toLinearMap := by
  let _ := southPairEuclideanAtlas
  change (southPairEuclideanEmbedding.tangentImage p)ᗮ = _
  rw [southPairEuclideanEmbedding_tangentImage]
  exact (Submodule.map_orthogonal_equiv _ southPairAmbientEuclideanCoordinates).symm

end NoExoticSixSphere.QuaternionicHopf
