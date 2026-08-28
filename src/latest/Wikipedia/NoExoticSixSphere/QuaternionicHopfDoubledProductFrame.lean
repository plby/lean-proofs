import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeSmoothness
import Wikipedia.NoExoticSixSphere.AmbientDifferentialScaling
import Wikipedia.NoExoticSixSphere.SmoothRangeFrameCongr

/-!
# The actual doubled product core and its normal frame

The endpoint tube is centered on twice the original product inclusion.
Its tangent image is proved equal to that of the original inclusion in
the same product atlas. Consequently the computed raw product frame is
also the actual normal frame of this doubled core.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southPairDoubledAmbient (p : Sphere 3 × Sphere 3) : SouthPairAmbientModel :=
  (2 : ℝ) • southPairAmbient p

theorem contMDiff_southPairDoubledAmbient :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, SouthPairAmbientModel) ∞ southPairDoubledAmbient := by
  let L : SouthPairAmbientModel →L[ℝ] SouthPairAmbientModel :=
    (2 : ℝ) • ContinuousLinearMap.id ℝ SouthPairAmbientModel
  exact L.contDiff.contMDiff.comp contMDiff_southPairAmbient

theorem southPairDoubledAmbient_injective : Function.Injective southPairDoubledAmbient :=
  (LinearEquiv.smulOfNeZero ℝ SouthPairAmbientModel 2 (by norm_num)).injective.comp
    southPairAmbient_injective

theorem southPairDoubledAmbient_isClosedEmbedding :
    Topology.IsClosedEmbedding southPairDoubledAmbient :=
  contMDiff_southPairDoubledAmbient.continuous.isClosedEmbedding
    southPairDoubledAmbient_injective

theorem southPairDoubledAmbient_derivative (p : Sphere 3 × Sphere 3) :
    NormalFrameOfEquations.ambientDifferential ((𝓡 3).prod (𝓡 3)) southPairDoubledAmbient p =
      (2 : ℝ) • NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) southPairAmbient p :=
  NormalFrameOfEquations.ambientDifferential_smul contMDiff_southPairAmbient 2 p

theorem southPairDoubledAmbient_tangentRange (p : Sphere 3 × Sphere 3) :
    (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairDoubledAmbient p).range =
        (NormalFrameOfEquations.ambientDifferential
          ((𝓡 3).prod (𝓡 3)) southPairAmbient p).range :=
  NormalFrameOfEquations.range_ambientDifferential_smul
    contMDiff_southPairAmbient 2 (by norm_num) p

theorem southPairDoubledAmbient_differential_injective (p : Sphere 3 × Sphere 3) :
    Function.Injective (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairDoubledAmbient p) :=
  NormalFrameOfEquations.injective_ambientDifferential_smul
    contMDiff_southPairAmbient 2 (by norm_num) p (southPairAmbient_differential_injective p)

def southPairDoubledNormalFrame : SmoothRangeFrame ((𝓡 3).prod (𝓡 3))
    (fun p : Sphere 3 × Sphere 3 ↦ (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairDoubledAmbient p).rangeᗮ.starProjection)
        SouthPairNormalModel :=
  southPairNormalFrame.congrProjection (funext (fun p ↦ congrArg
    (fun S : Submodule ℝ SouthPairAmbientModel ↦ Sᗮ.starProjection)
      (southPairDoubledAmbient_tangentRange p).symm))

theorem southPairDoubledNormalFrame_ambient (p : Sphere 3 × Sphere 3) :
    southPairDoubledNormalFrame.ambient p = southPairNormalFrame.ambient p :=
  southPairNormalFrame.congrProjection_ambient _ p

theorem southPairedRawTube_core (p : Sphere 3 × Sphere 3) :
    southPairedFrameTube 1 (p, 0) = southPairDoubledAmbient p :=
  southPairedFrameTube_core 1 p

theorem hasFDerivAt_southPairedRawTube_normal (p : Sphere 3 × Sphere 3) :
    HasFDerivAt (fun v : SouthPairNormalModel ↦ southPairedFrameTube 1 (p, v))
      (southPairDoubledNormalFrame.ambient p) 0 := by
  rw [southPairDoubledNormalFrame_ambient]
  exact hasFDerivAt_southPairedFrameTube_one p

end NoExoticSixSphere.QuaternionicHopf
