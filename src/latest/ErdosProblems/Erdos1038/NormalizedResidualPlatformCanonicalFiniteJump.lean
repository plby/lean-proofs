import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalConcrete
import ErdosProblems.Erdos1038.NormalizedResidualPlatformBlockTangent
import ErdosProblems.Erdos1038.PlatformResidualMaterialAbelPairingLimit
import ErdosProblems.Erdos1038.HighKPlatformFunctionalAssembly
import ErdosProblems.Erdos1038.PlatformReferenceExteriorCrossingBridge
import ErdosProblems.Erdos1038.HighKPlatformCanonicalCalibration

/-!
# Canonical normalized support from the finite-jump certificate

The canonical crossing theorem previously exposed a block-to-boundary
pairing premise.  The exact block tangent and the finite-jump Abel/Hilbert
identity prove that premise automatically.  Thus the only remaining hard
analytic input is the concrete finite-jump dominated-convergence
certificate itself.
-/

set_option warningAsError false

open Set Polynomial

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Fully joined canonical support theorem.  Given the explicit exterior
crossings, their positive reciprocal-slope weights, and the single
finite-jump certificate, all block integrability and pairing inequalities
are discharged internally. -/
theorem normalized_platformResidualSupportingBound_of_finiteJumpMaterialCrossings
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha1 : 1 ≤ platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hxPlusS : xPlus < s) (hs : 0 < s) (hsa : s < platformA)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) platformA xPlus)
    (hminusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus ≠ 0)
    (hsigmaMinus : 0 <
      platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
    (hsigmaPlus : 0 <
      platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
    (hfiniteJump : PlatformResidualMaterialFiniteJumpPairingCertificate
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold (xPlus - xMinus)
      (normalizedMainComponentWidth h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let sigmaMinus := platformReferenceNegativeCrossingAdjointWeight
    C k platformA hk ha ha2 hthreshold xMinus
  let sigmaPlus := platformReferencePositiveCrossingAdjointWeight
    C k platformA hk ha ha2 hthreshold xPlus
  have hintegrable : PlatformResidualPairingIntegrable C k platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold :=
    platformResidualPairingIntegrable_of_finiteJumpCertificate
      C k platformA hk ha ha2 hthreshold
      (lt_trans hminus.1 ha) hplus.2.1
      (by simpa only [C, k, sigmaMinus] using! hsigmaMinus)
      (by simpa only [C, k, sigmaPlus] using! hsigmaPlus)
      (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hfiniteJump)
  have hblocksReduced :
      (∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
        platformResidualReducedDirectionalPairing C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
    simpa only [C, k, sigmaMinus, sigmaPlus] using!
      h.normalized_sum_platformResidualTangentBlockTerm_le_reducedFieldPairing
        hres hk ha ha2 hthreshold (lt_trans hminus.1 ha) hplus.2.1
          (by simpa only [C, k, sigmaMinus] using! hsigmaMinus)
          (by simpa only [C, k, sigmaPlus] using! hsigmaPlus)
          (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hintegrable)
  have hweak :=
    platformResidualReducedDirectionalPairing_eq_boundaryExterior_add_endpoint
      C k platformA hk ha ha2 hthreshold
      (lt_trans hminus.1 ha) hplus.2.1
      (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hfiniteJump)
  have hBlockPairing :
      (∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
        platformBoundaryExteriorVariation platformA xMinus xPlus
            sigmaMinus sigmaPlus
            (platformResidualMaterialMean C k platformA
              hk ha ha2 hthreshold)
            (platformResidualMaterialCosineCoefficient C k platformA
              hk ha ha2 hthreshold) +
          endpointAdjointGamma (platformRadius platformA)
              sigmaMinus sigmaPlus (platformRho platformA xMinus)
                (platformRho platformA xPlus) *
            platformResidualMaterialField C k platformA
              hk ha ha2 hthreshold Real.pi := by
    rw [← hweak]
    exact hblocksReduced
  apply h.normalized_platformResidualSupportingBound_of_canonicalMaterialCrossingVelocity_endpoint
    hres hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier
      hminus hplus hminusDerivative hplusDerivative
      hsigmaMinus.le hsigmaPlus.le
  simpa only [C, k, sigmaMinus, sigmaPlus] using! hBlockPairing

/-- Local-crossing specialization.  The positive-slope crossing predicate
itself supplies a positive separation barrier strictly between the crossing
and the platform edge, so no separately chosen barrier point is needed. -/
theorem normalized_platformResidualSupportingBound_of_finiteJumpLocalCrossings
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha1 : 1 ≤ platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) platformA xPlus)
    (hminusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus ≠ 0)
    (hsigmaMinus : 0 <
      platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
    (hsigmaPlus : 0 <
      platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
    (hfiniteJump : PlatformResidualMaterialFiniteJumpPairingCertificate
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold (xPlus - xMinus)
      (normalizedMainComponentWidth h) := by
  obtain ⟨s, hxPlusS, _hsPlatform, hsa, hbarrier⟩ :=
    hplus.2.2.2 platformA hplus.2.1
  exact h.normalized_platformResidualSupportingBound_of_finiteJumpMaterialCrossings
    hres hk ha ha1 ha2 hthreshold hxPlusS
      (hplus.1.trans hxPlusS) hsa hbarrier hminus hplus
      hminusDerivative hplusDerivative hsigmaMinus hsigmaPlus hfiniteJump

/-- Final canonical platform adapter.  Once a numerical regime supplies its
effective scalar calibration at the two explicit crossings, the finite-jump
certificate and the canonical mesh limits yield the strict normalized
functional required by the high-ratio theorem. -/
theorem normalized_functional_strict_of_finiteJumpMaterialCrossings
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha1 : 1 ≤ platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hxPlusS : xPlus < s) (hs : 0 < s) (hsa : s < platformA)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) platformA xPlus)
    (hminusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus ≠ 0)
    (hsigmaMinus : 0 <
      platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
    (hsigmaPlus : 0 <
      platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
    (hcalibration : PlatformEffectiveCalibration
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus))
    (hfiniteJump : PlatformResidualMaterialFiniteJumpPairingCertificate
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold) :
    L < normalizedMainComponentWidth h +
      2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let sigmaMinus := platformReferenceNegativeCrossingAdjointWeight
    C k platformA hk ha ha2 hthreshold xMinus
  let sigmaPlus := platformReferencePositiveCrossingAdjointWeight
    C k platformA hk ha ha2 hthreshold xPlus
  have hsupport :=
    h.normalized_platformResidualSupportingBound_of_finiteJumpMaterialCrossings
      hres hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier
        hminus hplus hminusDerivative hplusDerivative
        hsigmaMinus hsigmaPlus hfiniteJump
  exact orderedResidual_functional_strict_of_effectiveCalibration C
    hk ha ha2 hthreshold (lt_trans hminus.1 ha) hplus.2.1
      (by simpa only [C, k, sigmaMinus] using! hsigmaMinus)
      (by simpa only [C, k, sigmaPlus] using! hsigmaPlus)
      (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hcalibration)
      (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hsupport)

/-- Barrier-free final adapter: the local positive crossing produces the
separation point internally. -/
theorem normalized_functional_strict_of_finiteJumpLocalCrossings
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha1 : 1 ≤ platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold) platformA xPlus)
    (hminusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative :
      platformReferenceExteriorPotentialXDerivativeLimit
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus ≠ 0)
    (hsigmaMinus : 0 <
      platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
    (hsigmaPlus : 0 <
      platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
    (hcalibration : PlatformEffectiveCalibration
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus))
    (hfiniteJump : PlatformResidualMaterialFiniteJumpPairingCertificate
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold) :
    L < normalizedMainComponentWidth h +
      2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let sigmaMinus := platformReferenceNegativeCrossingAdjointWeight
    C k platformA hk ha ha2 hthreshold xMinus
  let sigmaPlus := platformReferencePositiveCrossingAdjointWeight
    C k platformA hk ha ha2 hthreshold xPlus
  have hsupport :=
    h.normalized_platformResidualSupportingBound_of_finiteJumpLocalCrossings
      hres hk ha ha1 ha2 hthreshold hminus hplus
        hminusDerivative hplusDerivative hsigmaMinus hsigmaPlus hfiniteJump
  exact orderedResidual_functional_strict_of_effectiveCalibration C
    hk ha ha2 hthreshold (lt_trans hminus.1 ha) hplus.2.1
      (by simpa only [C, k, sigmaMinus] using! hsigmaMinus)
      (by simpa only [C, k, sigmaPlus] using! hsigmaPlus)
      (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hcalibration)
      (by simpa only [C, k, sigmaMinus, sigmaPlus] using! hsupport)

/-- Compact final interface consumed by the numerical regime split. -/
theorem normalized_functional_strict_of_finiteJumpCanonicalCrossingData
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha1 : 1 ≤ platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hcrossing : PlatformCanonicalExteriorCrossingData
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold xMinus xPlus)
    (hcalibration : PlatformEffectiveCalibration
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus))
    (hfiniteJump : PlatformResidualMaterialFiniteJumpPairingCertificate
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold) :
    L < normalizedMainComponentWidth h +
      2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  exact h.normalized_functional_strict_of_finiteJumpLocalCrossings
    hres hk ha ha1 ha2 hthreshold hcrossing.negativeCrossing
      hcrossing.positiveCrossing hcrossing.negativeDerivative_ne
      hcrossing.positiveDerivative_ne hcrossing.negativeWeight_pos
      hcrossing.positiveWeight_pos hcalibration hfiniteJump

/-- Checker-facing compact interface.  Explicit zero/slope data and an
explicit reciprocal-slope calibration are transported to the canonical
notations internally. -/
theorem normalized_functional_strict_of_finiteJumpExplicitCrossing
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha1 : 1 ≤ platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hcrossing : PlatformExplicitExteriorCrossingCertificate
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus)
    (hcalibration : PlatformEffectiveCalibration
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (-1 / platformExteriorWx (normalizedEndpointResidualRatio h)
        platformA xMinus)
      (1 / platformExteriorWx (normalizedEndpointResidualRatio h)
        platformA xPlus))
    (hfiniteJump : PlatformResidualMaterialFiniteJumpPairingCertificate
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
      hk ha ha2 hthreshold) :
    L < normalizedMainComponentWidth h +
      2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  let C := h.normalizedResidualConfiguration hres
  have hcanonical := hcrossing.toCanonical C hk ha ha2 hthreshold
  have hcanonicalCalibration :=
    hcrossing.effectiveCalibration_toCanonical C hk ha ha2 hthreshold
      hcalibration
  exact h.normalized_functional_strict_of_finiteJumpCanonicalCrossingData
    hres hk ha ha1 ha2 hthreshold hcanonical
      hcanonicalCalibration hfiniteJump

end EndpointNormalizationHypotheses

end

end Erdos1038
