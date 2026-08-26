import ErdosProblems.Erdos1038.PlatformResidualBlockTangent
import ErdosProblems.Erdos1038.NormalizedResidualBridge

/-!
# The concrete block tangent for the normalized residual configuration

The normalized residual index inherits the ambient real order.  Hence its
shifted target locations satisfy the order hypothesis of the concrete block
tangent theorem automatically.
-/

set_option warningAsError false

open Set Polynomial

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Pointwise manuscript inequality `(4.28)` for the actual normalized
residual configuration.  No additional target-order certificate is needed. -/
theorem normalized_platformResidualBlockLogTangentLower_le_directionalField
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (i : NormalizedResidualIndex h) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold i)
      (platformResidualBlockRight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold i)) :
    platformResidualBlockLogTangentLower
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold i theta ≤
      platformResidualReducedDirectionalField
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold i theta := by
  exact platformResidualBlockLogTangentLower_le_reducedDirectionalField
    (h.normalizedResidualConfiguration hres) hk ha ha2 hthreshold
      (h.normalizedResidualConfiguration_location_strictMono hres)
      i htheta

/-- Integrated block tangent for the normalized residual configuration. -/
theorem normalized_sum_platformResidualTangentBlockTerm_le_reducedFieldPairing
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hxMinus : xMinus < platformA) (hxPlus : xPlus < platformA)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hintegrable : PlatformResidualPairingIntegrable
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    (∑ i, platformResidualTangentBlockTerm
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
      platformResidualReducedDirectionalPairing
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  exact sum_platformResidualTangentBlockTerm_le_reducedFieldPairing
    (h.normalizedResidualConfiguration hres) hk ha ha2 hthreshold
      hxMinus hxPlus hsigmaMinus hsigmaPlus
      (h.normalizedResidualConfiguration_location_strictMono hres)
      hintegrable

/-- Reduced-field pairing criterion for the normalized supporting bound. -/
theorem normalized_platformResidualSupportingBound_of_reducedFieldPairing
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus M0 targetWidth : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hxMinus : xMinus < platformA) (hxPlus : xPlus < platformA)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hintegrable : PlatformResidualPairingIntegrable
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold)
    (hpairing : M0 + platformResidualReducedDirectionalPairing
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold ≤
      targetWidth) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth := by
  exact platformResidualSupportingBound_of_reducedFieldPairing
    (h.normalizedResidualConfiguration hres) hk ha ha2 hthreshold
      hxMinus hxPlus hsigmaMinus hsigmaPlus
      (h.normalizedResidualConfiguration_location_strictMono hres)
      hintegrable hpairing

end EndpointNormalizationHypotheses

end

end Erdos1038
