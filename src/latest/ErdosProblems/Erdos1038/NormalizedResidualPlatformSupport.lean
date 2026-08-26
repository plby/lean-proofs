import ErdosProblems.Erdos1038.HighKBlockFunctionalAssembly
import ErdosProblems.Erdos1038.NormalizedResidualWidth

/-!
# Exact normalized target for the platform supporting inequality

This module isolates the remaining platform input.  The normalized target
width is already the exact residual inverse series.  Consequently a platform
reference proves the concrete supporting bound as soon as its base value and
block tangent sum are identified with the reference inverse series and its
directional series, with the two corresponding convergence facts.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set Polynomial

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Exact reduction of the concrete normalized platform support bound to a
reference inverse-series certificate.  There is no target convergence
hypothesis: endpoint separation supplies it automatically. -/
theorem normalized_platformResidualSupportingBound_of_inverseSeries
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus M0 : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    {reference : NormalizedResidualIndex h → ℝ}
    (href : reference ∈ positiveCoordinates (NormalizedResidualIndex h))
    (hsumReference : Summable (fun n ↦ scaledLagrangeCoefficient
      (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)) n reference))
    (hsumDirectional : Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) (2 * j + 1) reference
        (h.normalizedResidualConfiguration hres).location))
    (hM0 : M0 = inverseWidthSeries
      (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)) reference)
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i =
        inverseWidthSeriesDirectional
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h)) reference
          (h.normalizedResidualConfiguration hres).location) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 (normalizedMainComponentWidth h) := by
  unfold PlatformResidualSupportingBound
  rw [hM0, hblocks]
  exact h.inverseWidthSeries_add_directional_le_normalizedMainComponentWidth
    hres href hsumReference hsumDirectional

/-- Equivalent endpoint form of the concrete normalized platform statement.
This makes the sole unresolved numerical inequality explicit even when no
reference vector has yet been constructed. -/
theorem normalized_platformResidualSupportingBound_iff_inverseWidthSeries
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus M0 : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA) :
    PlatformResidualSupportingBound
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
        M0 (normalizedMainComponentWidth h) ↔
      M0 + ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        inverseWidthSeries
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))
          (h.normalizedResidualConfiguration hres).location := by
  unfold PlatformResidualSupportingBound
  rw [h.normalizedMainComponentWidth_eq_inverseWidthSeries hres]

end EndpointNormalizationHypotheses

end

end Erdos1038
