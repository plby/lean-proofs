import ErdosProblems.Erdos1038.NormalizedResidualPlatformSupportLimit
import ErdosProblems.Erdos1038.PlatformReferenceRefinement

/-!
# Canonical normalized platform-support target

This module plugs the inverse-CDF platform samples into the product
refinement theorem.  All finite target-side algebra and every positivity
condition are discharged.  The remaining premises are exactly the
reference-series convergence and the analytic block lower bound.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set Polynomial Filter Topology

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Canonical-refinement form of the normalized platform supporting bound. -/
theorem normalized_platformResidualSupportingBound_of_canonicalRefinement
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus M0 D : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        degree
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (2 * j + 1)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget
          (h.normalizedResidualConfiguration hres) n)))
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n))
      atTop (𝓝 M0))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget
          (h.normalizedResidualConfiguration hres) n))
      atTop (𝓝 D))
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 (normalizedMainComponentWidth h) := by
  apply h.normalized_platformResidualSupportingBound_of_productRefinements
    hres hk ha ha2 hthreshold
    (platformResidualRefinementReference
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold)
  · exact fun n ↦
      platformResidualRefinementReference_mem_positiveCoordinates
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold n
  · simpa only [platformResidualRefinementAlpha] using! hsumReference
  · simpa only [platformResidualRefinementAlpha,
      platformResidualRefinementTarget] using! hsumDirectional
  · simpa only [platformResidualRefinementAlpha] using! hbase
  · simpa only [platformResidualRefinementAlpha,
      platformResidualRefinementTarget] using! hdirectional
  · exact hblocks

/-- Concrete reference-width specialization used by scalar calibration:
the platform main width is the distance between its two exterior crossings. -/
theorem normalized_platformResidualSupportingBound_of_canonicalCrossingRefinement
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        degree
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (2 * j + 1)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget
          (h.normalizedResidualConfiguration hres) n)))
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n))
      atTop (𝓝 (xPlus - xMinus)))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget
          (h.normalizedResidualConfiguration hres) n))
      atTop (𝓝 D))
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) (normalizedMainComponentWidth h) := by
  exact h.normalized_platformResidualSupportingBound_of_canonicalRefinement
    hres hk ha ha2 hthreshold hsumReference hsumDirectional
    hbase hdirectional hblocks

end EndpointNormalizationHypotheses

end

end Erdos1038
