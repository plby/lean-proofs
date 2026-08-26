import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalTail
import ErdosProblems.Erdos1038.PlatformReferenceSeriesLimits
import ErdosProblems.Erdos1038.PlatformReferenceDirectionalRootLimits
import ErdosProblems.Erdos1038.PlatformResidualMaterialExteriorIdentity
import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalAnalytic

/-!
# Canonical platform support after all mesh limits

Canonical quantile Riemann convergence, the finite-moment recurrences, and
uniform geometric domination now discharge both changing-dimensional
inverse-width limits.  The remaining continuum inputs are only the values
of the two explicit coefficient series and the genuine block/endpoint
inequalities.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Canonical support with both mesh limits discharged by the actual
moment recurrences and uniform comparison estimates. -/
theorem normalized_platformResidualSupportingBound_of_concreteSeries
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hs : 0 < s) (hsa : s < platformA)
    (hpotential : 0 < platformReferenceExteriorLogPotentialLimit
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold s)
    (hbaseValue :
      2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientLimit
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold (2 * j + 1) = xPlus - xMinus)
    (hdirectionalValue :
      2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientDirectionalLimit
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold (2 * j + 1) = D)
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
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hbase := tendsto_inverseWidthSeries_platformResidualRefinement
    C k platformA hk ha ha2 hthreshold hs hsa (by
      simpa only [C, k] using! hpotential)
  rw [show 2 * ∑' j,
      platformReferenceScaledLagrangeCoefficientLimit C k platformA
        hk ha ha2 hthreshold (2 * j + 1) = xPlus - xMinus by
    simpa only [C, k] using! hbaseValue] at hbase
  have hdirectional :=
    tendsto_inverseWidthSeriesDirectional_platformResidualRefinement
      C k platformA hk ha ha2 hthreshold hs hsa (by
        simpa only [C, k] using! hpotential)
  rw [show 2 * ∑' j,
      platformReferenceScaledLagrangeCoefficientDirectionalLimit
        C k platformA hk ha ha2 hthreshold (2 * j + 1) = D by
    simpa only [C, k] using! hdirectionalValue] at hdirectional
  apply h.normalized_platformResidualSupportingBound_of_positiveContinuumPotential
    hres hk ha ha2 hthreshold hs hsa hpotential
  · simpa only [C, k] using! hbase
  · simpa only [C, k] using! hdirectional
  · exact hblocks

/-- Endpoint-corrected Abel specialization of the concrete-series theorem.
The exterior Abel limit and the adjoint pairing limit are automatic. -/
theorem normalized_platformResidualSupportingBound_of_concreteSeries_endpoint
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus s endpointLimit : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hxMinus : xMinus < platformA) (hxPlus : xPlus < platformA)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    (hs : 0 < s) (hsa : s < platformA)
    (hpotential : 0 < platformReferenceExteriorLogPotentialLimit
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold s)
    (hbaseValue :
      2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientLimit
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold (2 * j + 1) = xPlus - xMinus)
    {abelCoefficient : ℕ → ℝ} {abelCoefficientBound : ℝ}
    (habelCoefficientBound :
      RealSequenceBoundedBy abelCoefficient abelCoefficientBound)
    (abelF0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    (hEndpointPartialSums : Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N,
        platformAbelEndpointSequence abelCoefficient n)
      atTop (nhds (endpointLimit - abelF0)))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hdirectionalValue :
      2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientDirectionalLimit
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold (2 * j + 1) =
        platformBoundaryExteriorVariation platformA xMinus xPlus
          sigmaMinus sigmaPlus abelF0 abelCoefficient)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        platformBoundaryExteriorVariation platformA xMinus xPlus
            sigmaMinus sigmaPlus abelF0 abelCoefficient +
          endpointAdjointGamma (platformRadius platformA)
            sigmaMinus sigmaPlus (platformRho platformA xMinus)
              (platformRho platformA xPlus) * endpointLimit) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) (normalizedMainComponentWidth h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hblocks :=
    platformResidualTangentBlockSum_le_boundaryExterior_of_endpoint_partialSums
      C hk ha ha2 hthreshold hxMinus hxPlus
      hsigmaMinus hsigmaPlus habelCoefficientBound abelF0 hlambda
      hEndpointPartialSums hEndpointNonpos (by
        simpa only [C, k] using! hBlockPairing)
  apply h.normalized_platformResidualSupportingBound_of_concreteSeries
    hres hk ha ha2 hthreshold hs hsa hpotential hbaseValue
    hdirectionalValue
  simpa only [C, k] using! hblocks

/-- Crossing-root specialization of the concrete canonical theorem.  Both
continuum coefficient-series values are now automatic: the base series is
the distance between the crossings, and the material series is their
implicit `M / Pₓ` width velocity. -/
theorem normalized_platformResidualSupportingBound_of_crossingVelocity
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus s : ℝ}
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
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        platformReferenceCrossingWidthMaterialVelocity
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold xMinus xPlus) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) (normalizedMainComponentWidth h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hlogBarrier : 0 < platformReferenceExteriorLogPotentialLimit
      C k platformA hk ha ha2 hthreshold s := by
    rw [← platformReferenceExteriorPotentialLimit_eq_logPotentialLimit
      C k platformA hk ha ha2 hthreshold hs]
    simpa only [C, k] using! hbarrier
  have hbaseValue :=
    two_mul_tsum_platformReferenceScaledLagrangeCoefficientLimit_eq_crossingWidth
      C k platformA hk ha ha1 ha2 hthreshold hxPlusS hs hsa
        (by simpa only [C, k] using! hbarrier)
        (by simpa only [C, k] using! hminus)
        (by simpa only [C, k] using! hplus)
  have hdirectionalValue :=
    two_mul_tsum_platformReferenceScaledLagrangeCoefficientDirectionalLimit_eq_crossingVelocity
      C k platformA hk ha ha1 ha2 hthreshold hxPlusS hs hsa
        (by simpa only [C, k] using! hbarrier)
        (by simpa only [C, k] using! hminus)
        (by simpa only [C, k] using! hplus)
        (by simpa only [C, k] using! hminusDerivative)
        (by simpa only [C, k] using! hplusDerivative)
  apply h.normalized_platformResidualSupportingBound_of_concreteSeries
    hres hk ha ha2 hthreshold hs hsa hlogBarrier
  · simpa only [C, k] using! hbaseValue
  · simpa only [C, k] using! hdirectionalValue
  · simpa only [C, k] using! hblocks

/-- Endpoint-corrected Abel adapter with automatic base and directional
series values.  The sole bridge between the two analytic notations is the
explicit equality identifying the chosen Abel boundary coefficient value
with the crossing `M / Pₓ` velocity. -/
theorem normalized_platformResidualSupportingBound_of_crossingVelocity_endpoint
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus s endpointLimit : ℝ}
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
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    {abelCoefficient : ℕ → ℝ} {abelCoefficientBound : ℝ}
    (habelCoefficientBound :
      RealSequenceBoundedBy abelCoefficient abelCoefficientBound)
    (abelF0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    (hEndpointPartialSums : Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N,
        platformAbelEndpointSequence abelCoefficient n)
      atTop (nhds (endpointLimit - abelF0)))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hboundaryVelocity :
      platformBoundaryExteriorVariation platformA xMinus xPlus
          sigmaMinus sigmaPlus abelF0 abelCoefficient =
        platformReferenceCrossingWidthMaterialVelocity
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold xMinus xPlus)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        platformBoundaryExteriorVariation platformA xMinus xPlus
            sigmaMinus sigmaPlus abelF0 abelCoefficient +
          endpointAdjointGamma (platformRadius platformA)
            sigmaMinus sigmaPlus (platformRho platformA xMinus)
              (platformRho platformA xPlus) * endpointLimit) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) (normalizedMainComponentWidth h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hlogBarrier : 0 < platformReferenceExteriorLogPotentialLimit
      C k platformA hk ha ha2 hthreshold s := by
    rw [← platformReferenceExteriorPotentialLimit_eq_logPotentialLimit
      C k platformA hk ha ha2 hthreshold hs]
    simpa only [C, k] using! hbarrier
  have hbaseValue :=
    two_mul_tsum_platformReferenceScaledLagrangeCoefficientLimit_eq_crossingWidth
      C k platformA hk ha ha1 ha2 hthreshold hxPlusS hs hsa
        (by simpa only [C, k] using! hbarrier)
        (by simpa only [C, k] using! hminus)
        (by simpa only [C, k] using! hplus)
  have hdirectionalCrossing :=
    two_mul_tsum_platformReferenceScaledLagrangeCoefficientDirectionalLimit_eq_crossingVelocity
      C k platformA hk ha ha1 ha2 hthreshold hxPlusS hs hsa
        (by simpa only [C, k] using! hbarrier)
        (by simpa only [C, k] using! hminus)
        (by simpa only [C, k] using! hplus)
        (by simpa only [C, k] using! hminusDerivative)
        (by simpa only [C, k] using! hplusDerivative)
  have hdirectionalValue :
      2 * ∑' j,
          platformReferenceScaledLagrangeCoefficientDirectionalLimit
            C k platformA hk ha ha2 hthreshold (2 * j + 1) =
        platformBoundaryExteriorVariation platformA xMinus xPlus
          sigmaMinus sigmaPlus abelF0 abelCoefficient := by
    rw [hdirectionalCrossing]
    simpa only [C, k] using! hboundaryVelocity.symm
  apply h.normalized_platformResidualSupportingBound_of_concreteSeries_endpoint
    (platformA := platformA) (xMinus := xMinus) (xPlus := xPlus)
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus) (s := s)
    (endpointLimit := endpointLimit)
    (abelCoefficient := abelCoefficient)
    (abelCoefficientBound := abelCoefficientBound) (abelF0 := abelF0)
    (lambda := lambda)
    hres hk ha ha2 hthreshold (lt_trans hminus.1 ha) hplus.2.1
      hsigmaMinus hsigmaPlus hs hsa hlogBarrier
  · simpa only [C, k] using! hbaseValue
  · exact habelCoefficientBound
  · exact hlambda
  · exact hEndpointPartialSums
  · exact hEndpointNonpos
  · simpa only [C, k] using! hdirectionalValue
  · simpa only [C, k] using! hBlockPairing

/-- Fully concrete endpoint-corrected adapter.  The Abel coefficient is the
cosine sequence of the residual material field, the endpoint limit is its
one-sided value at `pi`, and the adjoint masses are the reciprocal crossing
slopes.  Thus coefficient boundedness, endpoint convergence/sign, both
continuum series values, and the material-velocity identification are all
automatic. -/
theorem normalized_platformResidualSupportingBound_of_canonicalMaterialCrossingVelocity_endpoint
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
    (hsigmaMinus : 0 ≤
      platformReferenceNegativeCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xMinus)
    (hsigmaPlus : 0 ≤
      platformReferencePositiveCrossingAdjointWeight
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold xPlus)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm
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
          hk ha ha2 hthreshold i ≤
        platformBoundaryExteriorVariation platformA xMinus xPlus
            (platformReferenceNegativeCrossingAdjointWeight
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) platformA
              hk ha ha2 hthreshold xMinus)
            (platformReferencePositiveCrossingAdjointWeight
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) platformA
              hk ha ha2 hthreshold xPlus)
            (platformResidualMaterialMean
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) platformA
              hk ha ha2 hthreshold)
            (platformResidualMaterialCosineCoefficient
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) platformA
              hk ha ha2 hthreshold) +
          endpointAdjointGamma (platformRadius platformA)
              (platformReferenceNegativeCrossingAdjointWeight
                (h.normalizedResidualConfiguration hres)
                (normalizedEndpointResidualRatio h) platformA
                hk ha ha2 hthreshold xMinus)
              (platformReferencePositiveCrossingAdjointWeight
                (h.normalizedResidualConfiguration hres)
                (normalizedEndpointResidualRatio h) platformA
                hk ha ha2 hthreshold xPlus)
              (platformRho platformA xMinus) (platformRho platformA xPlus) *
            platformResidualMaterialField
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) platformA
              hk ha ha2 hthreshold Real.pi) :
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
  let coefficient := platformResidualMaterialCosineCoefficient
    C k platformA hk ha ha2 hthreshold
  let f0 := platformResidualMaterialMean C k platformA
    hk ha ha2 hthreshold
  let endpointLimit := platformResidualMaterialField C k platformA
    hk ha ha2 hthreshold Real.pi
  have hblocksBoundary :=
    platformResidualTangentBlockSum_le_boundaryExterior_of_endpoint_limit
      C hk ha ha2 hthreshold (lt_trans hminus.1 ha) hplus.2.1
      (by simpa only [C, k, sigmaMinus] using! hsigmaMinus)
      (by simpa only [C, k, sigmaPlus] using! hsigmaPlus)
      (platformResidualMaterialCosineCoefficient_bounded
        C k platformA hk ha ha2 hthreshold)
      f0 canonicalAbelParameter_isInteriorApproach
      (by
        simpa only [coefficient, f0, endpointLimit] using!
          tendsto_platformResidualMaterialAbelEndpoint_canonical
            C k platformA hk ha ha2 hthreshold)
      (by
        simpa only [endpointLimit] using!
          platformResidualMaterialField_pi_nonpos
            C k platformA hk ha ha2 hthreshold)
      (by simpa only [C, k, sigmaMinus, sigmaPlus, coefficient, f0,
        endpointLimit] using! hBlockPairing)
  have hboundaryVelocity :=
    platformBoundaryExteriorVariation_material_eq_crossingWidthMaterialVelocity
      C k platformA hk ha ha2 hthreshold (lt_trans hminus.1 ha) hplus.2.1
      (by simpa only [C, k] using! hminusDerivative)
      (by simpa only [C, k] using! hplusDerivative)
  have hblocksVelocity :
      ∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        platformReferenceCrossingWidthMaterialVelocity C k platformA
          hk ha ha2 hthreshold xMinus xPlus := by
    rw [← hboundaryVelocity]
    simpa only [coefficient, f0] using! hblocksBoundary
  apply h.normalized_platformResidualSupportingBound_of_crossingVelocity
    hres hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier
      hminus hplus hminusDerivative hplusDerivative
  simpa only [C, k, sigmaMinus, sigmaPlus] using! hblocksVelocity

end EndpointNormalizationHypotheses

end

end Erdos1038
