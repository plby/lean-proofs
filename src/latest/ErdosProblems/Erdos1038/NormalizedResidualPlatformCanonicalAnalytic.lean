import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalStrict
import ErdosProblems.Erdos1038.ResidualWidthSeriesLimits
import ErdosProblems.Erdos1038.PlatformAdjointAbelBoundary
import ErdosProblems.Erdos1038.PlatformAdjointAbelExteriorLimit
import ErdosProblems.Erdos1038.PlatformAdjointAbelEndpointLimit

/-!
# Canonical platform support from analytic convergence certificates

This file joins the three analytic interfaces used by the manuscript's
canonical platform argument.  Tannery certificates give the reference
width and material-direction limits, while the endpoint-corrected Abel
identity bounds the block tangent sum by that directional limit.

The resulting theorem has no intermediate `hbase`, `hdirectional`, or
`hblocks` hypotheses.  Its remaining assumptions are the primitive
coefficientwise/dominated convergence facts and the three atomic Abel
limits, together with the direct block-to-pairing tangent estimate.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- The endpoint-corrected Abel boundary theorem turns a direct
block-to-pairing tangent estimate into the block-to-directional estimate
needed by `PlatformResidualSupportingBound`. -/
theorem platformResidualTangentBlockSum_le_exterior_of_abel_limits
    (C : ResidualConfiguration iota)
    {k a xMinus xPlus sigmaMinus sigmaPlus D pairingLimit endpointLimit : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    {coefficient : ℕ → ℝ} {coefficientBound : ℝ}
    (hcoefficientBound : RealSequenceBoundedBy coefficient coefficientBound)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    (hExterior : Tendsto
      (fun n ↦ platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient (lambda n))
      atTop (nhds D))
    (hPairing : Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient (lambda n) theta))
      atTop (nhds pairingLimit))
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        pairingLimit) :
    ∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D := by
  exact hBlockPairing.trans
    (platformAdjointPairing_le_exterior_of_abel_limits
      hxMinus hxPlus ha2 hsigmaMinus hsigmaPlus hcoefficientBound f0
      hlambda hExterior hPairing hEndpoint hEndpointNonpos)

/-- Reduced Abel interface: the pairing convergence is generated
automatically by the endpoint-corrected identity, so only the exterior and
endpoint limits remain analytic inputs. -/
theorem platformResidualTangentBlockSum_le_exterior_of_exterior_endpoint_limits
    (C : ResidualConfiguration iota)
    {k a xMinus xPlus sigmaMinus sigmaPlus D endpointLimit : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    {coefficient : ℕ → ℝ} {coefficientBound : ℝ}
    (hcoefficientBound : RealSequenceBoundedBy coefficient coefficientBound)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    (hExterior : Tendsto
      (fun n ↦ platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient (lambda n))
      atTop (nhds D))
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        D + endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * endpointLimit) :
    ∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D := by
  apply platformResidualTangentBlockSum_le_exterior_of_abel_limits
    C hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hcoefficientBound f0 hlambda hExterior
      (tendsto_platformAdjointPairing_of_exterior_endpoint_abel_limits
        hxMinus hxPlus ha2 hcoefficientBound f0 hlambda
        hExterior hEndpoint)
      hEndpoint hEndpointNonpos
  exact hBlockPairing

/-- Fully automatic exterior-limit specialization.  The limit is the
absolutely convergent boundary coefficient series, so only the endpoint
limit and the concrete block-to-pairing estimate remain. -/
theorem platformResidualTangentBlockSum_le_boundaryExterior_of_endpoint_limit
    (C : ResidualConfiguration iota)
    {k a xMinus xPlus sigmaMinus sigmaPlus endpointLimit : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    {coefficient : ℕ → ℝ} {coefficientBound : ℝ}
    (hcoefficientBound : RealSequenceBoundedBy coefficient coefficientBound)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        platformBoundaryExteriorVariation a xMinus xPlus
            sigmaMinus sigmaPlus f0 coefficient +
          endpointAdjointGamma (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) * endpointLimit) :
    ∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
      platformBoundaryExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient := by
  apply platformResidualTangentBlockSum_le_exterior_of_exterior_endpoint_limits
    C hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hcoefficientBound f0 hlambda
      (tendsto_platformAbelExteriorVariation_boundary
        hxMinus hxPlus ha2 hcoefficientBound f0 hlambda)
      hEndpoint hEndpointNonpos
  exact hBlockPairing

/-- Abel's endpoint theorem discharges the endpoint-limit premise from
ordinary convergence of the full signed endpoint partial sums.  Together
with the automatic exterior limit, this leaves only the concrete endpoint
sum/sign and block-tangent estimates. -/
theorem platformResidualTangentBlockSum_le_boundaryExterior_of_endpoint_partialSums
    (C : ResidualConfiguration iota)
    {k a xMinus xPlus sigmaMinus sigmaPlus endpointLimit : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    {coefficient : ℕ → ℝ} {coefficientBound : ℝ}
    (hcoefficientBound : RealSequenceBoundedBy coefficient coefficientBound)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    (hEndpointPartialSums : Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N,
        platformAbelEndpointSequence coefficient n)
      atTop (nhds (endpointLimit - f0)))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        platformBoundaryExteriorVariation a xMinus xPlus
            sigmaMinus sigmaPlus f0 coefficient +
          endpointAdjointGamma (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) * endpointLimit) :
    ∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
      platformBoundaryExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient := by
  apply platformResidualTangentBlockSum_le_boundaryExterior_of_endpoint_limit
    C hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hcoefficientBound f0 hlambda
      (tendsto_platformAbelEndpointSeriesValue_of_partialSums
        hcoefficientBound hEndpointPartialSums hlambda)
      hEndpointNonpos
  exact hBlockPairing

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Fully joined canonical platform theorem.  Fixed-degree convergence and
uniform summable majorants pass both inverse-width series through the
canonical refinement limit.  The endpoint-corrected Abel identity then
passes the direct block tangent estimate to the same directional limit.

Thus every premise below is a primitive analytic fact about the canonical
reference quantile or its atomic velocity; the three intermediate support
premises have been eliminated. -/
theorem normalized_platformResidualSupportingBound_of_canonicalAnalyticCertificates
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hxMinus : xMinus < platformA) (hxPlus : xPlus < platformA)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    (hs : 0 < s)
    (hsd : ∀ n p, s <
      platformResidualRefinementReference
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold n p)
    (hpotential : ∀ n,
      0 < Real.log s +
        ∑ p,
          platformResidualRefinementAlpha
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) n p *
            Real.log
              (platformResidualRefinementReference
                  (h.normalizedResidualConfiguration hres)
                  (normalizedEndpointResidualRatio h) platformA
                  hk ha ha2 hthreshold n p - s))
    (baseLimitCoefficient baseMajorant : ℕ → ℝ)
    (hbaseMajorant : Summable baseMajorant)
    (hbaseCoefficient : ∀ j, Tendsto
      (fun n ↦ scaledLagrangeCoefficient
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (2 * j + 1)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n))
      atTop (nhds (baseLimitCoefficient j)))
    (hbaseDominated : ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficient
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (2 * j + 1)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)‖ ≤ baseMajorant j)
    (hbaseValue : 2 * ∑' j, baseLimitCoefficient j = xPlus - xMinus)
    (directionalLimitCoefficient directionalMajorant : ℕ → ℝ)
    (hdirectionalMajorant : Summable directionalMajorant)
    (hdirectionalCoefficient : ∀ j, Tendsto
      (fun n ↦ scaledLagrangeCoefficientDirectional
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (2 * j + 1)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget
          (h.normalizedResidualConfiguration hres) n))
      atTop (nhds (directionalLimitCoefficient j)))
    (hdirectionalDominated : ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficientDirectional
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (2 * j + 1)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget
          (h.normalizedResidualConfiguration hres) n)‖ ≤
        directionalMajorant j)
    (hdirectionalValue : 2 * ∑' j, directionalLimitCoefficient j = D)
    {abelCoefficient : ℕ → ℝ} {abelCoefficientBound : ℝ}
    (habelCoefficientBound :
      RealSequenceBoundedBy abelCoefficient abelCoefficientBound)
    (abelF0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    {pairingLimit endpointLimit : ℝ}
    (hExterior : Tendsto
      (fun n ↦ platformAbelExteriorVariation platformA xMinus xPlus
        sigmaMinus sigmaPlus abelF0 abelCoefficient (lambda n))
      atTop (nhds D))
    (hPairing : Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              platformA xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius platformA)
              abelCoefficient (lambda n) theta))
      atTop (nhds pairingLimit))
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        abelF0 abelCoefficient (lambda n))
      atTop (nhds endpointLimit))
    (hEndpointNonpos : endpointLimit ≤ 0)
    (hBlockPairing :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        pairingLimit) :
    PlatformResidualSupportingBound
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) (normalizedMainComponentWidth h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hbase := tendsto_inverseWidthSeries_of_dominated_coefficients_eq
    (fun n ↦ NormalizedResidualIndex h × Fin (n + 1))
    (fun n ↦ platformResidualRefinementAlpha C k n)
    (fun n ↦ platformResidualRefinementReference C k platformA
      hk ha ha2 hthreshold n)
    baseLimitCoefficient baseMajorant hbaseMajorant
    (by simpa only [C, k] using! hbaseCoefficient)
    (by simpa only [C, k] using! hbaseDominated)
    hbaseValue
  have hdirectional :=
    tendsto_inverseWidthSeriesDirectional_of_dominated_coefficients_eq
      (fun n ↦ NormalizedResidualIndex h × Fin (n + 1))
      (fun n ↦ platformResidualRefinementAlpha C k n)
      (fun n ↦ platformResidualRefinementReference C k platformA
        hk ha ha2 hthreshold n)
      (fun n ↦ platformResidualRefinementTarget C n)
      directionalLimitCoefficient directionalMajorant hdirectionalMajorant
      (by simpa only [C, k] using! hdirectionalCoefficient)
      (by simpa only [C, k] using! hdirectionalDominated)
      hdirectionalValue
  have hblocks :
      ∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D := by
    apply platformResidualTangentBlockSum_le_exterior_of_abel_limits
      C hk ha ha2 hthreshold hxMinus hxPlus
      hsigmaMinus hsigmaPlus habelCoefficientBound abelF0 hlambda
      hExterior hPairing hEndpoint hEndpointNonpos
    simpa only [C, k] using! hBlockPairing
  apply h.normalized_platformResidualSupportingBound_of_canonicalPositivePotential
    hres hk ha ha2 hthreshold hs hsd hpotential
  · simpa only [C, k] using! hbase
  · simpa only [C, k] using! hdirectional
  · simpa only [C, k] using! hblocks

end EndpointNormalizationHypotheses

end

end Erdos1038
