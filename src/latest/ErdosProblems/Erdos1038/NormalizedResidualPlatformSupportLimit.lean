import ErdosProblems.Erdos1038.NormalizedResidualPlatformSupport
import ErdosProblems.Erdos1038.ResidualWidthRefinement

/-!
# Refinement-limit form of normalized platform support

The constant-platform reference is a continuous probability measure.  It is
therefore reached in the convex inverse-series argument by finite common-mass
refinements, rather than by one coordinate vector indexed by the distinct
target atoms.  This file records the exact limit passage needed for that
argument.

It also records the correct one-sided finite bridge.  The canonical block
term is obtained after applying the logarithmic tangent inequality inside
each target block, so its sum need only be bounded above by the inverse-series
directional derivative; equality is neither needed nor asserted.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set Polynomial Filter Topology

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Correct one-sided version of the finite-coordinate platform bridge. -/
theorem normalized_platformResidualSupportingBound_of_inverseSeries_le
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
    (hM0 : M0 ≤ inverseWidthSeries
      (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)) reference)
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
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
  have hinverse :=
    h.inverseWidthSeries_add_directional_le_normalizedMainComponentWidth
      hres href hsumReference hsumDirectional
  linarith

/-- A closed supporting inequality survives a common-refinement limit. -/
theorem platformResidualSupportingBound_of_refinement_tendsto
    {iota : Type*} [Fintype iota] [LinearOrder iota]
    (C : ResidualConfiguration iota)
    {k platformA xMinus xPlus sigmaMinus sigmaPlus M0 targetWidth D : ℝ}
    (hk : 1 ≤ k) (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold k ≤ platformA)
    {base directional : ℕ → ℝ}
    (hbase : Tendsto base atTop (𝓝 M0))
    (hdirectional : Tendsto directional atTop (𝓝 D))
    (hfinite : ∀ n, base n + directional n ≤ targetWidth)
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D) :
    PlatformResidualSupportingBound C k platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth := by
  have hlimit : M0 + D ≤ targetWidth :=
    le_of_tendsto' (hbase.add hdirectional) hfinite
  unfold PlatformResidualSupportingBound
  linarith

/-- Fully expanded finite-refinement criterion.  The coordinate type may
change with the mesh.  Each mesh uses the already-proved finite convex
support theorem, while only the two reference-side expressions are passed
to the limit.

For the manuscript's application, `target n` repeats every atomic target
value on a common equal-mass refinement.  The remaining analytic bridge is
to construct those refinements and prove `hTargetWidth`, `hbase`,
`hdirectional`, and `hblocks`. -/
theorem platformResidualSupportingBound_of_inverseSeries_refinements
    {iota : Type*} [Fintype iota] [LinearOrder iota]
    (C : ResidualConfiguration iota)
    {k platformA xMinus xPlus sigmaMinus sigmaPlus M0 targetWidth D : ℝ}
    (hk : 1 ≤ k) (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold k ≤ platformA)
    (index : ℕ → Type*) [∀ n, Fintype (index n)]
    (alpha reference target : ∀ n, index n → ℝ)
    (halpha : ∀ n i, 0 < alpha n i)
    (href : ∀ n, reference n ∈ positiveCoordinates (index n))
    (htarget : ∀ n, target n ∈ positiveCoordinates (index n))
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient (alpha n) degree (reference n)))
    (hsumTarget : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient (alpha n) degree (target n)))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional (alpha n) (2 * j + 1)
        (reference n) (target n)))
    (hTargetWidth : ∀ n,
      inverseWidthSeries (alpha n) (target n) = targetWidth)
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries (alpha n) (reference n))
      atTop (𝓝 M0))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (alpha n) (reference n) (target n))
      atTop (𝓝 D))
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D) :
    PlatformResidualSupportingBound C k platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth := by
  apply platformResidualSupportingBound_of_refinement_tendsto C
    hk ha ha2 hthreshold hbase hdirectional
  · intro n
    rw [← hTargetWidth n]
    exact inverseWidthSeries_supporting_of_summable
      (alpha n) (halpha n) (href n) (htarget n)
      (hsumReference n) (hsumTarget n) (hsumDirectional n)
  · exact hblocks

/-- Product refinements repeat each target coordinate `n + 1` times.  The
target inverse width and its coefficient summability are then automatic:
only the genuinely new reference-side limits and the block estimate remain. -/
theorem platformResidualSupportingBound_of_product_refinements
    {iota : Type*} [Fintype iota] [LinearOrder iota]
    (C : ResidualConfiguration iota)
    {k platformA xMinus xPlus sigmaMinus sigmaPlus M0 D : ℝ}
    (hk : 1 ≤ k) (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold k ≤ platformA)
    (reference : ∀ n, iota × Fin (n + 1) → ℝ)
    (href : ∀ n,
      reference n ∈ positiveCoordinates (iota × Fin (n + 1)))
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient
        (refinedLagrangeWeight (n + 1) (residualLagrangeAlpha C k))
        degree (reference n)))
    (hsumTarget : Summable (fun degree ↦ scaledLagrangeCoefficient
      (residualLagrangeAlpha C k) degree C.location))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight (n + 1) (residualLagrangeAlpha C k))
        (2 * j + 1) (reference n)
        (refinedCoordinates (n + 1) C.location)))
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (refinedLagrangeWeight (n + 1) (residualLagrangeAlpha C k))
        (reference n)) atTop (𝓝 M0))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (refinedLagrangeWeight (n + 1) (residualLagrangeAlpha C k))
        (reference n) (refinedCoordinates (n + 1) C.location))
      atTop (𝓝 D))
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D) :
    PlatformResidualSupportingBound C k platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold M0
      (inverseWidthSeries (residualLagrangeAlpha C k) C.location) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  apply platformResidualSupportingBound_of_inverseSeries_refinements C
    hk ha ha2 hthreshold
    (fun n ↦ iota × Fin (n + 1))
    (fun n ↦ refinedLagrangeWeight (n + 1)
      (residualLagrangeAlpha C k))
    reference
    (fun n ↦ refinedCoordinates (n + 1) C.location)
    (fun n p ↦ refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C hk0) p)
    href
    (fun n ↦ refinedCoordinates_mem_positiveCoordinates
      (residual_locations_mem_positiveCoordinates C))
    hsumReference
    (fun n ↦
      (summable_scaledLagrangeCoefficient_refined_iff
        (Nat.succ_pos n) (residualLagrangeAlpha C k) C.location
        (residual_locations_mem_positiveCoordinates C)).2 hsumTarget)
    hsumDirectional
  · intro n
    exact inverseWidthSeries_refined (Nat.succ_pos n)
      (residualLagrangeAlpha C k) C.location
      (residual_locations_mem_positiveCoordinates C)
  · exact hbase
  · exact hdirectional
  · exact hblocks

/-- Normalized product-refinement bridge.  Endpoint separation supplies all
target-side convergence, and target refinement invariance identifies its
limit with the exact normalized main-component width. -/
theorem normalized_platformResidualSupportingBound_of_productRefinements
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus M0 D : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (reference : ∀ n,
      NormalizedResidualIndex h × Fin (n + 1) → ℝ)
    (href : ∀ n, reference n ∈ positiveCoordinates
      (NormalizedResidualIndex h × Fin (n + 1)))
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient
        (refinedLagrangeWeight (n + 1)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))) degree (reference n)))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight (n + 1)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))) (2 * j + 1)
        (reference n)
        (refinedCoordinates (n + 1)
          (h.normalizedResidualConfiguration hres).location)))
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (refinedLagrangeWeight (n + 1)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))) (reference n))
      atTop (𝓝 M0))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (refinedLagrangeWeight (n + 1)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h)))
        (reference n)
        (refinedCoordinates (n + 1)
          (h.normalizedResidualConfiguration hres).location))
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
  rw [h.normalizedMainComponentWidth_eq_inverseWidthSeries hres]
  exact platformResidualSupportingBound_of_product_refinements
    (h.normalizedResidualConfiguration hres) hk ha ha2 hthreshold
    reference href hsumReference
    (h.summable_normalized_scaledLagrangeCoefficient hres)
    hsumDirectional hbase hdirectional hblocks

end EndpointNormalizationHypotheses

end

end Erdos1038
