import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalSupport
import ErdosProblems.Erdos1038.ResidualWidthStrictReference

/-!
# Canonical platform support from strict finite-reference comparison

For canonical platform samples, both the reference and target coordinates
lie in a fixed positive compact interval.  Hence the relative material
displacement is uniformly bounded.  A strict positive inverse-branch
comparison at each mesh therefore supplies all coefficient summability
premises in the canonical support theorem automatically.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set Polynomial Filter Topology

namespace Erdos1038

noncomputable section

lemma platformResidualRefinement_relativeDisplacement_le
    {iota : Type*} [Fintype iota] [LinearOrder iota]
    (C : ResidualConfiguration iota)
    {k a : ℝ} (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    |(platformResidualRefinementTarget C n p -
          platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n p) /
        platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n p| ≤
      2 / a := by
  let reference := platformResidualRefinementReference C k a
    hk ha ha2 hthreshold n p
  let target := platformResidualRefinementTarget C n p
  have href := platformResidualRefinementReference_mem_Icc
    C k a hk ha ha2 hthreshold n p
  have htarget : target ∈ Icc (1 : ℝ) 2 := by
    simpa only [target, platformResidualRefinementTarget,
      refinedCoordinates] using! C.location_mem p.1
  have hrefPos : 0 < reference := ha.trans_le href.1
  have hdiff : |target - reference| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [htarget.1, htarget.2, href.1, href.2]
  change |(target - reference) / reference| ≤ 2 / a
  rw [abs_div, abs_of_pos hrefPos]
  calc
    |target - reference| / reference ≤ 2 / reference :=
      div_le_div_of_nonneg_right hdiff hrefPos.le
    _ ≤ 2 / a :=
      div_le_div_of_nonneg_left (by norm_num) ha href.1

/-- Product-refinement sums are weighted left Riemann sums on each target
mass block. -/
theorem sum_platformResidualRefinementAlpha_mul
    {iota : Type*} [Fintype iota]
    (C : ResidualConfiguration iota) (k : ℝ) (n : ℕ)
    (F : iota × Fin (n + 1) → ℝ) :
    (∑ p, platformResidualRefinementAlpha C k n p * F p) =
      ∑ i, residualLagrangeAlpha C k i *
        ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ j : Fin (n + 1), F (i, j)) := by
  classical
  unfold platformResidualRefinementAlpha refinedLagrangeWeight
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    (∑ y, residualLagrangeAlpha C k (i, y).1 /
          ((n + 1 : ℕ) : ℝ) * F (i, y)) =
        ∑ y, (residualLagrangeAlpha C k i /
          ((n + 1 : ℕ) : ℝ)) * F (i, y) := by rfl
    _ = (residualLagrangeAlpha C k i / ((n + 1 : ℕ) : ℝ)) *
        ∑ y, F (i, y) := by
      symm
      exact Finset.mul_sum _ _ _
    _ = residualLagrangeAlpha C k i *
        ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ j, F (i, j)) := by ring

/-- Product-refinement support with an arbitrary positive mesh size.  This
allows the canonical approximation to discard finitely many coarse meshes
once strict reference separation has been proved on a tail. -/
theorem platformResidualSupportingBound_of_variableProductRefinements
    {iota : Type*} [Fintype iota] [LinearOrder iota]
    (C : ResidualConfiguration iota)
    {k platformA xMinus xPlus sigmaMinus sigmaPlus M0 D : ℝ}
    (hk : 1 ≤ k) (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold k ≤ platformA)
    (mesh : ℕ → ℕ) (hmesh : ∀ n, 0 < mesh n)
    (reference : ∀ n, iota × Fin (mesh n) → ℝ)
    (href : ∀ n, reference n ∈ positiveCoordinates (iota × Fin (mesh n)))
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        degree (reference n)))
    (hsumTarget : Summable (fun degree ↦
      scaledLagrangeCoefficient (residualLagrangeAlpha C k)
        degree C.location))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        (2 * j + 1) (reference n)
        (refinedCoordinates (mesh n) C.location)))
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        (reference n)) atTop (nhds M0))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        (reference n) (refinedCoordinates (mesh n) C.location))
      atTop (nhds D))
    (hblocks :
      ∑ i, platformResidualTangentBlockTerm C k platformA
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤ D) :
    PlatformResidualSupportingBound C k platformA
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold M0
      (inverseWidthSeries (residualLagrangeAlpha C k) C.location) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  apply
    EndpointNormalizationHypotheses.platformResidualSupportingBound_of_inverseSeries_refinements C
    hk ha ha2 hthreshold
    (fun n ↦ iota × Fin (mesh n))
    (fun n ↦ refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
    reference
    (fun n ↦ refinedCoordinates (mesh n) C.location)
    (fun n p ↦ refinedLagrangeWeight_pos (hmesh n)
      (residualLagrangeAlpha_pos C hk0) p)
    href
    (fun n ↦ refinedCoordinates_mem_positiveCoordinates
      (residual_locations_mem_positiveCoordinates C))
    hsumReference
    (fun n ↦
      (summable_scaledLagrangeCoefficient_refined_iff
        (hmesh n) (residualLagrangeAlpha C k) C.location
        (residual_locations_mem_positiveCoordinates C)).2
          hsumTarget)
    hsumDirectional
  · intro n
    exact inverseWidthSeries_refined (hmesh n)
      (residualLagrangeAlpha C k) C.location
      (residual_locations_mem_positiveCoordinates C)
  · exact hbase
  · exact hdirectional
  · exact hblocks

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Normalized variable-mesh wrapper.  Endpoint separation supplies the
target-side series, while the reference may start at any positive mesh. -/
theorem normalized_platformResidualSupportingBound_of_variableProductRefinements
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus M0 D : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (mesh : ℕ → ℕ) (hmesh : ∀ n, 0 < mesh n)
    (reference : ∀ n, NormalizedResidualIndex h × Fin (mesh n) → ℝ)
    (href : ∀ n, reference n ∈
      positiveCoordinates (NormalizedResidualIndex h × Fin (mesh n)))
    (hsumReference : ∀ n, Summable (fun degree ↦
      scaledLagrangeCoefficient
        (refinedLagrangeWeight (mesh n)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))) degree (reference n)))
    (hsumDirectional : ∀ n, Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight (mesh n)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))) (2 * j + 1)
        (reference n)
        (refinedCoordinates (mesh n)
          (h.normalizedResidualConfiguration hres).location)))
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (refinedLagrangeWeight (mesh n)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h))) (reference n))
      atTop (nhds M0))
    (hdirectional : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (refinedLagrangeWeight (mesh n)
          (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h)))
        (reference n)
        (refinedCoordinates (mesh n)
          (h.normalizedResidualConfiguration hres).location))
      atTop (nhds D))
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
  exact platformResidualSupportingBound_of_variableProductRefinements
    (h.normalizedResidualConfiguration hres) hk ha ha2 hthreshold
    mesh hmesh reference href hsumReference
    (h.summable_normalized_scaledLagrangeCoefficient hres)
    hsumDirectional hbase hdirectional hblocks

/-- Canonical crossing-reference supporting bound with both summability
families discharged by a strict inverse-branch comparison at each mesh.
The remaining limit premises now state only the two actual continuum
limits and the analytic block estimate. -/
theorem normalized_platformResidualSupportingBound_of_canonicalStrictComparison
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hcomparison : ∀ n, ∃ s : ℝ,
      0 < s ∧
      (∀ p, s <
        platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n p) ∧
      inverseMonomial
          (platformResidualRefinementAlpha
            (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h) n)
          (platformResidualRefinementReference
            (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h) platformA
            hk ha ha2 hthreshold n) <
        s / lagrangePhiValue
          (platformResidualRefinementAlpha
            (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h) n)
          (platformResidualRefinementReference
            (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h) platformA
            hk ha ha2 hthreshold n) s)
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n))
      atTop (nhds (xPlus - xMinus)))
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
      atTop (nhds D))
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
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have halpha (n : ℕ) (p : NormalizedResidualIndex h × Fin (n + 1)) :
      0 < platformResidualRefinementAlpha C k n p := by
    exact refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C hk0) p
  have href (n : ℕ) :
      platformResidualRefinementReference C k platformA
          hk ha ha2 hthreshold n ∈
        positiveCoordinates (NormalizedResidualIndex h × Fin (n + 1)) :=
    platformResidualRefinementReference_mem_positiveCoordinates
      C k platformA hk ha ha2 hthreshold n
  have hweighted (n : ℕ) : Summable (fun degree : ℕ ↦
      ((degree : ℝ) + 1) *
        scaledLagrangeCoefficient
          (platformResidualRefinementAlpha C k n) degree
          (platformResidualRefinementReference C k platformA
            hk ha ha2 hthreshold n)) := by
    obtain ⟨s, hs, hsd, hstrict⟩ := hcomparison n
    exact summable_degreeWeight_scaledLagrangeCoefficient_of_lt_comparison
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k platformA
        hk ha ha2 hthreshold n)
      (halpha n) (href n) hs hsd hstrict
  have hsumReference (n : ℕ) : Summable (fun degree : ℕ ↦
      scaledLagrangeCoefficient
        (platformResidualRefinementAlpha C k n) degree
        (platformResidualRefinementReference C k platformA
          hk ha ha2 hthreshold n)) :=
    summable_scaledLagrangeCoefficient_of_degreeWeight
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k platformA
        hk ha ha2 hthreshold n)
      (halpha n) (href n) (hweighted n)
  have hsumDirectional (n : ℕ) : Summable (fun j : ℕ ↦
      scaledLagrangeCoefficientDirectional
        (platformResidualRefinementAlpha C k n) (2 * j + 1)
        (platformResidualRefinementReference C k platformA
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n)) := by
    apply summable_scaledLagrangeCoefficientDirectional_of_degreeWeight
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k platformA
        hk ha ha2 hthreshold n)
      (platformResidualRefinementTarget C n)
      (halpha n) (href n) (B := 2 / platformA)
      (div_nonneg (by norm_num) ha.le)
    · exact platformResidualRefinement_relativeDisplacement_le
        C hk ha ha2 hthreshold n
    · exact hweighted n
  exact h.normalized_platformResidualSupportingBound_of_canonicalCrossingRefinement
    hres hk ha ha2 hthreshold
    (by simpa only [C, k] using! hsumReference)
    (by simpa only [C, k] using! hsumDirectional)
    (by simpa only [C, k] using! hbase)
    (by simpa only [C, k] using! hdirectional)
    (by simpa only [C, k] using! hblocks)

/-- Riemann-sum form of the canonical criterion.  Positivity of the
discrete exterior logarithmic potential supplies the strict comparison and
hence both series-summability conclusions. -/
theorem normalized_platformResidualSupportingBound_of_canonicalPositivePotential
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
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
    (hbase : Tendsto
      (fun n ↦ inverseWidthSeries
        (platformResidualRefinementAlpha
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) n)
        (platformResidualRefinementReference
          (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) platformA
          hk ha ha2 hthreshold n))
      atTop (nhds (xPlus - xMinus)))
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
      atTop (nhds D))
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
  apply h.normalized_platformResidualSupportingBound_of_canonicalStrictComparison
    hres hk ha ha2 hthreshold
  · intro n
    refine ⟨s, hs, hsd n, ?_⟩
    apply inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
    · exact platformResidualRefinementReference_mem_positiveCoordinates
        (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) platformA
        hk ha ha2 hthreshold n
    · exact hs
    · exact hsd n
    · exact hpotential n
  · exact hbase
  · exact hdirectional
  · exact hblocks

end EndpointNormalizationHypotheses

end

end Erdos1038
