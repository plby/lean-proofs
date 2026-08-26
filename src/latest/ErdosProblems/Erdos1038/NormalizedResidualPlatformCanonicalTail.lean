import ErdosProblems.Erdos1038.PlatformReferenceMomentLimits
import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalAnalytic

/-!
# Discarding coarse canonical platform meshes

Strict separation of the continuum reference produces positivity only on a
tail of the canonical left-Riemann meshes.  Finite-dimensional convexity
does not require the discarded coarse meshes.  This file shifts to that
tail and applies the arbitrary-positive-mesh support theorem, eliminating
the artificial requirement that every coarse canonical mesh be strictly
separated.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Canonical platform support when the discrete exterior potential is
eventually positive.  The reference and directional limits are stated for
the original sequence; shifting to the positive tail preserves both. -/
theorem normalized_platformResidualSupportingBound_of_canonicalEventuallyPositivePotential
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hs : 0 < s) (hsa : s < platformA)
    (hpotential : ∀ᶠ n in atTop,
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
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hpotential)
  let mesh : ℕ → ℕ := fun n ↦ N + n + 1
  let reference : ∀ n, NormalizedResidualIndex h × Fin (mesh n) → ℝ :=
    fun n ↦ platformResidualRefinementReference C k platformA
      hk ha ha2 hthreshold (N + n)
  have hmesh (n : ℕ) : 0 < mesh n := by
    simp only [mesh]
    omega
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have halpha (n : ℕ)
      (p : NormalizedResidualIndex h × Fin (mesh n)) :
      0 < refinedLagrangeWeight (mesh n)
        (residualLagrangeAlpha C k) p :=
    refinedLagrangeWeight_pos (hmesh n)
      (residualLagrangeAlpha_pos C hk0) p
  have href (n : ℕ) :
      reference n ∈
        positiveCoordinates (NormalizedResidualIndex h × Fin (mesh n)) := by
    simpa only [reference, mesh] using!
      platformResidualRefinementReference_mem_positiveCoordinates
        C k platformA hk ha ha2 hthreshold (N + n)
  have hweighted (n : ℕ) : Summable (fun degree : ℕ ↦
      ((degree : ℝ) + 1) *
        scaledLagrangeCoefficient
          (refinedLagrangeWeight (mesh n)
            (residualLagrangeAlpha C k)) degree (reference n)) := by
    let m := N + n
    have hpotentialM :
        0 < Real.log s +
          ∑ p,
            platformResidualRefinementAlpha C k m p *
              Real.log
                (platformResidualRefinementReference C k platformA
                  hk ha ha2 hthreshold m p - s) := by
      exact hN m (Nat.le_add_right N n)
    have hsd (p : NormalizedResidualIndex h × Fin (m + 1)) :
        s < platformResidualRefinementReference C k platformA
          hk ha ha2 hthreshold m p :=
      hsa.trans_le (platformResidualRefinementReference_mem_Icc
        C k platformA hk ha ha2 hthreshold m p).1
    have hstrict :=
      inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
        (platformResidualRefinementAlpha C k m)
        (platformResidualRefinementReference C k platformA
          hk ha ha2 hthreshold m)
        (platformResidualRefinementReference_mem_positiveCoordinates
          C k platformA hk ha ha2 hthreshold m)
        hs hsd hpotentialM
    simpa only [mesh, reference, m, platformResidualRefinementAlpha] using!
      summable_degreeWeight_scaledLagrangeCoefficient_of_lt_comparison
        (platformResidualRefinementAlpha C k m)
        (platformResidualRefinementReference C k platformA
          hk ha ha2 hthreshold m)
        (fun p ↦ refinedLagrangeWeight_pos (Nat.succ_pos m)
          (residualLagrangeAlpha_pos C hk0) p)
        (platformResidualRefinementReference_mem_positiveCoordinates
          C k platformA hk ha ha2 hthreshold m)
        hs hsd hstrict
  have hsumReference (n : ℕ) : Summable (fun degree : ℕ ↦
      scaledLagrangeCoefficient
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        degree (reference n)) :=
    summable_scaledLagrangeCoefficient_of_degreeWeight
      (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
      (reference n) (halpha n) (href n) (hweighted n)
  have hsumDirectional (n : ℕ) : Summable (fun j : ℕ ↦
      scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        (2 * j + 1) (reference n)
        (refinedCoordinates (mesh n) C.location)) := by
    apply summable_scaledLagrangeCoefficientDirectional_of_degreeWeight
      (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
      (reference n) (refinedCoordinates (mesh n) C.location)
      (halpha n) (href n) (B := 2 / platformA)
      (div_nonneg (by norm_num) ha.le)
    · simpa only [mesh, reference, platformResidualRefinementTarget,
        platformResidualRefinementAlpha] using!
        platformResidualRefinement_relativeDisplacement_le
          C hk ha ha2 hthreshold (N + n)
    · exact hweighted n
  have hshift : Tendsto (fun n : ℕ ↦ N + n) atTop atTop := by
    simpa only [Nat.add_comm] using! tendsto_add_atTop_nat N
  have hbaseShift : Tendsto
      (fun n ↦ inverseWidthSeries
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        (reference n)) atTop (nhds (xPlus - xMinus)) := by
    simpa only [mesh, reference, C, k,
      platformResidualRefinementAlpha] using! hbase.comp hshift
  have hdirectionalShift : Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (refinedLagrangeWeight (mesh n) (residualLagrangeAlpha C k))
        (reference n) (refinedCoordinates (mesh n) C.location))
      atTop (nhds D) := by
    simpa only [mesh, reference, C, k,
      platformResidualRefinementAlpha,
      platformResidualRefinementTarget] using! hdirectional.comp hshift
  apply h.normalized_platformResidualSupportingBound_of_variableProductRefinements
    hres hk ha ha2 hthreshold mesh hmesh reference href
    hsumReference hsumDirectional hbaseShift hdirectionalShift
  simpa only [C, k] using! hblocks

/-- Positive continuum exterior potential is the exact strict-reference
condition: actual canonical left-Riemann convergence supplies eventual
discrete positivity, and the preceding theorem discards the coarse meshes. -/
theorem normalized_platformResidualSupportingBound_of_positiveContinuumPotential
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {platformA xMinus xPlus sigmaMinus sigmaPlus D s : ℝ}
    (hk : 1 ≤ normalizedEndpointResidualRatio h)
    (ha : 0 < platformA) (ha2 : platformA < 2)
    (hthreshold : platformThreshold (normalizedEndpointResidualRatio h) ≤
      platformA)
    (hs : 0 < s) (hsa : s < platformA)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold s)
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
  apply h.normalized_platformResidualSupportingBound_of_canonicalEventuallyPositivePotential
    hres hk ha ha2 hthreshold hs hsa
  · exact eventually_platformResidualRefinement_exteriorLogPotential_pos
      (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) platformA
      hk ha ha2 hthreshold hsa hlimit
  · exact hbase
  · exact hdirectional
  · exact hblocks

end EndpointNormalizationHypotheses

end

end Erdos1038
