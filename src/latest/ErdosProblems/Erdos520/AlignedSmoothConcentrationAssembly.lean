import ErdosProblems.Erdos520.AlignedConcentrationAssembly
import ErdosProblems.Erdos520.AlignedSmoothContribution

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Removing the smooth hypothesis from aligned concentration

The smooth contribution has now been proved unconditionally on the aligned
mesh.  These wrappers insert it into `AlignedConcentrationAssembly`, leaving
only the repaired quadratic-variation inputs (or their granular components).
-/

/-- Largest-prime concentration plus the unconditional aligned smooth bound
gives the complete test-point estimate. -/
theorem aeTestPointBound_partialSum_aligned_of_qv
    {C η : ℝ} {K m : ℕ}
    (hC : 0 < C) (hη : 0 < η) (hK : 2 ≤ K) (hm : 0 < m)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        largestPrimeQuadraticVariation omega
            (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K ell 0)
            (alignedRootExpTestPoint m i) ≤
          alignedLargestPrimeQvThreshold C K m ell i) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  have ha : ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        alignedThinEndpoint K ell 0 ≤ alignedRootExpTestPoint m i := by
    filter_upwards with ell
    intro i hi
    exact (alignedThinInitial_lt_testPoint_of_mem hi).le
  have hsmooth : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K ell 0)| ≤
          alignedLargestPrimeThreshold 1 η m ell i := by
    have h := ae_eventually_smoothContribution_alignedRootExpTests
      (K := K) (m := m) hK hη
    simpa only [alignedLargestPrimeThreshold, one_mul] using! h
  exact aeTestPointBound_partialSum_aligned_of_smooth_qv
    (fun ell => alignedThinEndpoint K ell 0)
    (by norm_num) hC hη (by omega) hm hgap ha hsmooth hqv

/-- The same endpoint for the total clamped cutoff. -/
theorem aeTestPointBound_partialSum_clampedAligned_of_qv
    (S : ℕ) {C η : ℝ} {K m : ℕ}
    (hC : 0 < C) (hη : 0 < η) (hK : 2 ≤ K) (hm : 0 < m)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        largestPrimeQuadraticVariation omega
            (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K (clampedAlignedScale S ell) 0)
            (alignedRootExpTestPoint m i) ≤
          alignedLargestPrimeQvThreshold C K m ell i) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  have ha : ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        alignedThinEndpoint K (clampedAlignedScale S ell) 0 ≤
          alignedRootExpTestPoint m i := by
    filter_upwards [eventually_clampedAlignedScale_eq S] with ell hscale
    intro i hi
    rw [hscale]
    exact (alignedThinInitial_lt_testPoint_of_mem hi).le
  have hsmooth : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K (clampedAlignedScale S ell) 0)| ≤
          alignedLargestPrimeThreshold 1 η m ell i := by
    have h := ae_eventually_smoothContribution_clampedAlignedRootExpTests
      S (K := K) (m := m) hK hη
    simpa only [alignedLargestPrimeThreshold, one_mul] using! h
  exact aeTestPointBound_partialSum_aligned_of_smooth_qv
    (fun ell => alignedThinEndpoint K (clampedAlignedScale S ell) 0)
    (by norm_num) hC hη (by omega) hm hgap ha hsmooth hqv

/-- Granular clamped-scale endpoint: after the deterministic smoothing
inequality, repaired block maximum, and auxiliary remainder bounds are
provided, the smooth contribution requires no further premise. -/
theorem aeTestPointBound_partialSum_clampedAligned_of_components
    (S : ℕ) {D B η : ℝ} {K m : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ)
    (hD : 0 < D) (hB : 0 < B) (hη : 0 < η)
    (hK : 2 ≤ K) (hm : 0 < m)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale
        (alignedRootExpTests K m)
        (fun _ell i => alignedRootExpTestPoint m i)
        (fun ell _i =>
          alignedThinEndpoint K (clampedAlignedScale S ell) 0)
        (fun _ell i => alignedRootExpTestPoint m i)
        J U E D ell omega)
    (hblock : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale J U B K ell omega)
    (haux : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m) E B K ell omega) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  have ha : ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        alignedThinEndpoint K (clampedAlignedScale S ell) 0 ≤
          alignedRootExpTestPoint m i := by
    filter_upwards [eventually_clampedAlignedScale_eq S] with ell hscale
    intro i hi
    rw [hscale]
    exact (alignedThinInitial_lt_testPoint_of_mem hi).le
  have hsmooth : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K (clampedAlignedScale S ell) 0)| ≤
          alignedLargestPrimeThreshold 1 η m ell i := by
    have h := ae_eventually_smoothContribution_clampedAlignedRootExpTests
      S (K := K) (m := m) hK hη
    simpa only [alignedLargestPrimeThreshold, one_mul] using! h
  exact aeTestPointBound_partialSum_aligned_of_components
    (fun ell => alignedThinEndpoint K (clampedAlignedScale S ell) 0)
    J U E (by norm_num) hD hB hη (by omega) hm hgap
    ha hsmooth hsmoothing hblock haux

end Problem520
end Erdos
