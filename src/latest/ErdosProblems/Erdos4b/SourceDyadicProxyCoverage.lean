/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicResidueCoverage
import ErdosProblems.Erdos4b.SourcePrimeIntervalRelativeCount
import ErdosProblems.Erdos4b.SourceProxyAllocationBounds

/-!
# Uniform constant coverage for intervals allocated by the exact proxy

The cofactor and endpoint factors cancel. This is the coverage input
for the later finite independent-residue covering argument.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem uniform_dyadicSourceProxyCoverage_lower
    {I : Type*} {K : ℕ} (hK : 0 < K) (S : Finset I)
    (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (a D J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hmain : 0 < sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)
    (hpinned : ∀ h : Fin K, 0 < sourcePinnedFirstVariationalIntegral S F h *
      sourcePinnedCompanionVariationalIntegral K G) :
    ∀ᶠ r in atTop, ∀ m p₀ A B N : ℕ, ∀ ρ : ℝ, Even m →
      DyadicPinnedSourceRange a D J δ r m p₀ A B →
      jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N →
      smoothFrontier r ≤ N →
      (∀ q ∈ auxiliaryPrimeInterval A B, ∀ h : Fin K,
        primorial (sourcePreSieveCutoff r) * h.val * q < p₀) →
      ρ * (D * intervalLength a r / m : ℕ) /
        (dyadicCompanionScale r * residualCofactorLocalProduct (smoothFrontier r) m) ≤
          (B : ℝ) - A →
      ρ * (∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h *
          sourcePinnedCompanionVariationalIntegral K G) /
        (16 * (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)) ≤
        dyadicSourceResidueCoverage S F G a D r m p₀ A B N := by
  have hcoverage := uniform_dyadicSourceResidueCoverage_lower hK S F G hFcompact hFsmooth
    hGcompact hGsmooth hFsimplex hFceiling hGsupport a D J hδ hmain hpinned
  have hcount := (tendsto_dyadicPrimaryFrontier_atTop a).eventually
    (eventually_primeInterval_card_ge_half_length J hδ)
  filter_upwards [hcoverage, hcount, eventually_ge_atTop 1] with r hcov hprime hr
  intro m p₀ A B N ρ heven hdata hN hYN hmargin hlength
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  have hT : (0 : ℝ) < (D * intervalLength a r / m : ℕ) :=
    by exact_mod_cast hdata.pinned_prime.pos.trans_le hdata.pinned_upper
  have hM : 0 ≤ ∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h *
      sourcePinnedCompanionVariationalIntegral K G :=
    Finset.sum_nonneg fun h _ ↦ (hpinned h).le
  exact proxy_interval_coverage_lower hV hL (residualCofactorLocalProduct_pos heven)
    hT hmain hM hlength
    (hprime A B hdata.interval_half hdata.interval_order hdata.interval_upper hdata.interval_length)
    (hcov m p₀ A B N hdata hN hYN hmargin)

end

end Erdos4b.SmoothParameters
