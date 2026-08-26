/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedProbability
import ErdosProblems.Erdos4b.SourceDyadicResidueNormalization
import ErdosProblems.Erdos4b.SourceDyadicPinnedSingularMass

/-!
# Uniform coverage by the literal dyadic source residue probabilities

The pinned mass and the unpinned normalization are combined at the
same finite cutoff. The boundary margin is explicit and will be supplied
only after the boundary residual primes are removed.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def dyadicSourceResidueCoverage {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (a D r m p₀ A B N : ℕ) : ℝ :=
  ∑ q : auxiliaryPrimeInterval A B, dyadicSourceResidueMass S F G a D r m q.val N
    ⟨p₀ % q.val, Nat.mod_lt p₀ (mem_auxiliaryPrimeInterval.mp q.property).2.2.pos⟩

theorem dyadicSourceResidueCoverage_nonneg {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (a D r m p₀ A B N : ℕ) :
    0 ≤ dyadicSourceResidueCoverage S F G a D r m p₀ A B N :=
  Finset.sum_nonneg fun q _ ↦ dyadicSourceResidueMass_nonneg S F G a D r m q.val N _

theorem uniform_dyadicSourceResidueCoverage_lower
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
    ∀ᶠ r in atTop, ∀ m p₀ A B N : ℕ, DyadicPinnedSourceRange a D J δ r m p₀ A B →
      jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N →
      smoothFrontier r ≤ N →
      (∀ q ∈ auxiliaryPrimeInterval A B, ∀ h : Fin K,
        primorial (sourcePreSieveCutoff r) * h.val * q < p₀) →
      dyadicAmbientScale a r * dyadicCompanionScale r *
          residualCofactorLocalProduct (smoothFrontier r) m * (auxiliaryPrimeInterval A B).card /
          (8 * (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G) *
            (D * intervalLength a r / m : ℕ)) *
          (∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h *
            sourcePinnedCompanionVariationalIntegral K G) ≤
        dyadicSourceResidueCoverage S F G a D r m p₀ A B N := by
  have hnormal := uniform_dyadicSourceResidueNormalization_pos_and_upper hK S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport a D hmain
  have hpins := eventually_all.mpr (fun h : Fin K ↦
    uniform_dyadicPinnedSingularWeightedMass_lower S F G hFcompact hFsmooth hGcompact
      hGsmooth hFsimplex hFceiling hGsupport h a D J hδ (hpinned h))
  filter_upwards [hnormal, hpins, eventually_sourcePinnedNormalizationConditions_dyadic K a D J δ,
    tendsto_sourcePreSieveCutoff_atTop.eventually (eventually_ge_atTop (2 * K))]
    with r hnorm hmass hconditions hw
  intro m p₀ A B N hdata hN hYN hmargin
  have hc := hconditions m p₀ A B hdata.cofactor_pos hdata.cofactor_le hdata.pinned_prime
    hdata.pinned_lower hdata.pinned_upper hdata.residual_coprime hdata.interval_half
    hdata.interval_order hdata.interval_upper hdata.interval_length
  have hY : 1 < smoothFrontier r := by have := hc.cutoff_le_companion; omega
  have heven := even_cofactor_of_pinnedResidual_coprime hdata.pinned_prime (by omega)
    hc.companion_lt_pinned hdata.residual_coprime
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := hc.companion_scale_pos
  have hD : dyadicAmbientScale a r / 10 < Real.log p₀ := by
    have hlo : dyadicAmbientScale a r / 2 ≤ Real.log p₀ := hc.log_pinned_lower
    linarith
  have hT : (0 : ℝ) < (D * intervalLength a r / m : ℕ) :=
    by exact_mod_cast hdata.pinned_prime.pos.trans_le hdata.pinned_upper
  let P := selectedFourierPrimeCutoff (fun p ↦ decide (sourcePreSieveCutoff r < p))
    (boundedFourierPrimes N)
  let W : Fin K → auxiliaryPrimeInterval A B → ℝ := fun h q ↦
    pinnedSourceRealIntegerWeight S F G h P (sourcePreSieveCutoff r) m p₀ q.val
      (dyadicAmbientScale a r) (dyadicCompanionScale r) /
        largeGapSingularSeries (preSievedShifts K (sourcePreSieveCutoff r)) m q.val
          (smoothFrontier r)
  let M : Fin K → ℝ := fun h ↦ sourcePinnedFirstVariationalIntegral S F h *
    sourcePinnedCompanionVariationalIntegral K G
  let μ : auxiliaryPrimeInterval A B → ℝ := fun q ↦
    dyadicSourceResidueMass S F G a D r m q.val N
      ⟨p₀ % q.val, Nat.mod_lt p₀ (mem_auxiliaryPrimeInterval.mp q.property).2.2.pos⟩
  have hmass' : ∀ h, M h *
      (residualCofactorLocalProduct (smoothFrontier r) m * (auxiliaryPrimeInterval A B).card) /
        (4 * (dyadicAmbientScale a r ^ (K - 1) * dyadicCompanionScale r ^ (K - 1))) ≤
      ∑ q, W h q := by
    intro h
    have hh := hmass h m p₀ A B N hdata hN hYN
    have hs : (∑ q, W h q) = dyadicPinnedSingularWeightedMass S F G h a r m p₀ A B N :=
      Finset.sum_coe_sort (auxiliaryPrimeInterval A B) (fun q ↦
        pinnedSourceRealIntegerWeight S F G h P (sourcePreSieveCutoff r) m p₀ q
          (dyadicAmbientScale a r) (dyadicCompanionScale r) /
            largeGapSingularSeries (preSievedShifts K (sourcePreSieveCutoff r)) m q
              (smoothFrontier r))
    rw [hs]
    simpa only [M, mul_assoc] using hh
  have hpoint : ∀ q, (dyadicAmbientScale a r ^ K * dyadicCompanionScale r ^ K /
        (2 * (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G) *
          (D * intervalLength a r / m : ℕ))) * (∑ h, W h q) ≤ μ q := by
    intro q
    have hqd := mem_auxiliaryPrimeInterval.mp q.property
    have hqrange : dyadicSourceRange a D r m q.val :=
      ⟨hdata.cofactor_pos, heven, hdata.cofactor_le, hqd.2.2,
        hdata.interval_half.trans (Nat.mul_le_mul_left 2 hqd.1),
        hqd.2.1.le.trans hdata.interval_upper⟩
    have hqnorm := hnorm m q.val N hqrange hN
    have hraw := sum_pinnedSourceWeight_le_sourceResidueRawWeight S F G P
      (selectedFourierPrimeCutoff_prime _ _) hV hY hdata.cofactor_pos hqd.2.2.pos
      hdata.pinned_prime hc.cutoff_le_companion hc.companion_lt_pinned hdata.pinned_upper
      hFceiling hGsupport hD hdata.residual_coprime
      (hmargin q.val q.property)
    exact sourceResidueMass_lower_of_pinned_sum hqd.2.2.pos S F G P
      (dyadicAmbientScale a r) (dyadicCompanionScale r)
      (D * intervalLength a r) (sourcePreSieveCutoff r) m p₀ _
      (mul_pos (pow_pos hV _) (pow_pos hL _)) hmain hT
      (largeGapSingularSeries_preSievedShifts_pos hw heven) hraw hqnorm.1 hqnorm.2
  have hresult := finite_coverage_lower_of_pinned_mass W M μ (by positivity) hmass' hpoint
  rw [sourceCoverageScale_identity hK hV hL hmain hT] at hresult
  simpa only [M, μ, dyadicSourceResidueCoverage, mul_assoc] using hresult

end

end Erdos4b.SmoothParameters
