/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCollisionLossBound
import ErdosProblems.Erdos4b.GeneralFourierSourceCutoffGrowth

/-!
# The normalized weighted collision loss tends to zero

This is the literal nonnegative source square, not an unweighted prime
count. The arithmetic source conditions discharge all scale and prime
distribution requirements. The Fourier cutoff may be any common cutoff
large enough to include the companion primes.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def sourcePinnedNormalizedCollisionLoss {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (w m p₀ Y X A B N : ℕ) : ℝ :=
  (Real.log X ^ (K - 1) * Real.log Y ^ (K - 1)) /
    (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) *
      weightedSingularCollisionLoss K w Y m A B
        (fun q ↦ pinnedSourceRealIntegerWeight S F G h
          (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N))
          w m p₀ q (Real.log X) (Real.log Y))

theorem tendsto_sourcePinnedNormalizedCollisionLoss_zero
    {α I : Type*} {l : Filter α} {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i))
    (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (h : Fin K)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (w m p₀ Y X A B N : α → ℕ) (hw : Tendsto w l atTop) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ)
    (hN : ∀ᶠ a in l,
      jointSourceCommonPrimeBound S F G (Real.log (X a)) (Real.log (Y a)) ≤ N a)
    (hYN : ∀ᶠ a in l, Y a ≤ N a) :
    Tendsto (fun a ↦ sourcePinnedNormalizedCollisionLoss S F G h
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) (N a)) l (𝓝 0) := by
  let P (a : α) := selectedFourierPrimeCutoff (fun p ↦ decide (w a < p))
    (boundedFourierPrimes (N a))
  have hV : Tendsto (fun a ↦ Real.log (X a)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX)
  have hY := (tendsto_sourceCutoff_atTop_and_ambient_div_zero Y (fun a ↦ Real.log (X a)) hV
    (hdata.mono fun a ha ↦ ha.companion_scale_lower)).1
  obtain ⟨C, hC, hmain⟩ := exists_eventually_pinnedSourceForcedGraphKernel_bound S F G h
    hFcompact hFsmooth hGcompact hGsmooth w m p₀ Y (fun a ↦ Real.log (X a)) hw hV hY
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.pinned_prime)
    (hdata.mono fun a ha ↦ ha.cutoff_le_companion)
    (hdata.mono fun a ha ↦ ha.companion_lt_pinned)
    (hdata.mono fun a ha ↦ ha.residual_coprime) (hdata.mono fun a ha ↦ ha.cutoff_small)
    (hdata.mono fun a ha ↦ ha.log_cofactor_le) (hdata.mono fun a ha ↦ ha.log_pinned_le)
    (hdata.mono fun a ha ↦ ha.companion_scale_lower)
    (hdata.mono fun a ha ↦ ha.companion_scale_le)
  have herr := tendsto_sourcePinnedNormalizedForcedPrimeError_zero S F G
    hFcompact (fun j i ↦ (hFsmooth j i).continuous) hGcompact hGsmooth.continuous
    hFsimplex hGsupport h J hδ w m p₀ Y X A B P
    (fun a ↦ selectedFourierPrimeCutoff_prime _ _) hw hX hdata
  have hsmall : Tendsto (fun a ↦ 2 * C / (w a : ℝ)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hw)
  have hlim := (hsmall.add herr).const_mul ((4 * K : ℝ) * (K : ℝ) ^ 2)
  simp only [zero_add, mul_zero] at hlim
  obtain ⟨W, hW⟩ := exists_uniform_half_le_pinnedSingularSeries K
  have hcount := eventually_sourcePinned_primeCount_pos hδ w m p₀ Y X A B hX hdata
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hdata, hw.eventually_ge_atTop W, hV.eventually_ge_atTop 0]
      with a ha hwa hVa
    have hSS := hW (w a) hwa h (m a) (p₀ a) (Y a) ha.cofactor_pos ha.pinned_prime
      ha.companion_lt_pinned ha.residual_coprime
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg (pow_nonneg hVa _) (pow_nonneg ha.companion_scale_pos.le _))
        (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    · exact weightedSingularCollisionLoss_nonneg _ _ _ _ _ _ _
        (fun q ↦ pinnedSourceRealIntegerWeight_nonneg S F G h _ _ _ _ q _ _)
  · filter_upwards [hdata, hmain, hN, hYN, hcount, hw.eventually_ge_atTop (max (max K 1) W),
      hV.eventually_ge_atTop 1, hX.eventually_ge_atTop 2, hY.eventually_gt_atTop 1]
      with a ha hma hNa hYNa hca hwa hVa hXa hYa
    have hSS := hW (w a) ((le_max_right _ _).trans hwa) h (m a) (p₀ a) (Y a)
      ha.cofactor_pos ha.pinned_prime ha.companion_lt_pinned ha.residual_coprime
    have hKw : K ≤ w a := (le_max_left K 1).trans ((le_max_left _ _).trans hwa)
    have hw0 : 0 < w a := (le_max_right K 1).trans ((le_max_left _ _).trans hwa)
    have hA : 0 < A a := by have := ha.interval_half; omega
    apply normalized_pinnedSourceCollisionLoss_le S F G h (P a)
      (selectedFourierPrimeCutoff_prime _ _)
      (fun p hp ↦ rough_of_mem_selectedFourierPrimeCutoff _ _ hp)
      _ (by linarith) hC hw0 hYa hKw ha.cofactor_pos ha.pinned_prime ha.residual_coprime
      hA ha.interval_order hFceiling hGsupport (by linarith [ha.log_pinned_lower])
      (by linarith) hca
    · intro p hp r
      have hd := mem_varyingSingularPrimeSupport.mp hp
      simpa only [Complex.ofReal_div] using hma ⟨p, hd.2.2.1⟩ hd.1 r (N a) hNa
    · intro p hp
      have hd := mem_varyingSingularPrimeSupport.mp hp
      exact mem_selected_rough_primeCutoff_of_le hd.2.2.1 hd.1 (hd.2.1.trans hYNa)

end

end Erdos4b
