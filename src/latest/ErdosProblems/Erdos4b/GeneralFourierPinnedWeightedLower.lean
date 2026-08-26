/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCollisionLossLimit
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeAsymptotic

/-!
# A pinned lower bound with the inverse singular correction retained

The all-one prime-weight asymptotic and the vanishing weighted collision
loss give a lower bound for the actual inverse-singular weighted sum.
The fixed factor from primes dividing the cofactor is divided out exactly.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem sourcePinnedNormalizationConditions_companion_lt_interval
    {K w m p₀ Y X A B J : ℕ} {δ : ℝ} (hK : 0 < K) (hX : 0 < X)
    (hV : 2 ≤ Real.log X) (ha : SourcePinnedNormalizationConditions K w m p₀ Y X A B J δ) :
    Y < A := by
  have hY1 : (1 : ℝ) < Y := (Real.log_pos_iff (Nat.cast_nonneg Y)).mp ha.companion_scale_pos
  have hY0 : (0 : ℝ) < Y := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLE := mul_le_mul_of_nonneg_right hK1 ha.companion_scale_pos.le
  by_contra hn
  have hXY : X ≤ 2 * Y := ha.interval_half.trans (Nat.mul_le_mul_left 2 (by omega))
  have hlog := Real.log_le_log (by exact_mod_cast hX : (0 : ℝ) < X)
    (by exact_mod_cast hXY : (X : ℝ) ≤ 2 * (Y : ℝ))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY0.ne'] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith [ha.companion_scale_small]

def sourcePinnedInverseSingularNormalizedWeight {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (w m p₀ Y X A B N : ℕ) : ℝ :=
  ((Real.log X ^ (K - 1) * Real.log Y ^ (K - 1)) /
    (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card)) /
      fixedSingularInverseFactor K w Y m *
        ∑ q ∈ auxiliaryPrimeInterval A B,
          pinnedSourceRealIntegerWeight S F G h
            (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N))
            w m p₀ q (Real.log X) (Real.log Y) * roughSingularInverseProduct K w Y m q

theorem normalized_pinnedWeight_sub_loss_le_inverseSingularWeight
    {K w m p₀ Y X A B N : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (hfour : 4 * K ≤ w) (hw : 0 < w) (hyA : Y < A)
    (hscale : 0 ≤ Real.log X ^ (K - 1) * Real.log Y ^ (K - 1))
    (hSS : 0 ≤ pinnedSingularSeries h w m p₀ Y) :
    (sourcePinnedPrimeNormalizedWeightSum S F G h w m p₀ Y N A B
      (Real.log X) (Real.log Y)).re - sourcePinnedNormalizedCollisionLoss S F G h w m p₀ Y X A B N ≤
      sourcePinnedInverseSingularNormalizedWeight S F G h w m p₀ Y X A B N := by
  let P := selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N)
  let W (q : ℕ) := pinnedSourceRealIntegerWeight S F G h P w m p₀ q (Real.log X) (Real.log Y)
  let ρ := (Real.log X ^ (K - 1) * Real.log Y ^ (K - 1)) /
    (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card)
  have hρ : 0 ≤ ρ := div_nonneg hscale (mul_nonneg hSS (Nat.cast_nonneg _))
  have hfixed := fixedSingularInverseFactor_pos (y := Y) (m := m) hfour hw
  have hlower := weighted_roughSingularInverseProduct_lower (m := m) (B := B) hfour hw hyA W
    (fun q hq ↦ pinnedSourceRealIntegerWeight_nonneg S F G h P w m p₀ q _ _)
  have hdiv : (∑ q ∈ auxiliaryPrimeInterval A B, W q) -
      weightedSingularCollisionLoss K w Y m A B W ≤
      (∑ q ∈ auxiliaryPrimeInterval A B, W q * roughSingularInverseProduct K w Y m q) /
        fixedSingularInverseFactor K w Y m := by
    apply (le_div_iff₀ hfixed).mpr
    simpa only [mul_comm] using hlower
  have hreal : (sourcePinnedPrimeNormalizedWeightSum S F G h w m p₀ Y N A B
      (Real.log X) (Real.log Y)).re = ρ * ∑ q ∈ auxiliaryPrimeInterval A B, W q := by
    unfold sourcePinnedPrimeNormalizedWeightSum
    simp_rw [← ofReal_pinnedSourceRealIntegerWeight]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hreal]
  change ρ * (∑ q ∈ auxiliaryPrimeInterval A B, W q) -
    ρ * weightedSingularCollisionLoss K w Y m A B W ≤
    ρ / fixedSingularInverseFactor K w Y m *
      ∑ q ∈ auxiliaryPrimeInterval A B, W q * roughSingularInverseProduct K w Y m q
  calc
    _ = ρ * ((∑ q ∈ auxiliaryPrimeInterval A B, W q) -
        weightedSingularCollisionLoss K w Y m A B W) := by ring
    _ ≤ ρ * ((∑ q ∈ auxiliaryPrimeInterval A B, W q * roughSingularInverseProduct K w Y m q) /
        fixedSingularInverseFactor K w Y m) := mul_le_mul_of_nonneg_left hdiv hρ
    _ = _ := by ring

theorem eventually_sourcePinnedInverseSingularNormalizedWeight_lower
    {α I : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i))
    (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (h : Fin K)
    (J : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (w m p₀ Y X A B N : α → ℕ) (hw : Tendsto w l atTop) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ)
    (hN : ∀ᶠ a in l,
      jointSourceCommonPrimeBound S F G (Real.log (X a)) (Real.log (Y a)) ≤ N a)
    (hYN : ∀ᶠ a in l, Y a ≤ N a) :
    ∀ᶠ a in l, sourcePinnedFirstVariationalIntegral S F h *
      sourcePinnedCompanionVariationalIntegral K G - ε <
        sourcePinnedInverseSingularNormalizedWeight S F G h
          (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) (N a) := by
  have hprime := tendsto_sourcePinnedPrimeNormalizedWeightSum S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport h J hδ
    w m p₀ Y X A B N hw hX hdata hN
  have hreal := (Complex.continuous_re.tendsto _).comp hprime
  simp only [Complex.ofReal_re, Function.comp_def] at hreal
  have hloss := tendsto_sourcePinnedNormalizedCollisionLoss_zero S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport h J hδ
    w m p₀ Y X A B N hw hX hdata hN hYN
  have hnet := hreal.sub hloss
  simp only [sub_zero] at hnet
  have hnear := hnet.eventually (lt_mem_nhds (sub_lt_self _ hε))
  have hV : Tendsto (fun a ↦ Real.log (X a)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX)
  obtain ⟨W, hW⟩ := exists_uniform_half_le_pinnedSingularSeries K
  filter_upwards [hnear, hdata, hw.eventually_ge_atTop (max (4 * K) W),
    hV.eventually_ge_atTop 2, hX.eventually_ge_atTop 1] with a hna ha hwa hVa hXa
  have hfour : 4 * K ≤ w a := (le_max_left _ _).trans hwa
  have hw0 : 0 < w a := by have := h.pos; omega
  have hSS := hW (w a) ((le_max_right _ _).trans hwa) h (m a) (p₀ a) (Y a)
    ha.cofactor_pos ha.pinned_prime ha.companion_lt_pinned ha.residual_coprime
  exact hna.trans_le (normalized_pinnedWeight_sub_loss_le_inverseSingularWeight S F G h
    hfour hw0 (sourcePinnedNormalizationConditions_companion_lt_interval h.pos hXa hVa ha)
    (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg ha.companion_scale_pos.le _))
    (by linarith))

theorem sourcePinnedInverseSingularNormalizedWeight_eq_singularQuotient
    {K w m p₀ Y X A B N : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (hfour : 4 * K ≤ w) (hwy : w ≤ Y) (hm : Even m) :
    sourcePinnedInverseSingularNormalizedWeight S F G h w m p₀ Y X A B N =
      ((Real.log X ^ (K - 1) * Real.log Y ^ (K - 1)) /
        (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card)) *
        (largeGapSingularSeries (preSievedShifts K w) m 1 w * genericRoughSingularProduct K w Y) /
        fixedSingularInverseFactor K w Y m *
          ∑ q ∈ auxiliaryPrimeInterval A B,
            pinnedSourceRealIntegerWeight S F G h
              (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N))
              w m p₀ q (Real.log X) (Real.log Y) /
                largeGapSingularSeries (preSievedShifts K w) m q Y := by
  have hsmall (q : ℕ) : largeGapSingularSeries (preSievedShifts K w) m q w =
      largeGapSingularSeries (preSievedShifts K w) m 1 w := by
    rw [largeGapSingularSeries_preSieveCutoff h.pos,
      largeGapSingularSeries_preSieveCutoff h.pos]
  unfold sourcePinnedInverseSingularNormalizedWeight
  simp_rw [roughSingularInverseProduct_eq_universal_div_singularSeries hfour hwy hm, hsmall]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

end

end Erdos4b
