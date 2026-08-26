/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeNormalization
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightExpansion

/-!
# Transfer of the vanishing normalized error to the literal pinned prime weight

The arithmetic square sum is compared to the exact totient graph
kernel using the actual interval prime count in the normalization.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem norm_real_normalized_complex_error_le
    {scale series count E : ℝ} {S T : ℂ}
    (hscale : 0 ≤ scale) (hseries : 0 < series) (hcount : 0 < count)
    (herror : ‖S - (count : ℂ) * T‖ ≤ E) :
    ‖(((scale / (series * count) : ℝ) : ℂ) * S) -
      (((scale / series : ℝ) : ℂ) * T)‖ ≤ scale / (series * count) * E := by
  have hid : (((scale / (series * count) : ℝ) : ℂ) * S) -
      (((scale / series : ℝ) : ℂ) * T) =
      ((scale / (series * count) : ℝ) : ℂ) * (S - (count : ℂ) * T) := by
    have hs : (series : ℂ) ≠ 0 := by exact_mod_cast hseries.ne'
    have hc : (count : ℂ) ≠ 0 := by exact_mod_cast hcount.ne'
    push_cast
    field_simp
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hscale (mul_nonneg hseries.le hcount.le))]
  exact mul_le_mul_of_nonneg_left herror (div_nonneg hscale (mul_nonneg hseries.le hcount.le))

def sourcePinnedPrimeNormalizedWeightSum {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (w m p₀ Y N A B : ℕ) (LD LE : ℝ) : ℂ :=
  (((LD ^ (K - 1) * LE ^ (K - 1)) /
    (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) : ℝ) : ℂ) *
      ∑ q ∈ auxiliaryPrimeInterval A B,
        pinnedSourceIntegerWeight S F G h
          (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N))
          w m p₀ q LD LE

theorem norm_sourcePinnedPrimeNormalizedWeightSum_sub_graph_le
    {K w m p₀ Y N A B : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    {LD : ℝ} (hLD : 0 < LD) (hY : 1 < Y) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hA : 0 < A) (hAB : A ≤ B)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀)
    (hSS : 0 < pinnedSingularSeries h w m p₀ Y)
    (hcount : 0 < (auxiliaryPrimeInterval A B).card) :
    let P := selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N)
    ‖sourcePinnedPrimeNormalizedWeightSum S F G h w m p₀ Y N A B LD (Real.log Y) -
      (((LD ^ (K - 1) * Real.log Y ^ (K - 1)) / pinnedSingularSeries h w m p₀ Y : ℝ) : ℂ) *
        pinnedSourceTotientGraphKernel S F G h w m p₀ Y N LD (Real.log Y)‖ ≤
      (LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
        (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) *
          pinnedSourceProgressionErrorBound S F G h P A B LD (Real.log Y) := by
  dsimp only
  have hraw := norm_pinnedSourcePrimeDivisorSum_sub_graphKernel_le (N := N) S F G h
    hLD hY hKw hm hp₀ hcop hA hAB hFsupport hGsupport hD
  unfold sourcePinnedPrimeNormalizedWeightSum
  rw [sum_pinnedSourceIntegerWeight_eq_primeDivisorSum S F G h _
    (selectedFourierPrimeCutoff_prime _ _)]
  apply norm_real_normalized_complex_error_le _ hSS (by exact_mod_cast hcount)
  · exact_mod_cast hraw
  · exact mul_nonneg (pow_nonneg hLD.le _)
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast hY.le)) _)

theorem tendsto_sourcePinnedPrimeWeight_sub_graph_zero
    {α I : Type*} {l : Filter α} {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (h : Fin K)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (w m p₀ Y X A B N : α → ℕ) (hw : Tendsto w l atTop) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ) :
    Tendsto (fun a ↦ sourcePinnedPrimeNormalizedWeightSum S F G h
        (w a) (m a) (p₀ a) (Y a) (N a) (A a) (B a) (Real.log (X a)) (Real.log (Y a)) -
      (((Real.log (X a) ^ (K - 1) * Real.log (Y a) ^ (K - 1)) /
          pinnedSingularSeries h (w a) (m a) (p₀ a) (Y a) : ℝ) : ℂ) *
        pinnedSourceTotientGraphKernel S F G h (w a) (m a) (p₀ a) (Y a) (N a)
          (Real.log (X a)) (Real.log (Y a))) l (𝓝 0) := by
  let P (a : α) := selectedFourierPrimeCutoff (fun p ↦ decide (w a < p))
    (boundedFourierPrimes (N a))
  have herror := tendsto_sourcePinnedNormalizedPrimeError_zero S F G
    hFcompact hFcont hGcompact hGcont hFsimplex hGsupport h J hδ w m p₀ Y X A B P
    (fun a ↦ selectedFourierPrimeCutoff_prime _ _) hw hX hdata
  have hcount := eventually_sourcePinned_primeCount_pos hδ w m p₀ Y X A B hX hdata
  obtain ⟨W, hW⟩ := exists_uniform_half_le_pinnedSingularSeries K
  have hlogTop : Tendsto (fun a ↦ Real.log (X a)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ herror
  filter_upwards [hdata, hcount, hw.eventually_ge_atTop (max K W),
    hlogTop.eventually_ge_atTop 1, hX.eventually_ge_atTop 2] with a ha hca hwa hVa hXa
  have hSS := hW (w a) ((le_max_right _ _).trans hwa) h (m a) (p₀ a) (Y a)
    ha.cofactor_pos ha.pinned_prime ha.companion_lt_pinned ha.residual_coprime
  have hY : 1 < Y a := by
    by_contra! hYa
    have hn := Real.log_nonpos (Nat.cast_nonneg (Y a)) (by exact_mod_cast hYa)
    linarith [ha.companion_scale_pos]
  have hA : 0 < A a := by have := ha.interval_half; omega
  exact norm_sourcePinnedPrimeNormalizedWeightSum_sub_graph_le S F G h (by linarith) hY
    ((le_max_left _ _).trans hwa) ha.cofactor_pos ha.pinned_prime ha.residual_coprime hA
    ha.interval_order hFceiling hGsupport (by linarith [ha.log_pinned_lower])
    (by linarith) hca

end

end Erdos4b
