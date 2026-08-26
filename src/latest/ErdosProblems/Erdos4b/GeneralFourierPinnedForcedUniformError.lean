/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedLogSaving
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeNormalization

/-!
# Vanishing normalized aggregate forced-prime discrepancy

The two endpoints are summed over every prime up to `Y`. The normalization
uses the literal pinned singular series and the actual interval prime count.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def pinnedSourceForcedProgressionErrorBound {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (Y A B : ℕ) (LD LE : ℝ) : ℝ :=
  pinnedSourceForcedEndpointErrorBound S F G h P Y (B - 1) LD LE +
    pinnedSourceForcedEndpointErrorBound S F G h P Y (A - 1) LD LE

theorem pinnedSourceForcedEndpointErrorBound_nonneg
    {K : ℕ} {I : Type*} (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (Y x : ℕ) (LD LE : ℝ) :
    0 ≤ pinnedSourceForcedEndpointErrorBound S F G h P Y x LD LE := by
  unfold pinnedSourceForcedEndpointErrorBound
  exact Finset.sum_nonneg fun p hp ↦ Finset.sum_nonneg fun d hd ↦
    mul_nonneg (norm_nonneg _) (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)

theorem pinnedSourceForcedProgressionErrorBound_nonneg
    {K : ℕ} {I : Type*} (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (Y A B : ℕ) (LD LE : ℝ) :
    0 ≤ pinnedSourceForcedProgressionErrorBound S F G h P Y A B LD LE :=
  add_nonneg (pinnedSourceForcedEndpointErrorBound_nonneg S F G h P Y (B - 1) LD LE)
    (pinnedSourceForcedEndpointErrorBound_nonneg S F G h P Y (A - 1) LD LE)

theorem exists_uniform_normalized_pinnedSourceForced_error_bound
    {K : ℕ} {I : Type*} (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ 0, ∃ W : ℕ, ∀ᶠ X : ℕ in atTop,
      ∀ (h : Fin K) (P : Finset ℕ) (w m p₀ Y A B : ℕ),
        (∀ p ∈ P, p.Prime) → W ≤ w → 0 < m → p₀.Prime → Y < p₀ →
        (m * p₀ - 1).Coprime (primorial Y) → 0 < Real.log Y → Real.log Y ≤ Real.log X →
        (K : ℝ) * Real.log Y ≤ Real.log X / 40 → X ≤ 2 * A → A ≤ B → B ≤ X →
        δ * (X : ℝ) / Real.log X ^ J ≤ (B : ℝ) - A →
        (Real.log X ^ (K - 1) * Real.log Y ^ (K - 1)) /
            (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) *
          pinnedSourceForcedProgressionErrorBound S F G h P Y A B (Real.log X) (Real.log Y) ≤
            C / Real.log X := by
  let L : ℕ := 2 * K + J + 2
  obtain ⟨C₀, hC₀, X₀, hX₀, hsource⟩ := exists_uniform_pinnedSourceForcedEndpoint_logSaving
    S F G hFcompact hFcont hGcompact hGcont hFsupport hGsupport L
  obtain ⟨W, hW⟩ := exists_uniform_half_le_pinnedSingularSeries K
  refine ⟨8 * C₀ * 2 ^ L / δ, by positivity, W, ?_⟩
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_primeInterval_card_lower J hδ,
    eventually_ge_atTop (max 8 (4 * X₀)), hlogTop.eventually_ge_atTop 160,
    hlogTop.eventually_ge_atTop (4 * Real.log 4)] with X hprimeCount hX hlog160 hlog4
  intro h P w m p₀ Y A B hP hw hm hp₀ hYp₀ hcop hLE hLEV hsmall hhalf hAB hBX hlength
  have hY : 1 < Y := by
    by_contra hn
    have hy : Y = 0 ∨ Y = 1 := by omega
    rcases hy with rfl | rfl <;> norm_num at hLE
  have hXpos : 0 < X := by omega
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hVpos : 0 < Real.log X := by linarith
  have hXA : X₀ ≤ A - 1 := by omega
  have hXB : X₀ ≤ B - 1 := by omega
  have hfourA : X ≤ 4 * (A - 1) := by omega
  have hfourB : X ≤ 4 * (B - 1) := by omega
  have hlogA := threeQuarter_log_le_log_of_four_mul_ge hXpos hfourA hlog4
  have hlogB := threeQuarter_log_le_log_of_four_mul_ge hXpos hfourB hlog4
  have hEA : pinnedSourceForcedEndpointErrorBound S F G h P Y (A - 1)
      (Real.log X) (Real.log Y) ≤ C₀ * 2 ^ L * (X : ℝ) / Real.log X ^ L := by
    apply (hsource h P (Real.log X) Y (A - 1) hP hlog160 hY hsmall hlogA hXA).trans
    exact logSaving_term_le_ambient L hC₀ (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sub_le A 1).trans (hAB.trans hBX)) hVpos (by linarith)
  have hEB : pinnedSourceForcedEndpointErrorBound S F G h P Y (B - 1)
      (Real.log X) (Real.log Y) ≤ C₀ * 2 ^ L * (X : ℝ) / Real.log X ^ L := by
    apply (hsource h P (Real.log X) Y (B - 1) hP hlog160 hY hsmall hlogB hXB).trans
    exact logSaving_term_le_ambient L hC₀ (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sub_le B 1).trans hBX) hVpos (by linarith)
  have herr : pinnedSourceForcedProgressionErrorBound S F G h P Y A B
      (Real.log X) (Real.log Y) ≤ 2 * C₀ * 2 ^ L * (X : ℝ) / Real.log X ^ L :=
    (add_le_add hEB hEA).trans_eq (by ring)
  have hseries := hW w hw h m p₀ Y hm hp₀ hYp₀ hcop
  have hcount := hprimeCount A B hhalf hAB hBX hlength
  have hnorm := normalized_pinned_error_le_inverse_ambient (2 * K) J hδ hC₀ hXreal hVpos
    (pinnedScaleProduct_le_ambient_power K (by linarith) hLE.le hLEV) hseries hcount
    (pinnedSourceForcedProgressionErrorBound_nonneg S F G h P Y A B
      (Real.log X) (Real.log Y)) herr
  exact hnorm.trans_eq (by dsimp only [L]; ring)

theorem tendsto_sourcePinnedNormalizedForcedPrimeError_zero
    {α I : Type*} {l : Filter α} {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (h : Fin K)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (w m p₀ Y X A B : α → ℕ) (P : α → Finset ℕ)
    (hP : ∀ a, ∀ p ∈ P a, p.Prime) (hw : Tendsto w l atTop) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ) :
    Tendsto (fun a ↦ (Real.log (X a) ^ (K - 1) * Real.log (Y a) ^ (K - 1)) /
        (pinnedSingularSeries h (w a) (m a) (p₀ a) (Y a) *
          (auxiliaryPrimeInterval (A a) (B a)).card) *
      pinnedSourceForcedProgressionErrorBound S F G h (P a) (Y a) (A a) (B a)
        (Real.log (X a)) (Real.log (Y a))) l (𝓝 0) := by
  obtain ⟨C, hC, W, hbound⟩ := exists_uniform_normalized_pinnedSourceForced_error_bound
    S F G hFcompact hFcont hGcompact hGcont hFsupport hGsupport J hδ
  obtain ⟨W', hW'⟩ := exists_uniform_half_le_pinnedSingularSeries K
  have hlogTop : Tendsto (fun a ↦ Real.log (X a)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX)
  apply squeeze_zero'
  · filter_upwards [hdata, hw.eventually_ge_atTop W', hlogTop.eventually_ge_atTop 0]
      with a ha hwa hVa
    have hSS := hW' (w a) hwa h (m a) (p₀ a) (Y a) ha.cofactor_pos ha.pinned_prime
      ha.companion_lt_pinned ha.residual_coprime
    exact mul_nonneg
      (div_nonneg (mul_nonneg (pow_nonneg hVa _) (pow_nonneg ha.companion_scale_pos.le _))
        (mul_nonneg (by linarith) (Nat.cast_nonneg _)))
      (pinnedSourceForcedProgressionErrorBound_nonneg S F G h (P a) (Y a) (A a) (B a) _ _)
  · filter_upwards [hdata, hw.eventually_ge_atTop W, hX.eventually hbound] with a ha hwa hba
    exact hba h (P a) (w a) (m a) (p₀ a) (Y a) (A a) (B a) (hP a) hwa
      ha.cofactor_pos ha.pinned_prime ha.companion_lt_pinned ha.residual_coprime
      ha.companion_scale_pos ha.companion_scale_le ha.companion_scale_small
      ha.interval_half ha.interval_order ha.interval_upper ha.interval_length
  · exact tendsto_const_nhds.div_atTop hlogTop

end

end Erdos4b
