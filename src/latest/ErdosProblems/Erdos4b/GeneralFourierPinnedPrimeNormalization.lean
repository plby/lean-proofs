/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedUniformError

/-!
# Numeric source conditions and the normalized pinned prime error limit

The conditions below contain only arithmetic and scale inequalities.
The distribution estimate and the prime-count lower bound are proved
inputs to the limit, not fields in the conditions.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

structure SourcePinnedNormalizationConditions
    (K w m p₀ Y X A B J : ℕ) (δ : ℝ) : Prop where
  cofactor_pos : 0 < m
  pinned_prime : p₀.Prime
  cutoff_le_companion : w ≤ Y
  companion_lt_pinned : Y < p₀
  residual_coprime : (m * p₀ - 1).Coprime (primorial Y)
  cutoff_small : (w : ℝ) ≤ Real.log (Real.log X + 1)
  log_cofactor_le : Real.log m ≤ Real.log X
  log_pinned_le : Real.log p₀ ≤ 2 * Real.log X
  log_pinned_lower : Real.log X / 2 ≤ Real.log p₀
  companion_scale_pos : 0 < Real.log Y
  companion_scale_le : Real.log Y ≤ Real.log X
  companion_scale_small : (K : ℝ) * Real.log Y ≤ Real.log X / 40
  companion_scale_lower : 2 * (Real.log X + 1) ^ (3 / 4 : ℝ) ≤ Real.log Y
  interval_half : X ≤ 2 * A
  interval_order : A ≤ B
  interval_upper : B ≤ X
  interval_length : δ * (X : ℝ) / Real.log X ^ J ≤ (B : ℝ) - A

theorem eventually_sourcePinned_primeCount_pos
    {α : Type*} {l : Filter α} {K J : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (w m p₀ Y X A B : α → ℕ) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ) :
    ∀ᶠ a in l, 0 < (auxiliaryPrimeInterval (A a) (B a)).card := by
  filter_upwards [hX.eventually (eventually_primeInterval_card_lower J hδ),
    hX.eventually_ge_atTop 2, hdata] with a hc hXa ha
  have hlog : 0 < Real.log (X a) := Real.log_pos (by exact_mod_cast (by omega : 1 < X a))
  have hXpos : (0 : ℝ) < X a := by exact_mod_cast (by omega : 0 < X a)
  have hcount := hc (A a) (B a) ha.interval_half ha.interval_order
    ha.interval_upper ha.interval_length
  exact_mod_cast (by positivity : 0 < δ * (X a : ℝ) /
    (2 * Real.log (X a) ^ (J + 1))).trans_le hcount

theorem tendsto_sourcePinnedNormalizedPrimeError_zero
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
      pinnedSourceProgressionErrorBound S F G h (P a) (A a) (B a)
        (Real.log (X a)) (Real.log (Y a))) l (𝓝 0) := by
  obtain ⟨C, hC, W, hbound⟩ := exists_uniform_normalized_pinnedSource_error_bound
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
      (pinnedSourceProgressionErrorBound_nonneg S F G h (P a) (A a) (B a) _ _)
  · filter_upwards [hdata, hw.eventually_ge_atTop W, hX.eventually hbound] with a ha hwa hba
    exact hba h (P a) (w a) (m a) (p₀ a) (Y a) (A a) (B a) (hP a) hwa
      ha.cofactor_pos ha.pinned_prime ha.companion_lt_pinned ha.residual_coprime
      ha.companion_scale_pos ha.companion_scale_le ha.companion_scale_small
      ha.interval_half ha.interval_order ha.interval_upper ha.interval_length
  · exact tendsto_const_nhds.div_atTop hlogTop

end

end Erdos4b
