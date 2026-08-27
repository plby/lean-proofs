/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsorptionBounds

/-! # Absorbing the actual tail, hit, and avoidance envelopes -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

theorem stageTailEnvelope_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ β : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 < z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 5 * z ^ 10) :
    F.stageTailEnvelope e κ δ (z ^ 30) (z ^ 10) β (z ^ 5) (z ^ 5) D ≤
      31 * S ^ 3 * z ^ 20 + 14 * S ^ 4 * z ^ 5 := by
  have hκ := h.kappa_pos
  have hD := h.degree_nonneg
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  have hvar := F.stageVarianceEnvelope_absorbed e h hz.le hsmall hδ0 hδ
  have hvar0 : 0 ≤ F.stageVarianceEnvelope e κ δ (z ^ 30) D := by
    unfold stageVarianceEnvelope stageFirstEnvelope stageSecondEnvelope
    positivity
  have hraw : (e.card : ℝ) * (F.stageVarianceEnvelope e κ δ (z ^ 30) D / (z ^ 5) ^ 2) ≤
      31 * S ^ 3 * z ^ 20 := by
    calc
      _ ≤ S * (31 * S ^ 2 * z ^ 30 / (z ^ 5) ^ 2) :=
        mul_le_mul h.card_le (div_le_div_of_nonneg_right hvar (by positivity))
          (by positivity) (by positivity)
      _ = _ := by field_simp
  have hreplace : (e.card : ℝ) *
      (2 * (β + 2 * z ^ 10) * (1 / κ ^ F.rank) * (1 / κ ^ e.card) * D / z ^ 5) ≤
      14 * S ^ 4 * z ^ 5 := by
    calc
      _ ≤ S * (2 * (7 * z ^ 10) * S * S * S / z ^ 5) := by
        gcongr
        · exact h.card_le
        · linarith
        · exact h.rank_inverse_le
        · exact h.card_inverse_le
        · exact h.degree_le
      _ = _ := by field_simp; ring
  unfold stageTailEnvelope
  rw [mul_add]
  exact add_le_add hraw hreplace

theorem normalized_sparsity_le (δ : ℝ) (hδ : 0 ≤ δ) (hI : 0 < Fintype.card I) :
    δ / Real.sqrt (Fintype.card I) ≤ δ := by
  apply div_le_self hδ
  exact Real.one_le_sqrt.mpr (by exact_mod_cast hI)

theorem testSetSquareBound_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (_hz : 0 ≤ z) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60) (hI : 0 < Fintype.card I) :
    F.testSetSquareBound e κ (δ / Real.sqrt (Fintype.card I)) ≤ 4 * S ^ 4 * z ^ 120 := by
  have hκ := h.kappa_pos
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  rw [F.testSetSquareBound_sqrt e κ δ hI]
  calc
    _ = 4 * (1 / κ ^ F.rank) ^ 2 * (e.card : ℝ) ^ 2 * δ ^ 2 := by
      rw [show 2 * F.rank = F.rank * 2 by omega, pow_mul]
      simp only [one_div, inv_pow]
    _ ≤ 4 * S ^ 2 * S ^ 2 * (z ^ 60) ^ 2 := by
      gcongr
      · exact h.rank_inverse_le
      · exact h.card_le
    _ = _ := by ring

theorem testSetMeanError_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 ≤ z) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60) :
    F.testSetMeanError e κ δ (z ^ 5 + z ^ 5) ≤ 2 * S * z ^ 5 + 2 * S ^ 3 * z ^ 60 := by
  have hκ := h.kappa_pos
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  calc
    _ ≤ S * (z ^ 5 + z ^ 5) + 2 * S * S ^ 2 * z ^ 60 := by
      unfold testSetMeanError
      gcongr
      · exact h.card_le
      · exact h.rank_inverse_le
      · exact h.card_le
    _ = _ := by ring

theorem testSetHitBound_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 ≤ z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60)
    (hI : 0 < Fintype.card I) :
    F.testSetHitBound e κ (δ / Real.sqrt (Fintype.card I)) ≤ 1 / 2 := by
  have hκ := h.kappa_pos
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  have hb := normalized_sparsity_le δ hδ0 hI
  calc
    _ ≤ 2 * S * S * z ^ 60 := by
      unfold testSetHitBound
      gcongr
      · exact h.rank_inverse_le
      · exact h.card_le
      · exact hb.trans hδ
    _ = 2 * S ^ 2 * z ^ 60 := by ring
    _ ≤ _ := absorption_hit_small h.scale_ge hz hsmall

theorem testSetProduct_small (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 ≤ z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60)
    (hI : 0 < Fintype.card I) :
    2 * F.testSetSquareBound e κ (δ / Real.sqrt (Fintype.card I)) +
      F.testSetMeanError e κ δ (z ^ 5 + z ^ 5) ≤ 1 := by
  have hQ := F.testSetSquareBound_absorbed e h hz hδ0 hδ hI
  have hE := F.testSetMeanError_absorbed e h hz hδ0 hδ
  have hbudget := absorption_product_small h.scale_ge hz hsmall
  linarith

theorem stageErrorEnvelope_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 < z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60)
    (hI : 0 < Fintype.card I) :
    F.stageErrorEnvelope e κ δ (z ^ 30) (z ^ 10)
      (F.stageNormalizerTailBound κ (δ / Real.sqrt (Fintype.card I)) (z ^ 30) (z ^ 10))
      (z ^ 5) (z ^ 5) (δ / Real.sqrt (Fintype.card I)) D ≤ 69 * S ^ 4 * z ^ 5 := by
  have hκ := h.kappa_pos
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  have hb0 : 0 ≤ δ / Real.sqrt (Fintype.card I) := by positivity
  have hβ := F.stageNormalizerTailBound_absorbed e h hz hsmall hb0
    (normalized_sparsity_le δ hδ0 hI) hδ
  have hβ0 : 0 ≤ F.stageNormalizerTailBound κ
      (δ / Real.sqrt (Fintype.card I)) (z ^ 30) (z ^ 10) := by
    unfold stageNormalizerTailBound
    positivity
  have hQ := F.testSetSquareBound_absorbed e h hz.le hδ0 hδ hI
  have hE := F.testSetMeanError_absorbed e h hz.le hδ0 hδ
  have hT := F.stageTailEnvelope_absorbed e h hz hsmall hδ0 hδ hβ0 hβ
  have hpoly := absorption_error_polynomial hS hz.le
    (absorption_parameter_le_one hS hz.le hsmall)
  unfold stageErrorEnvelope
  linarith

theorem stageRelativeError_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 < z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60)
    (hI : 0 < Fintype.card I) :
    z ^ 30 + (1 + z ^ 30) * Real.exp ((e.card : ℝ) * D) *
      F.stageErrorEnvelope e κ δ (z ^ 30) (z ^ 10)
        (F.stageNormalizerTailBound κ (δ / Real.sqrt (Fintype.card I)) (z ^ 30) (z ^ 10))
        (z ^ 5) (z ^ 5) (δ / Real.sqrt (Fintype.card I)) D ≤ z ^ 3 := by
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  have hz1 := absorption_parameter_le_one hS hz.le hsmall
  have hp30 : z ^ 30 ≤ 1 := pow_le_one₀ hz.le hz1
  have hE := F.stageErrorEnvelope_absorbed e h hz hsmall hδ0 hδ hI
  have hcoef : (1 + z ^ 30) * Real.exp ((e.card : ℝ) * D) ≤ 2 * S :=
    mul_le_mul (by linarith) h.exponential_le (Real.exp_pos _).le (by norm_num)
  have hroot : z ^ 30 ≤ S ^ 5 * z ^ 5 := by
    simpa only [pow_zero, one_mul] using
      (absorption_monomial_mono hS hz.le hz1 (a := 0) (b := 30) (c := 5) (d := 5)
        (by omega) (by omega))
  calc
    _ ≤ z ^ 30 + (1 + z ^ 30) * Real.exp ((e.card : ℝ) * D) * (69 * S ^ 4 * z ^ 5) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (by positivity))
    _ ≤ z ^ 30 + (2 * S) * (69 * S ^ 4 * z ^ 5) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef (by positivity))
    _ ≤ 139 * S ^ 5 * z ^ 5 := by nlinarith only [hroot]
    _ ≤ _ := absorption_final_error h.scale_ge hz.le hsmall

end

end Erdos4b.FGKMT.FiniteEdgeFamily
