/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsorptionPowers

/-! # A common scalar bound and absorption of the normalizer and vertex errors -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

structure StageAbsorptionBounds (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) (κ D S : ℝ) : Prop where
  scale_ge : 256 ≤ S
  kappa_pos : 0 < κ
  degree_nonneg : 0 ≤ D
  card_le : (e.card : ℝ) ≤ S
  rank_le : (F.rank : ℝ) ≤ S
  degree_le : D ≤ S
  inverse_le : 1 / κ ≤ S
  rank_inverse_le : 1 / κ ^ F.rank ≤ S
  card_inverse_le : 1 / κ ^ e.card ≤ S
  exponential_le : Real.exp ((e.card : ℝ) * D) ≤ S

theorem stageFirstEnvelope_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 ≤ z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60) :
    F.stageFirstEnvelope e κ δ ≤ z ^ 30 := by
  have hκ := h.kappa_pos
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  calc
    _ ≤ S * S * ((e.card : ℝ) * δ) := by
      unfold stageFirstEnvelope
      gcongr
      · exact h.inverse_le
      · exact h.rank_inverse_le
    _ ≤ S * S * (S * δ) := by gcongr; exact h.card_le
    _ = S ^ 3 * δ := by ring
    _ ≤ S ^ 3 * z ^ 60 := mul_le_mul_of_nonneg_left hδ (by positivity)
    _ ≤ z ^ 30 := absorption_scaled_power_le hS hz hsmall (by omega) (by omega)

theorem stageSecondEnvelope_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 ≤ z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60) :
    F.stageSecondEnvelope e κ δ D ≤ 3 * z ^ 30 := by
  have hκ := h.kappa_pos
  have hD := h.degree_nonneg
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  calc
    _ = (1 / κ) ^ 2 * (1 / κ ^ F.rank) ^ 2 *
        ((2 * (e.card : ℝ) + F.rank) * δ * D) := by
      unfold stageSecondEnvelope
      rw [show 2 * F.rank = F.rank * 2 by omega, pow_mul]
      simp only [one_div, inv_pow]
    _ ≤ S ^ 2 * S ^ 2 * ((2 * S + S) * δ * S) := by
      gcongr
      · exact h.inverse_le
      · exact h.rank_inverse_le
      · exact h.card_le
      · exact h.rank_le
      · exact h.degree_le
    _ = 3 * (S ^ 6 * δ) := by ring
    _ ≤ 3 * (S ^ 6 * z ^ 60) := by gcongr
    _ ≤ 3 * z ^ 30 := mul_le_mul_of_nonneg_left
      (absorption_scaled_power_le hS hz hsmall (by omega) (by omega)) (by norm_num)

theorem stageNormalizerTailBound_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ b : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 < z) (hsmall : S ^ 3 * z ≤ 1) (hb0 : 0 ≤ b)
    (hb : b ≤ δ) (hδ : δ ≤ z ^ 60) :
    F.stageNormalizerTailBound κ b (z ^ 30) (z ^ 10) ≤ 5 * z ^ 10 := by
  have hκ := h.kappa_pos
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  have hz1 := absorption_parameter_le_one hS hz.le hsmall
  have hp30 : z ^ 30 ≤ 1 := pow_le_one₀ hz.le hz1
  have hterm : (1 / κ ^ F.rank) * ((F.rank : ℝ) * b) ≤ z ^ 30 := by
    calc
      _ ≤ S * (S * z ^ 60) := by
        gcongr
        · exact h.rank_inverse_le
        · exact h.rank_le
        · exact hb.trans hδ
      _ = S ^ 2 * z ^ 60 := by ring
      _ ≤ _ := absorption_scaled_power_le hS hz.le hsmall (by omega) (by omega)
  unfold stageNormalizerTailBound
  apply (div_le_iff₀ (pow_pos (pow_pos hz 10) 2)).mpr
  have hproduct : (1 + z ^ 30) * (1 / κ ^ F.rank) * ((F.rank : ℝ) * b) ≤ 2 * z ^ 30 := by
    calc
      _ = (1 + z ^ 30) * ((1 / κ ^ F.rank) * ((F.rank : ℝ) * b)) := by ring
      _ ≤ 2 * z ^ 30 := mul_le_mul (by linarith) hterm (by positivity) (by norm_num)
  calc
    _ ≤ 5 * z ^ 30 := by linarith
    _ = _ := by ring

theorem stageVarianceEnvelope_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {κ D S z δ : ℝ} (h : F.StageAbsorptionBounds e κ D S)
    (hz : 0 ≤ z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60) :
    F.stageVarianceEnvelope e κ δ (z ^ 30) D ≤ 31 * S ^ 2 * z ^ 30 := by
  have hκ := h.kappa_pos
  have hD := h.degree_nonneg
  have hS : 1 ≤ S := by linarith [h.scale_ge]
  have hz1 := absorption_parameter_le_one hS hz hsmall
  have hp30 : z ^ 30 ≤ 1 := pow_le_one₀ hz hz1
  have hp30half := (absorption_half_bounds h.scale_ge hz hsmall).1
  have hL1 := F.stageFirstEnvelope_absorbed e h hz hsmall hδ0 hδ
  have hL2 := F.stageSecondEnvelope_absorbed e h hz hsmall hδ0 hδ
  have hL10 : 0 ≤ F.stageFirstEnvelope e κ δ := by unfold stageFirstEnvelope; positivity
  have hL20 : 0 ≤ F.stageSecondEnvelope e κ δ D := by unfold stageSecondEnvelope; positivity
  have hD2 : D ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hD h.degree_le 2
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have h1 : 4 * z ^ 30 * D ^ 2 ≤ 4 * S ^ 2 * z ^ 30 := by
    nlinarith [mul_le_mul_of_nonneg_left hD2 (by positivity : 0 ≤ 4 * z ^ 30)]
  have h2 : (1 + 4 * z ^ 30) * F.stageSecondEnvelope e κ δ D ≤ 9 * z ^ 30 := by
    have hmul := mul_le_mul (by linarith : 1 + 4 * z ^ 30 ≤ 3) hL2 hL20 (by norm_num)
    nlinarith
  have hmean : 4 * z ^ 30 * (D + F.stageFirstEnvelope e κ δ) +
      F.stageFirstEnvelope e κ δ ≤ 4 * z ^ 30 * (S + 1) + z ^ 30 := by
    exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add h.degree_le (hL1.trans hp30))
      (by positivity)) hL1
  have h3 : 2 * D * (4 * z ^ 30 * (D + F.stageFirstEnvelope e κ δ) +
      F.stageFirstEnvelope e κ δ) ≤ 8 * S ^ 2 * z ^ 30 + 10 * S * z ^ 30 := by
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_left h.degree_le (by norm_num))
      hmean (by positivity) (by positivity : 0 ≤ 2 * S)
    nlinarith
  unfold stageVarianceEnvelope
  have h4 : 9 * z ^ 30 + 10 * S * z ^ 30 ≤ 19 * S ^ 2 * z ^ 30 := by
    have hSsq : 1 ≤ S ^ 2 := one_le_pow₀ hS
    nlinarith [mul_nonneg (sub_nonneg.mpr hS2) (pow_nonneg hz 30),
      mul_nonneg (sub_nonneg.mpr hSsq) (pow_nonneg hz 30)]
  linarith

end

end Erdos4b.FGKMT.FiniteEdgeFamily
