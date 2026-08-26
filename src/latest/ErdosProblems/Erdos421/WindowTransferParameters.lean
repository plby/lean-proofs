import ErdosProblems.Erdos421.WindowL1Bounds
import ErdosProblems.Erdos421.FrozenLogSaving

/-! # Common scale and energy parameters for the prime-cutoff transfer -/

namespace Erdos421

open MeasureTheory

theorem prime_transfer_window_scales {X e L δ : ℝ} (hX : 1 ≤ X)
    (hlog : 1 ≤ Real.log X) (he : 0 ≤ e) (hL : 2 ≤ L)
    (hδlo : 16 * Real.pi / X ^ (9 / 10 - e) ≤ δ)
    (hδhi : δ ≤ (Real.log X) ^ (-L)) :
    0 < δ ∧ δ ≤ (Real.log X) ^ (-2 : ℝ) ∧ X ^ (1 / 10 : ℝ) ≤ δ * X := by
  have hXp : 0 < X := by linarith
  have hδ : 0 < δ := (by positivity : 0 < 16 * Real.pi / X ^ (9 / 10 - e)).trans_le hδlo
  refine ⟨hδ, hδhi.trans (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)), ?_⟩
  have hpi : (1 : ℝ) ≤ 16 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ X ^ (1 - (9 / 10 - e)) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = X / X ^ (9 / 10 - e) := by rw [Real.rpow_sub hXp, Real.rpow_one]
    _ ≤ (16 * Real.pi / X ^ (9 / 10 - e)) * X := by
      have h := mul_le_mul_of_nonneg_right hpi
        (div_nonneg hXp.le (Real.rpow_nonneg hXp.le (9 / 10 - e)))
      simpa only [one_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
    _ ≤ _ := mul_le_mul_of_nonneg_right hδlo hXp.le

theorem logarithmic_abs_integral_le_two_errors {f : ℝ → ℝ} (hf : Continuous f)
    {X s τ : ℝ} (hX : 1 < X) (hs : 0 ≤ s) (hτ : 0 < τ)
    (henergy : (∫ y in Real.log X..Real.log (2 * X), |f y| ^ 2) ≤
      36 * s ^ 2 + τ ^ 2 / (Real.log X) ^ 2) :
    (∫ y in Real.log X..Real.log (2 * X), |f y|) ≤ 6 * s + τ / Real.log X := by
  have hlog := Real.log_pos hX
  have ht : 0 < τ / Real.log X := div_pos hτ hlog
  apply logarithmic_dyadic_abs_integral_le_of_energy hf (by linarith)
    (by positivity : 0 < 6 * s + τ / Real.log X)
  apply henergy.trans
  rw [← div_pow]
  nlinarith [mul_nonneg hs ht.le]

theorem logarithmic_abs_integral_le_one_error {f : ℝ → ℝ} (hf : Continuous f)
    {X τ : ℝ} (hX : 1 < X) (hτ : 0 < τ)
    (henergy : (∫ y in Real.log X..Real.log (2 * X), |f y| ^ 2) ≤
      τ ^ 2 / (Real.log X) ^ 2) :
    (∫ y in Real.log X..Real.log (2 * X), |f y|) ≤ τ / Real.log X := by
  apply logarithmic_dyadic_abs_integral_le_of_energy hf (by linarith)
    (div_pos hτ (Real.log_pos hX))
  simpa only [div_pow] using henergy

theorem cutoff_l1_error_absorption {τ L : ℝ} (hτ : 0 < τ) (hL : 0 < L) (hτL : τ ≤ L) :
    τ ^ 2 / L ^ 2 ≤ τ / L := by
  have hsmall : τ / L ≤ 1 := (div_le_one hL).mpr hτL
  rw [← div_pow]
  nlinarith [div_nonneg hτ.le hL.le]

end Erdos421
