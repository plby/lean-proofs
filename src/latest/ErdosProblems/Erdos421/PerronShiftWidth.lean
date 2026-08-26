import ErdosProblems.Erdos421.LogPowerWidthBounds

/-! # Uniform contour widths for polynomial ranges of the frequency -/

namespace Erdos421

open Filter Topology

noncomputable def perronShiftWidth (T : ℝ) : ℝ := logPowerZeroWidth (2 * T) / 64

noncomputable def perronWidthCoefficient (K : ℕ) : ℝ :=
  ((2 : ℝ) ^ 44)⁻¹ / (64 * ((K : ℝ) + 1) ^ (15 / 16 : ℝ))

theorem perronWidthCoefficient_pos (K : ℕ) : 0 < perronWidthCoefficient K := by
  unfold perronWidthCoefficient
  exact div_pos (by positivity) (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (by positivity) _))

theorem perronShiftWidth_pos {T : ℝ} (hT : 1 < T) : 0 < perronShiftWidth T := by
  exact div_pos (logPowerZeroWidth_pos (by linarith : 1 < 2 * T)) (by norm_num)

theorem perronShiftWidth_le {T : ℝ} (hT : Real.exp 1 ≤ T) : perronShiftWidth T ≤ 1 / 64 := by
  have hTp : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log (2 * T) := by
    have h := Real.log_le_log (Real.exp_pos 1) (hT.trans (by linarith : T ≤ 2 * T))
    rwa [Real.log_exp] at h
  exact div_le_div_of_nonneg_right (logPowerZeroWidth_le_one hlog) (by norm_num)

theorem perronShiftWidth_fits_half_height {T : ℝ} (hT : 1 < T) :
    perronShiftWidth T ≤ logPowerZeroWidth (T + T / 2) / 64 := by
  have hwidth := logPowerZeroWidth_antitone (by linarith : 1 < T + T / 2)
    (by linarith : T + T / 2 ≤ 2 * T)
  exact div_le_div_of_nonneg_right hwidth (by norm_num)

theorem logarithmic_polynomial_frequency_bound {x T : ℝ} (hx : 2 ≤ x) (hT : 0 < T)
    (K : ℕ) (hupper : T ≤ x ^ K) :
    Real.log (2 * T) ≤ ((K : ℝ) + 1) * Real.log x := by
  have hxp : 0 < x := by linarith
  have hlog := Real.log_le_log hT hupper
  rw [Real.log_pow] at hlog
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne']
  nlinarith only [hlog, htwo]

theorem perronShiftWidth_lower {x T : ℝ} (hx : 2 ≤ x) (hT : 1 < T)
    (K : ℕ) (hupper : T ≤ x ^ K) :
    perronWidthCoefficient K / (Real.log x) ^ (15 / 16 : ℝ) ≤ perronShiftWidth T := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogT : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hl := logarithmic_polynomial_frequency_bound hx (by linarith : 0 < T) K hupper
  have hp := Real.rpow_le_rpow hlogT.le hl (by norm_num : (0 : ℝ) ≤ 15 / 16)
  rw [Real.mul_rpow (by positivity : 0 ≤ (K : ℝ) + 1) hlogx.le] at hp
  calc
    _ = ((2 : ℝ) ^ 44)⁻¹ /
        (64 * (((K : ℝ) + 1) ^ (15 / 16 : ℝ) * (Real.log x) ^ (15 / 16 : ℝ))) := by
      unfold perronWidthCoefficient
      ring
    _ ≤ ((2 : ℝ) ^ 44)⁻¹ / (64 * (Real.log (2 * T)) ^ (15 / 16 : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ = _ := by unfold perronShiftWidth logPowerZeroWidth; ring

theorem perronWidthCoefficient_log_identity (K : ℕ) {L : ℝ} (hL : 0 < L) :
    perronWidthCoefficient K / L ^ (15 / 16 : ℝ) * L =
      perronWidthCoefficient K * L ^ (1 / 16 : ℝ) := by
  have he : L ^ (1 / 16 : ℝ) = L / L ^ (15 / 16 : ℝ) := by
    rw [show (1 / 16 : ℝ) = 1 - 15 / 16 by norm_num, Real.rpow_sub hL, Real.rpow_one]
  rw [he]
  ring

theorem perronShiftWidth_covers_inverse_log_eventually (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ T : ℝ, 1 < T → T ≤ x ^ K → 1 / Real.log x ≤ perronShiftWidth T := by
  have hlim : Tendsto (fun x : ℝ ↦ perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ))
      atTop atTop :=
    Tendsto.const_mul_atTop (perronWidthCoefficient_pos K)
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlim.eventually (eventually_ge_atTop 1)]
    with x hx hlarge
  intro T hT hupper
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsmall : 1 / Real.log x ≤ perronWidthCoefficient K / (Real.log x) ^ (15 / 16 : ℝ) := by
    apply (div_le_iff₀ hlog).mpr
    rwa [perronWidthCoefficient_log_identity K hlog]
  exact hsmall.trans (perronShiftWidth_lower hx hT K hupper)

end Erdos421
