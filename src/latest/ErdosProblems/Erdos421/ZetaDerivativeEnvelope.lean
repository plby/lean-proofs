import ErdosProblems.Erdos421.LogPowerWidthBounds
import ErdosProblems.Erdos421.ZetaPolynomialEnvelopePower

/-! # A uniform logarithmic amplitude for the derivative disks -/

namespace Erdos421

open Filter Topology

theorem polynomialZetaEnvelope_log_amplitude_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 ≤ R → R ≤ 1 →
      polynomialZetaEnvelope 12 R (2 * T + R) *
        (1 + 1 / (logPowerZeroWidth T / 64)) ≤ Real.exp (2 * Real.log T) := by
  let C : ℝ := polynomialZetaStripConstant 12 + 64
  let D : ℝ := 1 + 64 * (2 : ℝ) ^ 44
  have hC : 0 < C := by dsimp only [C]; linarith [polynomialZetaStripConstant_pos 12]
  have hD : 0 < D := by dsimp only [D]; positivity
  have hlittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)
  have hlim := hlittle.tendsto_div_nhds_zero.const_mul (C * D)
  simp only [Real.rpow_two, Real.rpow_one, mul_zero] at hlim
  have hsmall : ∀ᶠ T : ℝ in atTop, C * D * (Real.log T) ^ 2 ≤ T := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_gt_atTop (0 : ℝ)] with T hlimT hT
    have h : C * D * (Real.log T) ^ 2 / T ≤ 1 := by
      simpa only [mul_div_assoc] using hlimT.le
    exact (div_le_one hT).mp h
  have hlogs : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, eventually_ge_atTop (3 : ℝ), hlogs] with T hsmall hT hlog
  intro R hR hR1
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hwidth : 0 < logPowerZeroWidth T := logPowerZeroWidth_pos (by linarith)
  have henv := polynomialZetaEnvelope_dilated_bound (by decide : 0 < 12) hR hR1 hT hlog
  have hpow : T ^ (R / (12 : ℝ)) ≤ T := by
    apply Real.rpow_le_self_of_one_le hT1
    linarith
  have henv' : polynomialZetaEnvelope 12 R (2 * T + R) ≤ C * T * Real.log T :=
    henv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
      (by linarith))
  have hrecip := logPowerZeroWidth_reciprocal_bound hlog
  calc
    _ ≤ (C * T * Real.log T) * (D * Real.log T) :=
      mul_le_mul henv' hrecip (by positivity) (by positivity)
    _ = (C * D * (Real.log T) ^ 2) * T := by ring
    _ ≤ T * T := mul_le_mul_of_nonneg_right hsmall hTp.le
    _ = Real.exp (2 * Real.log T) := by
      rw [two_mul, Real.exp_add, Real.exp_log hTp]

theorem log_derivative_radius_bound {T : ℝ} (hlog : 1 ≤ Real.log T) :
    16 * (2 * Real.log T) / (logPowerZeroWidth T / 8) ≤
      (2 : ℝ) ^ 52 * (Real.log T) ^ 2 := by
  have hlogp : 0 < Real.log T := by linarith
  have hpow : (Real.log T) ^ (15 / 16 : ℝ) ≤ Real.log T :=
    Real.rpow_le_self_of_one_le hlog (by norm_num)
  have he : 16 * (2 * Real.log T) / (logPowerZeroWidth T / 8) =
      (2 : ℝ) ^ 52 * Real.log T * (Real.log T) ^ (15 / 16 : ℝ) := by
    unfold logPowerZeroWidth
    rw [div_div_eq_mul_div, div_div_eq_mul_div, div_inv_eq_mul]
    norm_num
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (2 : ℝ) ^ 52 * Real.log T)
  exact h.trans_eq (by ring)

end Erdos421
