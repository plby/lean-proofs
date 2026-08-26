import ErdosProblems.Erdos421.ZetaPolynomialEnvelope

/-! # A power-times-logarithm bound for the disk envelope -/

namespace Erdos421

theorem polynomialZetaEnvelope_dilated_bound {K : ℕ} (hK : 0 < K) {R T : ℝ}
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hT : 3 ≤ T) (hlog : 1 ≤ Real.log T) :
    polynomialZetaEnvelope K R (2 * T + R) ≤
      (polynomialZetaStripConstant K + 64) *
        T ^ (R / (K : ℝ)) * Real.log T := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hc := polynomialZetaStripConstant_pos K
  let α := R / (K : ℝ)
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hα1 : α ≤ 1 := by
    dsimp only [α]
    apply (div_le_one (by positivity : (0 : ℝ) < K)).mpr
    linarith
  have hB : 1 ≤ 2 * T + R := by linarith
  have hB3 : 2 * T + R ≤ 3 * T := by linarith
  have hB23 : 2 * T + R + 2 ≤ 3 * T := by linarith
  have hl3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  have hlogB : Real.log (2 * T + R) ≤ 3 * Real.log T := by
    have h := Real.log_le_log (by linarith : 0 < 2 * T + R) hB3
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hTp.ne'] at h
    linarith only [h, hl3, hlog]
  have hlogB2 : Real.log (2 * T + R + 2) ≤ 3 * Real.log T := by
    have h := Real.log_le_log (by linarith : 0 < 2 * T + R + 2) hB23
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hTp.ne'] at h
    linarith only [h, hl3, hlog]
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have h := log_difference_lower (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)
    norm_num at h
    exact h
  have hden : 1 / 2 ≤ (K : ℝ) * Real.log 2 := by
    nlinarith
  have hcoef : 1 + Real.log (2 * T + R) / ((K : ℝ) * Real.log 2) ≤
      7 * Real.log T := by
    have h := div_le_div_of_nonneg_left (Real.log_nonneg hB)
      (by norm_num : (0 : ℝ) < 1 / 2) hden
    linarith only [h, hlogB, hlog]
  have hpow2 : (2 : ℝ) ^ R ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hR1
  have hpow3 : (3 : ℝ) ^ α ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα1
  have hpowB : (2 * T + R) ^ α ≤ 3 * T ^ α := by
    calc
      _ ≤ (3 * T) ^ α := Real.rpow_le_rpow (by linarith) hB3 hα
      _ = (3 : ℝ) ^ α * T ^ α := Real.mul_rpow (by norm_num) hTp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow3 (Real.rpow_nonneg hTp.le α)
  have hpowT : 1 ≤ T ^ α := Real.one_le_rpow hT1 hα
  let W := T ^ α * Real.log T
  have hW : 1 ≤ W := by
    dsimp only [W]
    nlinarith only [hpowT, hlog]
  have hprod : (1 + Real.log (2 * T + R) / ((K : ℝ) * Real.log 2)) *
      (2 : ℝ) ^ R * (2 * T + R) ^ α ≤ 42 * W := by
    have h := mul_le_mul
      (mul_le_mul hcoef hpow2 (by positivity) (by linarith : 0 ≤ 7 * Real.log T))
      hpowB (by positivity) (by nlinarith : 0 ≤ 7 * Real.log T * 2)
    simpa only [W] using (h.trans_eq (by ring))
  have hconst : polynomialZetaStripConstant K + 12 ≤
      (polynomialZetaStripConstant K + 12) * W :=
    le_mul_of_one_le_right (by positivity) hW
  have hlogW : Real.log (2 * T + R + 2) ≤ 3 * W := by
    apply hlogB2.trans
    dsimp only [W]
    nlinarith only [hpowT, hlog]
  rw [mul_assoc (polynomialZetaStripConstant K + 64)]
  change _ ≤ (polynomialZetaStripConstant K + 64) * W
  unfold polynomialZetaEnvelope
  change (1 + Real.log (2 * T + R) / ((K : ℝ) * Real.log 2)) *
    (2 : ℝ) ^ R * (2 * T + R) ^ α + polynomialZetaStripConstant K + 12 +
    Real.log (2 * T + R + 2) ≤ _
  nlinarith only [hprod, hconst, hlogW, hW]

end Erdos421
