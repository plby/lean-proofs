import ErdosProblems.Erdos421.StripConstants
import ErdosProblems.Erdos421.ZetaRightHeight

/-! # A uniform norm envelope for the disks in the zero detector -/

namespace Erdos421

open Complex Metric

noncomputable def zetaStripEnvelope (r K : ℕ) (η T : ℝ) : ℝ :=
  (1 + Real.log T / (((r : ℝ) + 1) * Real.log 2)) *
    (2 : ℝ) ^ η * T ^ (η / ((r : ℝ) + 1)) +
    131072 * K * ((2 ^ r : ℕ) : ℝ) + 12 + Real.log (T + 2)

theorem zetaStripEnvelope_pos (r K : ℕ) (η : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    0 < zetaStripEnvelope r K η T := by
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl' : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold zetaStripEnvelope
  positivity

theorem riemannZeta_strip_envelope (r K : ℕ) (hK : 2 * r + 4 ≤ K) (hK8 : 8 ≤ K)
    {η T : ℝ} (_hη : 0 ≤ η) (hηD : η ≤ logarithmicSavingExponent r K / 2)
    (s : ℂ) (hs : 1 - η ≤ s.re) (ht : (2 : ℝ) ^ (r + 1) ≤ |s.im|)
    (hT : |s.im| ≤ T) : ‖riemannZeta s‖ ≤ zetaStripEnvelope r K η T := by
  have htwo : (2 : ℝ) ≤ 2 ^ (r + 1) := by
    exact_mod_cast (show 2 ≤ 2 ^ (r + 1) by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ r + 1 by omega))
  have ht2 : 2 ≤ |s.im| := htwo.trans ht
  have hT2 : 2 ≤ T := ht2.trans hT
  have htp : 0 < |s.im| := by linarith
  have hlog : Real.log |s.im| ≤ Real.log T := Real.log_le_log htp hT
  have hlog0 : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogT' : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hden : 0 < ((r : ℝ) + 1) * Real.log 2 := by positivity
  by_cases hs1 : s.re ≤ 1
  · have ha : 0 ≤ 1 - s.re := sub_nonneg.mpr hs1
    have haη : 1 - s.re ≤ η := by linarith
    have hb := riemannZeta_near_one_explicit_bound r K hK hK8 s hs1 (haη.trans hηD) ht
    have hcoef : 1 + Real.log |s.im| / (((r : ℝ) + 1) * Real.log 2) ≤
        1 + Real.log T / (((r : ℝ) + 1) * Real.log 2) := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right hlog hden.le)
    have hpow2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) haη
    have hpowT : |s.im| ^ ((1 - s.re) / ((r : ℝ) + 1)) ≤
        T ^ (η / ((r : ℝ) + 1)) := by
      apply (Real.rpow_le_rpow htp.le hT (by positivity)).trans
      exact Real.rpow_le_rpow_of_exponent_le (by linarith)
        (div_le_div_of_nonneg_right haη (by positivity))
    have hprod := mul_le_mul
      (mul_le_mul hcoef hpow2 (by positivity) (by positivity)) hpowT
      (by positivity) (by positivity)
    unfold zetaStripEnvelope
    linarith
  · have hb := riemannZeta_right_height_bound s (le_of_not_ge hs1) (by linarith)
    have hl := Real.log_le_log (by linarith : 0 < |s.im| + 2)
      (add_le_add hT (le_refl 2))
    have hp : 0 ≤ (1 + Real.log T / (((r : ℝ) + 1) * Real.log 2)) *
        (2 : ℝ) ^ η * T ^ (η / ((r : ℝ) + 1)) := by positivity
    unfold zetaStripEnvelope
    have hc : 0 ≤ 131072 * (K : ℝ) * ((2 ^ r : ℕ) : ℝ) := by positivity
    linarith

theorem riemannZeta_disk_envelope (r K : ℕ) (hK : 2 * r + 4 ≤ K) (hK8 : 8 ≤ K)
    {c : ℂ} {R T : ℝ} (hR : 0 ≤ R) (hRD : R ≤ logarithmicSavingExponent r K / 2)
    (hc : 1 ≤ c.re) (hlo : (2 : ℝ) ^ (r + 1) + R ≤ |c.im|)
    (hhi : |c.im| + R ≤ T) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖riemannZeta (c + z)‖ ≤ zetaStripEnvelope r K R T := by
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hr : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hn
  have hi : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hn
  have hreal : 1 - R ≤ (c + z).re := by
    simp only [Complex.add_re]
    linarith [(abs_le.mp hr).1]
  have hlow : (2 : ℝ) ^ (r + 1) ≤ |(c + z).im| := by
    have h := abs_sub_abs_le_abs_sub c.im (c.im + z.im)
    simp only [sub_add_cancel_left, abs_neg] at h
    simp only [Complex.add_im]
    linarith
  have hhigh : |(c + z).im| ≤ T := by
    simp only [Complex.add_im]
    exact (abs_add_le _ _).trans ((add_le_add le_rfl hi).trans hhi)
  exact riemannZeta_strip_envelope r K hK hK8 hR hRD (c + z) hreal hlow hhigh

end Erdos421
