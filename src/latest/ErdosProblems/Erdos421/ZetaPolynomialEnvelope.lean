import ErdosProblems.Erdos421.ZetaPolynomialConstants
import ErdosProblems.Erdos421.ZetaGrowthZeroExclusion

/-! # Polynomial-degree norm bounds on the actual zero-detector disks -/

namespace Erdos421

open Complex Metric

noncomputable def polynomialZetaEnvelope (K : ℕ) (η T : ℝ) : ℝ :=
  (1 + Real.log T / ((K : ℝ) * Real.log 2)) *
    (2 : ℝ) ^ η * T ^ (η / (K : ℝ)) +
    polynomialZetaStripConstant K + 12 + Real.log (T + 2)

theorem polynomialZetaEnvelope_pos (K : ℕ) (η : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    0 < polynomialZetaEnvelope K η T := by
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl' : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := polynomialZetaStripConstant_pos K
  unfold polynomialZetaEnvelope
  positivity

theorem riemannZeta_polynomial_strip_envelope {K : ℕ} (hK : 12 ≤ K)
    {η T : ℝ} (hηD : η ≤ polynomialLogarithmicExponent K / 2)
    (s : ℂ) (hs : 1 - η ≤ s.re) (ht : (2 : ℝ) ^ K ≤ |s.im|)
    (hT : |s.im| ≤ T) : ‖riemannZeta s‖ ≤ polynomialZetaEnvelope K η T := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have htwo : (2 : ℝ) ≤ 2 ^ K := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ K by omega)
  have ht2 : 2 ≤ |s.im| := htwo.trans ht
  have hT2 : 2 ≤ T := ht2.trans hT
  have htp : 0 < |s.im| := by linarith
  have hlog : Real.log |s.im| ≤ Real.log T := Real.log_le_log htp hT
  have hlog0 : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogT' : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hden : 0 < (K : ℝ) * Real.log 2 := by positivity
  have hc := polynomialZetaStripConstant_pos K
  by_cases hs1 : s.re ≤ 1
  · have ha : 0 ≤ 1 - s.re := sub_nonneg.mpr hs1
    have haη : 1 - s.re ≤ η := by linarith
    have hb := riemannZeta_polynomial_growth_bound hK s hs1 (haη.trans hηD) ht
    have hcoef : 1 + Real.log |s.im| / ((K : ℝ) * Real.log 2) ≤
        1 + Real.log T / ((K : ℝ) * Real.log 2) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hlog hden.le)
    have hpow2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) haη
    have hpowT : |s.im| ^ ((1 - s.re) / (K : ℝ)) ≤ T ^ (η / (K : ℝ)) := by
      apply (Real.rpow_le_rpow htp.le hT (by positivity)).trans
      exact Real.rpow_le_rpow_of_exponent_le (by linarith)
        (div_le_div_of_nonneg_right haη hKp.le)
    have hprod := mul_le_mul
      (mul_le_mul hcoef hpow2 (by positivity) (by positivity)) hpowT
      (by positivity) (by positivity)
    unfold polynomialZetaEnvelope
    linarith
  · have hb := riemannZeta_right_height_bound s (le_of_not_ge hs1) (by linarith)
    have hl := Real.log_le_log (by linarith : 0 < |s.im| + 2)
      (add_le_add hT (le_refl 2))
    have hp : 0 ≤ (1 + Real.log T / ((K : ℝ) * Real.log 2)) *
        (2 : ℝ) ^ η * T ^ (η / (K : ℝ)) := by positivity
    unfold polynomialZetaEnvelope
    linarith

theorem riemannZeta_polynomial_disk_envelope {K : ℕ} (hK : 12 ≤ K)
    {c : ℂ} {R T : ℝ} (hRD : R ≤ polynomialLogarithmicExponent K / 2)
    (hc : 1 ≤ c.re) (hlo : (2 : ℝ) ^ K + R ≤ |c.im|)
    (hhi : |c.im| + R ≤ T) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖riemannZeta (c + z)‖ ≤ polynomialZetaEnvelope K R T := by
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hr : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hn
  have hi : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hn
  have hreal : 1 - R ≤ (c + z).re := by
    simp only [Complex.add_re]
    linarith [(abs_le.mp hr).1]
  have hlow : (2 : ℝ) ^ K ≤ |(c + z).im| := by
    have h := abs_sub_abs_le_abs_sub c.im (c.im + z.im)
    simp only [sub_add_cancel_left, abs_neg] at h
    simp only [Complex.add_im]
    linarith
  have hhigh : |(c + z).im| ≤ T := by
    simp only [Complex.add_im]
    exact (abs_add_le _ _).trans ((add_le_add le_rfl hi).trans hhi)
  exact riemannZeta_polynomial_strip_envelope hK hRD (c + z) hreal hlow hhigh

theorem riemannZeta_polynomial_two_disks_bound {K : ℕ} (hK : 12 ≤ K)
    {R A u t v : ℝ} (hR : 0 < R) (hRD : R ≤ polynomialLogarithmicExponent K / 2)
    (hu : 0 < u) (hlo : (2 : ℝ) ^ K + R ≤ |t|)
    (hvlo : |t| ≤ |v|) (hvhi : |v| ≤ 2 * |t|)
    (hexp : polynomialZetaEnvelope K R (2 * |t| + R) * (1 + 1 / u) ≤ Real.exp A) :
    ∀ z ∈ sphere (0 : ℂ) R,
      ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I + z)‖ ≤
        Real.exp A * ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I)‖ := by
  have hbase : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hT : 1 ≤ 2 * |t| + R := by linarith [abs_nonneg t]
  have hM := (polynomialZetaEnvelope_pos K R hT).le
  have hc : 1 < (((1 + u : ℝ) : ℂ) + v * I).re := by simp; linarith
  have hlow : (2 : ℝ) ^ K + R ≤ |(((1 + u : ℝ) : ℂ) + v * I).im| := by
    simpa using hlo.trans hvlo
  have hhigh : |(((1 + u : ℝ) : ℂ) + v * I).im| + R ≤ 2 * |t| + R := by
    simpa using add_le_add hvhi (le_refl R)
  intro z hz
  have hb := riemannZeta_polynomial_disk_envelope hK hRD hc.le hlow hhigh
    (sphere_subset_closedBall hz)
  have hrel : ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I + z)‖ ≤
      (polynomialZetaEnvelope K R (2 * |t| + R) * (1 + 1 / u)) *
        ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I)‖ := by
    simpa using riemannZeta_norm_relative_to_center hc hM hb
  exact hrel.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))

end Erdos421
