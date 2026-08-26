import ErdosProblems.Erdos421.ZetaLogPowerZeroFree
import ErdosProblems.Erdos421.LogDerivativeInterior

/-! # Logarithmic-derivative estimates using the proved zero-free region -/

namespace Erdos421

open Complex Metric

noncomputable def logPowerZeroWidth (T : ℝ) : ℝ :=
  ((2 : ℝ) ^ 44)⁻¹ / (Real.log T) ^ (15 / 16 : ℝ)

theorem logPowerZeroWidth_pos {T : ℝ} (hT : 1 < T) : 0 < logPowerZeroWidth T := by
  unfold logPowerZeroWidth
  exact div_pos (by positivity) (Real.rpow_pos_of_pos (Real.log_pos hT) _)

theorem logPowerZeroWidth_antitone {S T : ℝ} (hS : 1 < S) (hST : S ≤ T) :
    logPowerZeroWidth T ≤ logPowerZeroWidth S := by
  have hS0 : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos hS
  unfold logPowerZeroWidth
  apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlogS _)
  exact Real.rpow_le_rpow hlogS.le (Real.log_le_log hS0 hST) (by norm_num)

theorem exists_riemannZeta_log_power_disk_nonvanishing :
    ∃ T₀ > 1, ∀ (c : ℂ) (R : ℝ), 0 ≤ R → 1 ≤ c.re → T₀ + R ≤ |c.im| →
      R ≤ logPowerZeroWidth (|c.im| + R) →
      ∀ z ∈ closedBall (0 : ℂ) R, riemannZeta (c + z) ≠ 0 := by
  obtain ⟨T₀, hT₀, hzero⟩ := riemannZeta_eventually_ne_zero_log_power_strip
  refine ⟨T₀, hT₀, ?_⟩
  intro c R hR hc hlo hwidth z hz
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hi : |z.im| ≤ R := (abs_im_le_norm z).trans hn
  have hr : |z.re| ≤ R := (abs_re_le_norm z).trans hn
  have hlow : T₀ ≤ |(c + z).im| := by
    have h := abs_sub_abs_le_abs_sub c.im (c.im + z.im)
    simp only [sub_add_cancel_left, abs_neg] at h
    simp only [add_im]
    linarith
  have hhigh : |(c + z).im| ≤ |c.im| + R := by
    simp only [add_im]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hi)
  have hw := hwidth.trans (logPowerZeroWidth_antitone (hT₀.trans_le hlow) hhigh)
  have hreal : 1 - logPowerZeroWidth |(c + z).im| ≤ (c + z).re := by
    simp only [add_re]
    linarith [(abs_le.mp hr).1]
  have h := hzero (c + z).im (c + z).re hlow hreal
  simpa only [re_add_im] using h

/-- Every analytic input in this estimate is supplied by the proved zero-free
region and growth bounds. Its hypotheses constrain only numerical parameters. -/
theorem exists_riemannZeta_log_derivative_strip_bound :
    ∃ T₀ > 1, ∀ (K : ℕ) (c : ℂ) (R A : ℝ), 12 ≤ K → 1 < c.re → 0 < R → 0 < A →
      R ≤ polynomialLogarithmicExponent K / 2 → T₀ + R ≤ |c.im| →
      (2 : ℝ) ^ K + R ≤ |c.im| → R ≤ logPowerZeroWidth (|c.im| + R) →
      polynomialZetaEnvelope K R (2 * |c.im| + R) * (1 + 1 / (c.re - 1)) ≤ Real.exp A →
      ∀ w : ℂ, ‖w‖ ≤ R / 4 → ‖logDeriv riemannZeta (c + w)‖ ≤ 16 * A / R := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_riemannZeta_log_power_disk_nonvanishing
  refine ⟨T₀, hT₀, ?_⟩
  intro K c R A hK hc hR hA hRD hlo hfreq hwidth hexp w hw
  have hshift : ∀ s ∈ ball c R, s - c ∈ closedBall (0 : ℂ) R := by
    intro s hs
    have hn : ‖s - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hs
    exact mem_closedBall_zero_iff.mpr hn.le
  have hz : ∀ s ∈ ball c R, riemannZeta s ≠ 0 := by
    intro s hs
    have h := hzero c R hR.le hc.le hlo hwidth (s - c) (hshift s hs)
    rwa [show c + (s - c) = s by ring] at h
  have hf : DifferentiableOn ℂ riemannZeta (ball c R) := by
    intro s hs
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro he
    subst s
    have hd : ‖(1 : ℂ) - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hs
    have hi := abs_im_le_norm ((1 : ℂ) - c)
    simp only [sub_im, one_im, zero_sub, abs_neg] at hi
    linarith
  have hT : 1 ≤ 2 * |c.im| + R := by linarith [abs_nonneg c.im]
  have hM := (polynomialZetaEnvelope_pos K R hT).le
  have hb : ∀ s ∈ ball c R, ‖riemannZeta s‖ ≤ Real.exp A * ‖riemannZeta c‖ := by
    intro s hs
    have hen := riemannZeta_polynomial_disk_envelope hK hRD hc.le hfreq
      (by linarith [abs_nonneg c.im] : |c.im| + R ≤ 2 * |c.im| + R) (hshift s hs)
    rw [show c + (s - c) = s by ring] at hen
    have hrel := riemannZeta_norm_relative_to_center hc hM hen
    exact hrel.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  exact logarithmic_derivative_bound_inside_ball hR hA hf hz hb hw

end Erdos421
