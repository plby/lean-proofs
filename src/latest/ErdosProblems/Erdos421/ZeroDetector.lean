import ErdosProblems.Erdos421.ZeroDerivative

/-! # Detecting a zero from the real logarithmic derivative -/

namespace Erdos421

open Complex ComplexConjugate MeromorphicOn Metric

theorem zeroDerivativeKernel_re (R : ℝ) (w : ℂ) :
    (-1 / w + conj w / (R : ℂ) ^ 2).re =
      -w.re * (1 / normSq w - 1 / R ^ 2) := by
  rw [Complex.add_re, neg_div, one_div, Complex.neg_re, Complex.inv_re,
    ← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.conj_re]
  ring

theorem zeroDerivativeKernel_re_nonneg {R : ℝ} {w : ℂ}
    (hw : w ∈ ball 0 R) (hw0 : w ≠ 0) (hwre : w.re ≤ 0) :
    0 ≤ (-1 / w + conj w / (R : ℂ) ^ 2).re := by
  rw [zeroDerivativeKernel_re]
  apply mul_nonneg (neg_nonneg.mpr hwre)
  apply sub_nonneg.mpr
  apply div_le_div_of_nonneg_left zero_le_one (Complex.normSq_pos.mpr hw0)
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg w) (mem_ball_zero_iff.mp hw).le 2

theorem zeroDerivativeTerm_re_nonneg {f : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hzeros : ∀ z ∈ ball 0 R, f z = 0 → z.re ≤ 0)
    (hw : w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset) :
    0 ≤ ((divisor f (ball 0 R) w : ℂ) *
      (-1 / w + conj w / (R : ℂ) ^ 2)).re := by
  have hws := hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hw
  have hwball := (divisor f (ball 0 R)).supportWithinDomain hws
  have hwzero := (divisor_ne_zero_iff_zero_on_disk hR hf hf0 hwball).mp hws
  have hw0 : w ≠ 0 := by rintro rfl; exact hf0 hwzero
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  exact mul_nonneg (by exact_mod_cast (hf.mono ball_subset_closedBall).divisor_nonneg w)
    (zeroDerivativeKernel_re_nonneg hwball hw0 (hzeros w hwball hwzero))

theorem zero_sum_re_le_logDeriv_add {f : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp A * ‖f 0‖) :
    (∑ w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
      (divisor f (ball 0 R) w : ℂ) * (-1 / w + conj w / (R : ℂ) ^ 2)).re ≤
      (logDeriv f 0).re + 4 * A / R := by
  have hn := logDeriv_sub_zero_sum_bound hR hA hf hf0 hM
  have hre := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hn)
  simp only [Complex.sub_re] at hre
  linarith

theorem logDeriv_re_lower_bound {f : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp A * ‖f 0‖)
    (hzeros : ∀ z ∈ ball 0 R, f z = 0 → z.re ≤ 0) :
    -(4 * A / R) ≤ (logDeriv f 0).re := by
  have hsum : 0 ≤ (∑ w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
      (divisor f (ball 0 R) w : ℂ) * (-1 / w + conj w / (R : ℂ) ^ 2)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun w hw ↦ zeroDerivativeTerm_re_nonneg hR hf hf0 hzeros hw)
  linarith [zero_sum_re_le_logDeriv_add hR hA hf hf0 hM]

theorem zeroDerivativeKernel_re_le_logDeriv_add {f : ℂ → ℂ} {R A : ℝ} {w : ℂ}
    (hR : 0 < R) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp A * ‖f 0‖)
    (hzeros : ∀ z ∈ ball 0 R, f z = 0 → z.re ≤ 0)
    (hw : w ∈ ball 0 R) (hfw : f w = 0) :
    (-1 / w + conj w / (R : ℂ) ^ 2).re ≤ (logDeriv f 0).re + 4 * A / R := by
  classical
  have hdiv := (divisor_ne_zero_iff_zero_on_disk hR hf hf0 hw).mpr hfw
  have hmem := hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mpr hdiv
  have hdivpos : 1 ≤ divisor f (ball 0 R) w :=
    Int.add_one_le_iff.mpr (lt_of_le_of_ne
      ((hf.mono ball_subset_closedBall).divisor_nonneg w) (Ne.symm hdiv))
  have hw0 : w ≠ 0 := by rintro rfl; exact hf0 hfw
  have hk := zeroDerivativeKernel_re_nonneg hw hw0 (hzeros w hw hfw)
  have hsingle : (-1 / w + conj w / (R : ℂ) ^ 2).re ≤
      ((divisor f (ball 0 R) w : ℂ) * (-1 / w + conj w / (R : ℂ) ^ 2)).re := by
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    exact le_mul_of_one_le_left hk (by exact_mod_cast hdivpos)
  have hsum : ((divisor f (ball 0 R) w : ℂ) *
      (-1 / w + conj w / (R : ℂ) ^ 2)).re ≤
      (∑ v ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        (divisor f (ball 0 R) v : ℂ) * (-1 / v + conj v / (R : ℂ) ^ 2)).re := by
    rw [Complex.re_sum]
    exact Finset.single_le_sum
      (fun v hv ↦ zeroDerivativeTerm_re_nonneg hR hf hf0 hzeros hv) hmem
  exact hsingle.trans (hsum.trans (zero_sum_re_le_logDeriv_add hR hA hf hf0 hM))

theorem real_zero_reciprocal_bound {f : ℂ → ℂ} {R A d : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp A * ‖f 0‖)
    (hzeros : ∀ z ∈ ball 0 R, f z = 0 → z.re ≤ 0)
    (hd : 0 < d) (hdR : d < R) (hfd : f (-d) = 0) :
    1 / d - d / R ^ 2 ≤ (logDeriv f 0).re + 4 * A / R := by
  have hw : -(d : ℂ) ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd] using hdR
  have hb := zeroDerivativeKernel_re_le_logDeriv_add hR hA hf hf0 hM hzeros hw hfd
  convert hb using 1
  rw [zeroDerivativeKernel_re]
  simp only [Complex.neg_re, Complex.ofReal_re, neg_neg, normSq_neg,
    normSq_ofReal]
  field_simp

end Erdos421
