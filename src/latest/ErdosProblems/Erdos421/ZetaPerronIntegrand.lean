import ErdosProblems.Erdos421.VonMangoldtPerron
import ErdosProblems.Erdos421.ZetaLogDerivativeBound

/-! # Analyticity and boundary bounds for the zeta Perron integrand -/

namespace Erdos421

open Complex

noncomputable def zetaPerronIntegrand (x t : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * perronKernel s * logDeriv riemannZeta (s + t * I)

theorem zetaPerronIntegrand_differentiableAt {x t : ℝ} {s : ℂ}
    (hx : 0 < x) (hs : 0 < s.re) (hs1 : s + t * I ≠ 1)
    (hzero : riemannZeta (s + t * I) ≠ 0) :
    DifferentiableAt ℂ (zetaPerronIntegrand x t) s := by
  have hs0 : s ≠ 0 := by intro he; simp only [he, zero_re, lt_self_iff_false] at hs
  have hsadd : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at h
    linarith
  have hζ := analyticOn_riemannZeta (s + t * I) (by simpa only [Set.mem_compl_iff,
    Set.mem_singleton_iff] using hs1)
  have hlog : DifferentiableAt ℂ (logDeriv riemannZeta) (s + t * I) :=
    (hζ.deriv.div hζ hzero).differentiableAt
  have hkernel : DifferentiableAt ℂ perronKernel s :=
    (differentiableAt_const (1 : ℂ)).div
      (differentiableAt_id.mul (differentiableAt_id.add_const (1 : ℂ))) (mul_ne_zero hs0 hsadd)
  have hpower : DifferentiableAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  exact (hpower.mul hkernel).mul (hlog.comp s (differentiableAt_id.add_const (t * I)))

theorem zetaPerronIntegrand_norm {x : ℝ} (hx : 0 < x) (t : ℝ) (s : ℂ) :
    ‖zetaPerronIntegrand x t s‖ =
      x ^ s.re * ‖perronKernel s‖ * ‖logDeriv riemannZeta (s + t * I)‖ := by
  rw [zetaPerronIntegrand, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]

theorem zetaPerronIntegrand_horizontal_bound {x t b B H : ℝ} {s : ℂ}
    (hx : 1 ≤ x) (hsb : s.re ≤ b) (hH : 0 < H) (hsH : |s.im| = H)
    (hlog : ‖logDeriv riemannZeta (s + t * I)‖ ≤ B) :
    ‖zetaPerronIntegrand x t s‖ ≤ x ^ b * B / H ^ 2 := by
  have hxp : 0 < x := by linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans hlog
  have hkernel := perronKernel_imaginary_bound (by rwa [hsH] : 0 < |s.im|)
  have hs2 : s.im ^ 2 = H ^ 2 := by rw [← sq_abs s.im, hsH]
  rw [hs2] at hkernel
  rw [zetaPerronIntegrand_norm hxp]
  have hb := mul_le_mul
    (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx hsb) hkernel
      (norm_nonneg _) (Real.rpow_nonneg hxp.le _)) hlog (norm_nonneg _)
        (by positivity : 0 ≤ x ^ b * (1 / H ^ 2))
  exact hb.trans_eq (by ring)

theorem zetaPerronIntegrand_vertical_bound {x σ t B : ℝ} (hx : 0 < x)
    (hσ : 1 / 2 ≤ σ) {y : ℝ}
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + y * I + t * I)‖ ≤ B) :
    ‖zetaPerronIntegrand x t ((σ : ℂ) + y * I)‖ ≤
      (4 * x ^ σ * B) * (1 + y ^ 2)⁻¹ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hlog
  rw [zetaPerronIntegrand_norm hx]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left (perronKernel_vertical_square_bound hσ y)
      (Real.rpow_nonneg hx.le σ)) hlog (norm_nonneg _) (by positivity)
  exact hb.trans_eq (by ring)

end Erdos421
