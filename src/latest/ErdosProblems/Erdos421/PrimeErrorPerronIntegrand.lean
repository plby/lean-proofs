import ErdosProblems.Erdos421.PrimeErrorPerron
import ErdosProblems.Erdos421.ZetaPerronContour

/-! # Analyticity and boundary estimates for the pole-cancelled Perron integrand -/

namespace Erdos421

open Complex MeasureTheory Set

noncomputable def primeErrorPerronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * perronKernel s * zetaPrimeError s

theorem primeErrorPerronIntegrand_differentiableAt {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hs : 0 < s.re) (hzero : riemannZeta₁ s ≠ 0) :
    DifferentiableAt ℂ (primeErrorPerronIntegrand x) s := by
  have hs0 : s ≠ 0 := by intro he; simp only [he, zero_re, lt_self_iff_false] at hs
  have hsadd : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at h
    linarith
  have hkernel : DifferentiableAt ℂ perronKernel s :=
    (differentiableAt_const (1 : ℂ)).div
      (differentiableAt_id.mul (differentiableAt_id.add_const (1 : ℂ))) (mul_ne_zero hs0 hsadd)
  have hpower : DifferentiableAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  exact (hpower.mul hkernel).mul (analyticAt_zetaPrimeError hzero).differentiableAt

theorem primeErrorPerronIntegrand_norm {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖primeErrorPerronIntegrand x s‖ = x ^ s.re * ‖perronKernel s‖ * ‖zetaPrimeError s‖ := by
  rw [primeErrorPerronIntegrand, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]

theorem primeErrorPerronIntegrand_horizontal_bound {x b B H : ℝ} {s : ℂ}
    (hx : 1 ≤ x) (hsb : s.re ≤ b) (hH : 0 < H) (hsH : |s.im| = H)
    (herror : ‖zetaPrimeError s‖ ≤ B) :
    ‖primeErrorPerronIntegrand x s‖ ≤ x ^ b * B / H ^ 2 := by
  have hxp : 0 < x := by linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans herror
  have hkernel := perronKernel_imaginary_bound (by rwa [hsH] : 0 < |s.im|)
  have hs2 : s.im ^ 2 = H ^ 2 := by rw [← sq_abs s.im, hsH]
  rw [hs2] at hkernel
  rw [primeErrorPerronIntegrand_norm hxp]
  have hb := mul_le_mul
    (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx hsb) hkernel
      (norm_nonneg _) (Real.rpow_nonneg hxp.le _)) herror (norm_nonneg _)
        (by positivity : 0 ≤ x ^ b * (1 / H ^ 2))
  exact hb.trans_eq (by ring)

theorem primeErrorPerronIntegrand_vertical_bound {x σ B : ℝ} (hx : 0 < x)
    (hσ : 1 / 2 ≤ σ) {y : ℝ} (herror : ‖zetaPrimeError ((σ : ℂ) + y * I)‖ ≤ B) :
    ‖primeErrorPerronIntegrand x ((σ : ℂ) + y * I)‖ ≤
      (4 * x ^ σ * B) * (1 + y ^ 2)⁻¹ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans herror
  rw [primeErrorPerronIntegrand_norm hx]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left (perronKernel_vertical_square_bound hσ y)
      (Real.rpow_nonneg hx.le σ)) herror (norm_nonneg _) (by positivity)
  exact hb.trans_eq (by ring)

theorem primeErrorPerronIntegrand_rectangle_bound {x a b H B : ℝ}
    (hx : 1 ≤ x) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hH : 0 < H) (hB : 0 ≤ B)
    (hzero : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, riemannZeta₁ s ≠ 0)
    (herror : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, ‖zetaPrimeError s‖ ≤ B) :
    ‖∫ y : ℝ in -H..H, primeErrorPerronIntegrand x ((b : ℂ) + y * I)‖ ≤
      4 * Real.pi * x ^ a * B + 2 * (b - a) * (x ^ b * B / H ^ 2) := by
  have hxp : 0 < x := by linarith
  have hF : DifferentiableOn ℂ (primeErrorPerronIntegrand x) (Icc a b ×ℂ Icc (-H) H) := by
    intro s hs
    exact (primeErrorPerronIntegrand_differentiableAt hxp
      (by linarith [hs.1.1] : 0 < s.re) (hzero s hs)).differentiableWithinAt
  have hpoint : ∀ r ∈ Icc a b, ∀ y ∈ Icc (-H) H,
      (r : ℂ) + y * I ∈ Icc a b ×ℂ Icc (-H) H := by
    intro r hr y hy
    change ((r : ℂ) + y * I).re ∈ Icc a b ∧ ((r : ℂ) + y * I).im ∈ Icc (-H) H
    simpa using And.intro hr hy
  have htop : ∀ r ∈ Icc a b,
      ‖primeErrorPerronIntegrand x ((r : ℂ) + H * I)‖ ≤ x ^ b * B / H ^ 2 := by
    intro r hr
    apply primeErrorPerronIntegrand_horizontal_bound hx (by simpa using hr.2) hH
      (by simp [abs_of_pos hH])
    exact herror _ (hpoint r hr H ⟨by linarith, le_rfl⟩)
  have hbottom : ∀ r ∈ Icc a b,
      ‖primeErrorPerronIntegrand x ((r : ℂ) + (-H : ℝ) * I)‖ ≤ x ^ b * B / H ^ 2 := by
    intro r hr
    apply primeErrorPerronIntegrand_horizontal_bound hx (by simpa using hr.2) hH
      (by simp [abs_of_pos hH])
    exact herror _ (hpoint r hr (-H) ⟨le_rfl, by linarith⟩)
  have hleft : ‖∫ y : ℝ in -H..H, primeErrorPerronIntegrand x ((a : ℂ) + y * I)‖ ≤
      4 * Real.pi * x ^ a * B := by
    have hb := vertical_integral_inv_square_bound hH.le
      (by positivity : 0 ≤ 4 * x ^ a * B) (fun y hy ↦
        primeErrorPerronIntegrand_vertical_bound hxp ha (herror _ (hpoint a ⟨le_rfl, hab⟩ y hy)))
    exact hb.trans_eq (by ring)
  exact (vertical_integral_shift_norm_le hab hH.le hF htop hbottom).trans
    (add_le_add hleft le_rfl)

end Erdos421
