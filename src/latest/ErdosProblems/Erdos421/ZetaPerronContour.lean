import ErdosProblems.Erdos421.ZetaPerronIntegrand
import ErdosProblems.Erdos421.VerticalContourShift

/-! # Quantitative finite contour bounds for the zeta Perron integral -/

namespace Erdos421

open Complex Filter MeasureTheory Set

theorem vertical_integral_inv_square_bound {F : ℝ → ℂ} {H C : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hbound : ∀ y ∈ Icc (-H) H, ‖F y‖ ≤ C * (1 + y ^ 2)⁻¹) :
    ‖∫ y : ℝ in -H..H, F y‖ ≤ C * Real.pi := by
  have hg := integrable_inv_one_add_sq.const_mul C
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -H ≤ H)
    (Eventually.of_forall (fun y hy ↦ hbound y ⟨hy.1.le, hy.2⟩)) hg.intervalIntegrable
  have hfull := setIntegral_le_integral hg
    (Eventually.of_forall (fun y : ℝ ↦ mul_nonneg hC (by positivity : 0 ≤ (1 + y ^ 2)⁻¹)))
    (s := Ioc (-H) H)
  rw [← intervalIntegral.integral_of_le (by linarith : -H ≤ H)] at hfull
  have h := hb.trans hfull
  rwa [integral_const_mul, integral_univ_inv_one_add_sq] at h

theorem zetaPerronIntegrand_rectangle_bound {x t a b H B : ℝ}
    (hx : 1 ≤ x) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hH : 0 < H) (hB : 0 ≤ B)
    (hpole : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, s + t * I ≠ 1)
    (hzero : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, riemannZeta (s + t * I) ≠ 0)
    (hlog : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, ‖logDeriv riemannZeta (s + t * I)‖ ≤ B) :
    ‖∫ y : ℝ in -H..H, zetaPerronIntegrand x t ((b : ℂ) + y * I)‖ ≤
      4 * Real.pi * x ^ a * B + 2 * (b - a) * (x ^ b * B / H ^ 2) := by
  have hxp : 0 < x := by linarith
  have hF : DifferentiableOn ℂ (zetaPerronIntegrand x t) (Icc a b ×ℂ Icc (-H) H) := by
    intro s hs
    exact (zetaPerronIntegrand_differentiableAt hxp
      (by linarith [hs.1.1] : 0 < s.re) (hpole s hs) (hzero s hs)).differentiableWithinAt
  have hpoint : ∀ r ∈ Icc a b, ∀ y ∈ Icc (-H) H,
      (r : ℂ) + y * I ∈ Icc a b ×ℂ Icc (-H) H := by
    intro r hr y hy
    change ((r : ℂ) + y * I).re ∈ Icc a b ∧ ((r : ℂ) + y * I).im ∈ Icc (-H) H
    simpa using And.intro hr hy
  have htop : ∀ r ∈ Icc a b,
      ‖zetaPerronIntegrand x t ((r : ℂ) + H * I)‖ ≤ x ^ b * B / H ^ 2 := by
    intro r hr
    apply zetaPerronIntegrand_horizontal_bound hx (by simpa using hr.2) hH
      (by simp [abs_of_pos hH])
    exact hlog _ (hpoint r hr H ⟨by linarith, le_rfl⟩)
  have hbottom : ∀ r ∈ Icc a b,
      ‖zetaPerronIntegrand x t ((r : ℂ) + (-H : ℝ) * I)‖ ≤ x ^ b * B / H ^ 2 := by
    intro r hr
    apply zetaPerronIntegrand_horizontal_bound hx (by simpa using hr.2) hH
      (by simp [abs_of_pos hH])
    exact hlog _ (hpoint r hr (-H) ⟨le_rfl, by linarith⟩)
  have hleft : ‖∫ y : ℝ in -H..H, zetaPerronIntegrand x t ((a : ℂ) + y * I)‖ ≤
      4 * Real.pi * x ^ a * B := by
    have hb := vertical_integral_inv_square_bound hH.le
      (by positivity : 0 ≤ 4 * x ^ a * B) (fun y hy ↦
        zetaPerronIntegrand_vertical_bound hxp ha (hlog _ (hpoint a ⟨le_rfl, hab⟩ y hy)))
    exact hb.trans_eq (by ring)
  exact (vertical_integral_shift_norm_le hab hH.le hF htop hbottom).trans
    (add_le_add hleft le_rfl)

end Erdos421
