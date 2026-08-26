import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! # A finite vertical contour displacement with explicit horizontal errors -/

namespace Erdos421

open Complex MeasureTheory Set

theorem vertical_integral_shift_identity {F : ℂ → ℂ} {a b H : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (Icc a b ×ℂ Icc (-H) H)) :
    I * (∫ y : ℝ in -H..H, F ((b : ℂ) + y * I)) =
      I * (∫ y : ℝ in -H..H, F ((a : ℂ) + y * I)) +
        (∫ x : ℝ in a..b, F ((x : ℂ) + H * I)) -
        (∫ x : ℝ in a..b, F ((x : ℂ) + (-H : ℝ) * I)) := by
  let z : ℂ := (a : ℂ) + (-H : ℝ) * I
  let w : ℂ := (b : ℂ) + H * I
  have hrect : DifferentiableOn ℂ F (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    simpa only [z, w, add_re, add_im, ofReal_re, ofReal_im, mul_I_re, mul_I_im,
      neg_zero, add_zero, zero_add, uIcc_of_le hab, uIcc_of_le (by linarith : -H ≤ H)] using hF
  have hz := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hrect
  simp only [z, w, add_re, add_im, ofReal_re, ofReal_im, mul_I_re, mul_I_im,
    neg_zero, add_zero, zero_add, smul_eq_mul] at hz
  linear_combination hz

theorem vertical_integral_shift_norm_le {F : ℂ → ℂ} {a b H B : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (Icc a b ×ℂ Icc (-H) H))
    (htop : ∀ x ∈ Icc a b, ‖F ((x : ℂ) + H * I)‖ ≤ B)
    (hbottom : ∀ x ∈ Icc a b, ‖F ((x : ℂ) + (-H : ℝ) * I)‖ ≤ B) :
    ‖∫ y : ℝ in -H..H, F ((b : ℂ) + y * I)‖ ≤
      ‖∫ y : ℝ in -H..H, F ((a : ℂ) + y * I)‖ + 2 * (b - a) * B := by
  have hioc : ∀ x ∈ uIoc a b, x ∈ Icc a b := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    exact ⟨hx.1.le, hx.2⟩
  have htop' := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx ↦ htop x (hioc x hx))
  have hbottom' := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx ↦ hbottom x (hioc x hx))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at htop' hbottom'
  have he := vertical_integral_shift_identity hab hH hF
  have hnorm : ‖∫ y : ℝ in -H..H, F ((b : ℂ) + y * I)‖ ≤
      ‖∫ y : ℝ in -H..H, F ((a : ℂ) + y * I)‖ +
        ‖∫ x : ℝ in a..b, F ((x : ℂ) + H * I)‖ +
        ‖∫ x : ℝ in a..b, F ((x : ℂ) + (-H : ℝ) * I)‖ := by
    calc
      _ = ‖I * (∫ y : ℝ in -H..H, F ((b : ℂ) + y * I))‖ := by
        simp only [norm_mul, norm_I, one_mul]
      _ = _ := congrArg norm he
      _ ≤ _ := by
        have h := (norm_sub_le
          (I * (∫ y : ℝ in -H..H, F ((a : ℂ) + y * I)) +
            (∫ x : ℝ in a..b, F ((x : ℂ) + H * I)))
          (∫ x : ℝ in a..b, F ((x : ℂ) + (-H : ℝ) * I))).trans
            (add_le_add (norm_add_le _ _) le_rfl)
        simpa only [norm_mul, norm_I, one_mul] using h
  linarith

end Erdos421
