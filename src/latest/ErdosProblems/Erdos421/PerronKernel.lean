import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # The absolutely integrable kernel for a smoothed Perron formula -/

namespace Erdos421

open Complex MeasureTheory

noncomputable def perronKernel (s : ℂ) : ℂ := 1 / (s * (s + 1))

theorem perronKernel_vertical_norm_le {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    ‖perronKernel ((σ : ℂ) + y * I)‖ ≤ 1 / (σ ^ 2 + y ^ 2) := by
  let s : ℂ := (σ : ℂ) + y * I
  have hs : s.re = σ := by simp [s]
  have hsi : s.im = y := by simp [s]
  have hnorm : ‖s‖ ≤ ‖s + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, normSq_apply, add_re, add_im, one_re, one_im, add_zero]
    rw [hs]
    nlinarith
  have hprod : σ ^ 2 + y ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    have h := mul_le_mul_of_nonneg_left hnorm (norm_nonneg s)
    have he : ‖s‖ * ‖s‖ = σ ^ 2 + y ^ 2 := by
      rw [← pow_two, Complex.sq_norm, normSq_apply, hs, hsi]
      ring
    rwa [he] at h
  change ‖perronKernel s‖ ≤ _
  rw [perronKernel, norm_div, norm_one, norm_mul]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod

theorem perronKernel_vertical_square_bound {σ : ℝ} (hσ : 1 / 2 ≤ σ) (y : ℝ) :
    ‖perronKernel ((σ : ℂ) + y * I)‖ ≤ 4 * (1 + y ^ 2)⁻¹ := by
  have hσp : 0 < σ := by linarith
  apply (perronKernel_vertical_norm_le hσp y).trans
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < σ ^ 2 + y ^ 2)
    (by positivity : 0 < 1 + y ^ 2)).mpr
  nlinarith [sq_nonneg y]

theorem perronKernel_vertical_continuous {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun y : ℝ ↦ perronKernel ((σ : ℂ) + y * I)) := by
  have hleft : ∀ y : ℝ, (σ : ℂ) + y * I ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, zero_re] at hr
    linarith
  have hright : ∀ y : ℝ, (σ : ℂ) + y * I + 1 ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, zero_re, one_re] at hr
    linarith
  unfold perronKernel
  apply Continuous.div continuous_const (by fun_prop)
  intro y
  exact mul_ne_zero (hleft y) (hright y)

theorem perronKernel_vertical_integrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    VerticalIntegrable perronKernel σ := by
  have hcont := perronKernel_vertical_continuous (by linarith : 0 < σ)
  exact (integrable_inv_one_add_sq.const_mul 4).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (perronKernel_vertical_square_bound hσ))

theorem perronKernel_imaginary_bound {s : ℂ} (hs : 0 < |s.im|) :
    ‖perronKernel s‖ ≤ 1 / s.im ^ 2 := by
  have hleft := abs_im_le_norm s
  have hright : |s.im| ≤ ‖s + 1‖ := by
    simpa only [add_im, one_im, add_zero] using abs_im_le_norm (s + 1)
  have hprod : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    have h := mul_le_mul hleft hright (abs_nonneg s.im) (norm_nonneg s)
    simpa only [← pow_two, sq_abs] using h
  rw [perronKernel, norm_div, norm_one, norm_mul]
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_ne_zero (abs_pos.mp hs)) hprod

end Erdos421
