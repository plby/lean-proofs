import ErdosProblems.Erdos421.PrimeErrorPerronIntegrand
import ErdosProblems.Erdos421.ZetaPerronTails
import ErdosProblems.Erdos421.ZetaRightHalfPlane

/-! # Absolute convergence and tails of the pole-cancelled Perron comparison -/

namespace Erdos421

open Complex MeasureTheory

theorem zetaPrimeError_right_bound {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖zetaPrimeError ((σ : ℂ) + t * I)‖ ≤
      -(logDeriv riemannZeta (σ : ℂ)).re + 1 + 1 / (σ - 1) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by intro he; rw [he, one_re] at hs; exact hs.false
  rw [zetaPrimeError_eq hs1 (riemannZeta_ne_zero_of_one_le_re hs.le)]
  have hd := riemannZeta_logDeriv_norm_le_real hσ t
  have hz := norm_riemannZeta_right_halfPlane_le hs
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero] at hz
  exact (norm_add_le _ _).trans (by linarith)

theorem primeErrorPerronIntegrand_right_continuous {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) :
    Continuous (fun y : ℝ ↦ primeErrorPerronIntegrand x ((σ : ℂ) + y * I)) := by
  have hd : ∀ y : ℝ, DifferentiableAt ℂ (primeErrorPerronIntegrand x) ((σ : ℂ) + y * I) := by
    intro y
    have hs : 1 < ((σ : ℂ) + y * I).re := by simpa using hσ
    exact primeErrorPerronIntegrand_differentiableAt hx (by linarith)
      (riemannZeta₁_ne_zero_on_right hs.le)
  have hcurve : Continuous (fun y : ℝ ↦ (σ : ℂ) + y * I) := by fun_prop
  exact continuous_iff_continuousAt.mpr
    (fun y ↦ (hd y).continuousAt.comp (f := fun v : ℝ ↦ (σ : ℂ) + v * I)
      (x := y) hcurve.continuousAt)

theorem primeErrorPerronIntegrand_right_integrable {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ ↦ primeErrorPerronIntegrand x ((σ : ℂ) + y * I)) := by
  have hi := integrable_inv_one_add_sq.const_mul
    (4 * x ^ σ * (-(logDeriv riemannZeta (σ : ℂ)).re + 1 + 1 / (σ - 1)))
  apply hi.mono' (primeErrorPerronIntegrand_right_continuous hx hσ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y ↦
    primeErrorPerronIntegrand_vertical_bound hx (by linarith) (zetaPrimeError_right_bound hσ y))

theorem primeErrorPerronIntegrand_right_inverse_square {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) {y : ℝ} (hy : y ≠ 0) :
    ‖primeErrorPerronIntegrand x ((σ : ℂ) + y * I)‖ ≤
      (x ^ σ * (-(logDeriv riemannZeta (σ : ℂ)).re + 1 + 1 / (σ - 1))) / y ^ 2 := by
  have hkernel := perronKernel_imaginary_bound
    (s := (σ : ℂ) + y * I) (by simpa using abs_pos.mpr hy)
  simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at hkernel
  rw [primeErrorPerronIntegrand_norm hx]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg hx.le σ))
    (zetaPrimeError_right_bound hσ y) (norm_nonneg _) (by positivity)
  exact hb.trans_eq (by ring)

theorem primeErrorPerronIntegrand_tail_bound {x σ H : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (hH : 0 < H) :
    ‖(∫ y : ℝ, primeErrorPerronIntegrand x ((σ : ℂ) + y * I)) -
      (∫ y : ℝ in -H..H, primeErrorPerronIntegrand x ((σ : ℂ) + y * I))‖ ≤
      2 * (x ^ σ * (-(logDeriv riemannZeta (σ : ℂ)).re + 1 + 1 / (σ - 1))) / H := by
  apply norm_integral_sub_symmetric_interval_le
    (primeErrorPerronIntegrand_right_integrable hx hσ) hH
  intro y hy
  exact primeErrorPerronIntegrand_right_inverse_square hx hσ (abs_pos.mp (hH.trans hy))

theorem exists_primeErrorPerron_tail_bound :
    ∃ B > 0, ∃ r > 0, ∀ x σ H : ℝ, 0 < x → 1 < σ → σ < 1 + r → 0 < H →
      ‖(∫ y : ℝ, primeErrorPerronIntegrand x ((σ : ℂ) + y * I)) -
        (∫ y : ℝ in -H..H, primeErrorPerronIntegrand x ((σ : ℂ) + y * I))‖ ≤
        2 * (x ^ σ * (2 / (σ - 1) + B)) / H := by
  obtain ⟨B, hB, r, hr, hpole⟩ := exists_riemannZeta_logDeriv_pole_bound
  refine ⟨B + 1, by linarith, r, hr, ?_⟩
  intro x σ H hx hσ hσr hH
  apply (primeErrorPerronIntegrand_tail_bound hx hσ hH).trans
  apply div_le_div_of_nonneg_right _ hH.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le σ)
  rw [show 2 / (σ - 1) = 1 / (σ - 1) + 1 / (σ - 1) by ring]
  linarith [hpole σ hσ hσr]

end Erdos421
