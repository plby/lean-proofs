import ErdosProblems.Erdos421.ZetaLogDerivativeRight
import ErdosProblems.Erdos421.ZetaPerronIntegrand
import ErdosProblems.Erdos421.IntegralSquareTails

/-! # Absolute convergence and quantitative tails of the actual Perron integral -/

namespace Erdos421

open Complex MeasureTheory

theorem zetaPerronIntegrand_right_log_bound {σ : ℝ} (hσ : 1 < σ) (t y : ℝ) :
    ‖logDeriv riemannZeta ((σ : ℂ) + y * I + t * I)‖ ≤
      -(logDeriv riemannZeta (σ : ℂ)).re := by
  have h := riemannZeta_logDeriv_norm_le_real hσ (y + t)
  have he : (σ : ℂ) + (y + t : ℝ) * I = (σ : ℂ) + y * I + t * I := by
    push_cast
    ring
  rwa [he] at h

theorem zetaPerronIntegrand_right_continuous {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) :
    Continuous (fun y : ℝ ↦ zetaPerronIntegrand x t ((σ : ℂ) + y * I)) := by
  have hd : ∀ y : ℝ, DifferentiableAt ℂ (zetaPerronIntegrand x t) ((σ : ℂ) + y * I) := by
    intro y
    have hs : 1 < ((σ : ℂ) + y * I + t * I).re := by simpa using hσ
    have hs1 : (σ : ℂ) + y * I + t * I ≠ 1 := by
      intro he
      rw [he, one_re] at hs
      exact (lt_irrefl _) hs
    exact zetaPerronIntegrand_differentiableAt hx (by simpa using (by linarith : 0 < σ))
      hs1 (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hcurve : Continuous (fun y : ℝ ↦ (σ : ℂ) + y * I) := by fun_prop
  exact continuous_iff_continuousAt.mpr
    (fun y ↦ (hd y).continuousAt.comp (f := fun v : ℝ ↦ (σ : ℂ) + v * I)
      (x := y) hcurve.continuousAt)

theorem zetaPerronIntegrand_right_integrable {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) :
    Integrable (fun y : ℝ ↦ zetaPerronIntegrand x t ((σ : ℂ) + y * I)) := by
  have hi := integrable_inv_one_add_sq.const_mul
    (4 * x ^ σ * (-(logDeriv riemannZeta (σ : ℂ)).re))
  apply hi.mono' (zetaPerronIntegrand_right_continuous hx hσ t).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y ↦
    zetaPerronIntegrand_vertical_bound hx (by linarith)
      (zetaPerronIntegrand_right_log_bound hσ t y))

theorem zetaPerronIntegrand_right_inverse_square {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ‖zetaPerronIntegrand x t ((σ : ℂ) + y * I)‖ ≤
      (x ^ σ * (-(logDeriv riemannZeta (σ : ℂ)).re)) / y ^ 2 := by
  have hkernel := perronKernel_imaginary_bound
    (s := (σ : ℂ) + y * I) (by simpa using abs_pos.mpr hy)
  simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at hkernel
  rw [zetaPerronIntegrand_norm hx]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg hx.le σ))
    (zetaPerronIntegrand_right_log_bound hσ t y) (norm_nonneg _) (by positivity)
  exact hb.trans_eq (by ring)

theorem zetaPerronIntegrand_tail_bound {x σ H : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (hH : 0 < H) (t : ℝ) :
    ‖(∫ y : ℝ, zetaPerronIntegrand x t ((σ : ℂ) + y * I)) -
      (∫ y : ℝ in -H..H, zetaPerronIntegrand x t ((σ : ℂ) + y * I))‖ ≤
      2 * (x ^ σ * (-(logDeriv riemannZeta (σ : ℂ)).re)) / H := by
  apply norm_integral_sub_symmetric_interval_le (zetaPerronIntegrand_right_integrable hx hσ t) hH
  intro y hy
  exact zetaPerronIntegrand_right_inverse_square hx hσ t (abs_pos.mp (hH.trans hy))

theorem exists_zetaPerron_tail_bound :
    ∃ B > 0, ∃ r > 0, ∀ x σ H t : ℝ, 0 < x → 1 < σ → σ < 1 + r → 0 < H →
      ‖(∫ y : ℝ, zetaPerronIntegrand x t ((σ : ℂ) + y * I)) -
        (∫ y : ℝ in -H..H, zetaPerronIntegrand x t ((σ : ℂ) + y * I))‖ ≤
        2 * (x ^ σ * (1 / (σ - 1) + B)) / H := by
  obtain ⟨B, hB, r, hr, hpole⟩ := exists_riemannZeta_logDeriv_pole_bound
  refine ⟨B, hB, r, hr, ?_⟩
  intro x σ H t hx hσ hσr hH
  apply (zetaPerronIntegrand_tail_bound hx hσ hH t).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hpole σ hσ hσr) (Real.rpow_nonneg hx.le σ)) (by norm_num)) hH.le

end Erdos421
