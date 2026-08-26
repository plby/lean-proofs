import ErdosProblems.Erdos421.PerronKernel
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Absolute convergence and interchange for smoothed Perron integrals -/

namespace Erdos421

open Complex MeasureTheory

noncomputable def perronSummand (a : ℕ → ℂ) (x σ t : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (x : ℂ) ^ ((σ : ℂ) + y * I) * perronKernel ((σ : ℂ) + y * I) *
    LSeries.term a ((σ : ℂ) + (t + y : ℝ) * I) n

theorem perronSummand_norm (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (σ t : ℝ) (n : ℕ) (y : ℝ) :
    ‖perronSummand a x σ t n y‖ =
      (x ^ σ * ‖LSeries.term a (σ : ℂ) n‖) * ‖perronKernel ((σ : ℂ) + y * I)‖ := by
  unfold perronSummand
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  ring

theorem perronSummand_continuous (a : ℕ → ℂ) {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ)
    (t : ℝ) (n : ℕ) : Continuous (perronSummand a x σ t n) := by
  have hz : Continuous (fun y : ℝ ↦ (σ : ℂ) + y * I) := by fun_prop
  have hp := hz.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have hterm : Continuous (fun s : ℂ ↦ LSeries.term a s n) :=
    continuous_iff_continuousAt.mpr (fun s ↦ (LSeries.hasDerivAt_term a n s).continuousAt)
  exact (hp.mul (perronKernel_vertical_continuous hσ)).mul (hterm.comp (by fun_prop))

theorem perronSummand_integrable (a : ℕ → ℂ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ)
    (t : ℝ) (n : ℕ) : Integrable (perronSummand a x σ t n) := by
  have hi := (perronKernel_vertical_integrable hσ).norm.const_mul
    (x ^ σ * ‖LSeries.term a (σ : ℂ) n‖)
  apply hi.mono' (perronSummand_continuous a hx (by linarith) t n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y ↦ (perronSummand_norm a hx σ t n y).le)

theorem integral_norm_perronSummand (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (σ t : ℝ) (n : ℕ) :
    (∫ y : ℝ, ‖perronSummand a x σ t n y‖) =
      (x ^ σ * ‖LSeries.term a (σ : ℂ) n‖) *
        ∫ y : ℝ, ‖perronKernel ((σ : ℂ) + y * I)‖ := by
  simp_rw [perronSummand_norm a hx σ t n]
  exact integral_const_mul _ _

theorem perron_integral_LSeries_eq_tsum {a : ℕ → ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) (t : ℝ) :
    (∫ y : ℝ, (x : ℂ) ^ ((σ : ℂ) + y * I) * perronKernel ((σ : ℂ) + y * I) *
      LSeries a ((σ : ℂ) + (t + y : ℝ) * I)) =
      ∑' n : ℕ, ∫ y : ℝ, perronSummand a x σ t n y := by
  have hs : Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖perronSummand a x σ t n y‖) := by
    have hnorm : Summable (fun n : ℕ ↦ ‖LSeries.term a (σ : ℂ) n‖) :=
      summable_norm_iff.mpr ha
    have h := hnorm.mul_left (x ^ σ * ∫ y : ℝ, ‖perronKernel ((σ : ℂ) + y * I)‖)
    apply h.congr
    intro n
    rw [integral_norm_perronSummand a hx σ t n]
    ring
  have hint := integral_tsum_of_summable_integral_norm
    (perronSummand_integrable a hx hσ t) hs
  rw [hint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    simp only [perronSummand, tsum_mul_left, LSeries])

end Erdos421
