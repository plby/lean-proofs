import ErdosProblems.Erdos421.ZetaZeroDetector
import Mathlib.Analysis.Complex.Order

/-! # Absolute logarithmic-derivative control in the right half-plane -/

namespace Erdos421

open Complex
open scoped ComplexOrder

theorem nonnegative_LSeries_norm_le_real (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (σ t : ℝ) (hs : LSeriesSummable (fun n ↦ (a n : ℂ)) (σ : ℂ)) :
    ‖LSeries (fun n ↦ (a n : ℂ)) ((σ : ℂ) + t * I)‖ ≤
      (LSeries (fun n ↦ (a n : ℂ)) (σ : ℂ)).re := by
  have he : ∀ n : ℕ,
      ‖LSeries.term (fun m ↦ (a m : ℂ)) ((σ : ℂ) + t * I) n‖ =
        ‖LSeries.term (fun m ↦ (a m : ℂ)) (σ : ℂ) n‖ := by
    intro n
    simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_I_re,
      ofReal_im, neg_zero, add_zero]
  have hn : Summable (fun n ↦ ‖LSeries.term (fun m ↦ (a m : ℂ)) ((σ : ℂ) + t * I) n‖) := by
    simpa only [he] using (summable_norm_iff.mpr hs)
  have hnonneg : ∀ n : ℕ, 0 ≤ LSeries.term (fun m ↦ (a m : ℂ)) (σ : ℂ) n := by
    intro n
    exact LSeries.term_nonneg (by exact_mod_cast ha n) σ
  unfold LSeries
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun m ↦ (a m : ℂ)) ((σ : ℂ) + t * I) n‖ :=
      norm_tsum_le_tsum_norm hn
    _ = ∑' n : ℕ, (LSeries.term (fun m ↦ (a m : ℂ)) (σ : ℂ) n).re := by
      apply tsum_congr
      intro n
      rw [he n]
      exact (Complex.re_eq_norm.mpr (hnonneg n)).symm
    _ = _ := (Complex.re_tsum hs).symm

theorem riemannZeta_logDeriv_norm_le_real {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ -(logDeriv riemannZeta (σ : ℂ)).re := by
  have hs0 : 1 < (σ : ℂ).re := by simpa only [ofReal_re] using hσ
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hb := nonnegative_LSeries_norm_le_real ArithmeticFunction.vonMangoldt
    (fun n ↦ ArithmeticFunction.vonMangoldt_nonneg (n := n)) σ t
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs0)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs0] at hb
  simpa only [logDeriv_apply, neg_div, norm_neg, neg_re] using hb

theorem exists_riemannZeta_logDeriv_right_bound :
    ∃ B > 0, ∃ r > 0, ∀ σ t : ℝ, 1 < σ → σ < 1 + r →
      ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ 1 / (σ - 1) + B := by
  obtain ⟨B, hB, r, hr, hpole⟩ := exists_riemannZeta_logDeriv_pole_bound
  exact ⟨B, hB, r, hr, fun σ t hσ hσr ↦
    (riemannZeta_logDeriv_norm_le_real hσ t).trans (hpole σ hσ hσr)⟩

end Erdos421
