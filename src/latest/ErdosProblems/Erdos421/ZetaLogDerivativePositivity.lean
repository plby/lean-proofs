import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! # The three-four-one inequality for the actual zeta logarithmic derivative -/

namespace Erdos421

open Complex

theorem real_coefficient_LSeries_term_re (a : ℕ → ℝ) (σ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (fun m ↦ (a m : ℂ)) ((σ : ℂ) + t * I) n).re =
      a n * Real.exp (-Real.log n * σ) * Real.cos (Real.log n * t) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add, mul_neg, Real.cos_neg]
  ring_nf

theorem LSeries_term_trigonometric_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun m ↦ (a m : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (fun m ↦ (a m : ℂ)) ((σ : ℂ) + t * I) n).re +
      (LSeries.term (fun m ↦ (a m : ℂ)) ((σ : ℂ) + (2 * t : ℝ) * I) n).re := by
  by_cases hn : n = 0
  · simp [hn]
  have h0 := real_coefficient_LSeries_term_re a σ 0 hn
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_zero, Real.cos_zero, mul_one] at h0
  rw [h0, real_coefficient_LSeries_term_re a σ t hn,
    real_coefficient_LSeries_term_re a σ (2 * t) hn]
  rw [show Real.log n * (2 * t) = 2 * (Real.log n * t) by ring, Real.cos_two_mul]
  have he : 3 * (a n * Real.exp (-Real.log n * σ)) +
      4 * (a n * Real.exp (-Real.log n * σ) * Real.cos (Real.log n * t)) +
      a n * Real.exp (-Real.log n * σ) * (2 * Real.cos (Real.log n * t) ^ 2 - 1) =
      2 * a n * Real.exp (-Real.log n * σ) * (1 + Real.cos (Real.log n * t)) ^ 2 := by ring
  rw [he]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (ha n)) (Real.exp_pos _).le)
    (sq_nonneg _)

theorem LSeries_trigonometric_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (σ t : ℝ)
    (h0 : LSeriesSummable (fun n ↦ (a n : ℂ)) (σ : ℂ))
    (h1 : LSeriesSummable (fun n ↦ (a n : ℂ)) ((σ : ℂ) + t * I))
    (h2 : LSeriesSummable (fun n ↦ (a n : ℂ)) ((σ : ℂ) + (2 * t : ℝ) * I)) :
    0 ≤ 3 * (LSeries (fun n ↦ (a n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n ↦ (a n : ℂ)) ((σ : ℂ) + t * I)).re +
      (LSeries (fun n ↦ (a n : ℂ)) ((σ : ℂ) + (2 * t : ℝ) * I)).re := by
  have hs := (((Complex.hasSum_re h0.hasSum).mul_left 3).add
    ((Complex.hasSum_re h1.hasSum).mul_left 4)).add (Complex.hasSum_re h2.hasSum)
  change 0 ≤ 3 * (∑' n, LSeries.term (fun n ↦ (a n : ℂ)) (σ : ℂ) n).re +
    4 * (∑' n, LSeries.term (fun n ↦ (a n : ℂ)) ((σ : ℂ) + t * I) n).re +
    (∑' n, LSeries.term (fun n ↦ (a n : ℂ)) ((σ : ℂ) + (2 * t : ℝ) * I) n).re
  rw [← hs.tsum_eq]
  exact tsum_nonneg (LSeries_term_trigonometric_nonneg ha σ t)

theorem riemannZeta_logDeriv_trigonometric_bound {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    3 * (logDeriv riemannZeta (σ : ℂ)).re +
      4 * (logDeriv riemannZeta ((σ : ℂ) + t * I)).re +
      (logDeriv riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)).re ≤ 0 := by
  have hs0 : 1 < (σ : ℂ).re := hσ
  have hs1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + (2 * t : ℝ) * I).re := by simpa using hσ
  have h := LSeries_trigonometric_nonneg
    (fun n ↦ ArithmeticFunction.vonMangoldt_nonneg (n := n)) σ t
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs0)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs2)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs0,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs2] at h
  simp only [neg_div, Complex.neg_re] at h
  simpa only [logDeriv_apply] using (by linarith :
    3 * (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)).re +
      (deriv riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)).re ≤ 0)

end Erdos421
