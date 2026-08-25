import ErdosProblems.Erdos48.LogDerivativeSeries

/-!
# Four-character positivity

For a quadratic character `chi1`, the coefficients of the four logarithmic
derivatives used in zero repulsion are nonnegative.  This remains true
after multiplication by every nonnegative power of `log n`.
-/

namespace Linnik

open Complex ArithmeticFunction LSeries
open scoped BigOperators

theorem quadratic_four_character_phase_nonneg
    {q n : ℕ} (chi1 chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ^ 2 = 1) (hn : n ≠ 0) (t : ℝ) :
    0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (chi1 n).re +
      (chi n * (n : ℂ) ^ (-(I * t))).re +
      ((chi * chi1) n * (n : ℂ) ^ (-(I * t))).re := by
  by_cases hunit : IsUnit (n : ZMod q)
  · have hsquare : (chi1 n) ^ 2 = 1 := by
      rw [← chi1.pow_apply' two_ne_zero, hchi1, MulChar.one_apply hunit]
    have hw : ‖chi n * (n : ℂ) ^ (-(I * t))‖ = 1 := by
      rw [norm_mul, ← hunit.unit_spec,
        DirichletCharacter.unit_norm_eq_one chi hunit.unit]
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have hre := (abs_le.mp ((Complex.abs_re_le_norm
      (chi n * (n : ℂ) ^ (-(I * t)))).trans hw.le)).1
    rcases sq_eq_one_iff.mp hsquare with hval | hval
    · simp only [MulChar.one_apply hunit, MulChar.mul_apply, hval, one_re,
        mul_one]
      linarith
    · simp only [MulChar.one_apply hunit, MulChar.mul_apply, hval, one_re,
        neg_re, mul_neg_one, neg_mul]
      ring_nf
      exact le_rfl
  · simp [MulChar.map_nonunit, hunit]

/-- Coefficient-level phase expansion for logarithmically weighted
von Mangoldt Dirichlet series. -/
theorem weighted_vonMangoldt_term_re {q k n : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) :
    (LSeries.term (fun m : ℕ ↦
      (Real.log m : ℂ) ^ k * chi m * (vonMangoldt m : ℂ))
        ((sigma : ℂ) + I * t) n).re =
      Real.log n ^ k * vonMangoldt n * (n : ℝ) ^ (-sigma) *
        (chi n * (n : ℂ) ^ (-(I * t))).re := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    neg_add, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero]
  ring

theorem quadratic_four_weighted_terms_nonneg {q k n : ℕ}
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ^ 2 = 1)
    (sigma t : ℝ) :
    0 ≤ (LSeries.term (fun m : ℕ ↦ (Real.log m : ℂ) ^ k *
        (1 : DirichletCharacter ℂ q) m * (vonMangoldt m : ℂ)) (sigma : ℂ) n).re +
      (LSeries.term (fun m : ℕ ↦ (Real.log m : ℂ) ^ k *
        chi1 m * (vonMangoldt m : ℂ)) (sigma : ℂ) n).re +
      (LSeries.term (fun m : ℕ ↦ (Real.log m : ℂ) ^ k *
        chi m * (vonMangoldt m : ℂ)) ((sigma : ℂ) + I * t) n).re +
      (LSeries.term (fun m : ℕ ↦ (Real.log m : ℂ) ^ k *
        (chi * chi1) m * (vonMangoldt m : ℂ)) ((sigma : ℂ) + I * t) n).re := by
  by_cases hn : n = 0
  · simp [hn]
  have hzero (psi : DirichletCharacter ℂ q) :
      (LSeries.term (fun m : ℕ ↦ (Real.log m : ℂ) ^ k *
        psi m * (vonMangoldt m : ℂ)) (sigma : ℂ) n).re =
      Real.log n ^ k * vonMangoldt n * (n : ℝ) ^ (-sigma) * (psi n).re := by
    simpa using weighted_vonMangoldt_term_re (k := k) (n := n) psi sigma 0
  rw [hzero, hzero, weighted_vonMangoldt_term_re, weighted_vonMangoldt_term_re]
  have hweight : 0 ≤ Real.log n ^ k * vonMangoldt n * (n : ℝ) ^ (-sigma) := by
    positivity
  have h := mul_nonneg hweight (quadratic_four_character_phase_nonneg chi1 chi hchi1 hn t)
  nlinarith

theorem weighted_vonMangoldt_LSeriesSummable {q k : ℕ}
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦
      (Real.log n : ℂ) ^ k * chi n * (vonMangoldt n : ℂ)) s := by
  let a : ℕ → ℂ :=
    (fun n : ℕ ↦ chi n) * fun n : ℕ ↦ (vonMangoldt n : ℂ)
  have hbound : ∀ j : ℕ, abscissaOfAbsConv ((logMul^[j]) a) ≤ 1 := by
    intro j
    induction j with
    | zero => exact Erdos48.abscissaOfAbsConv_twist_vonMangoldt_le_one chi
    | succ j ih =>
      simpa only [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul] using ih
  have hcoeff : (logMul^[k]) a =
      fun n : ℕ ↦ (Real.log n : ℂ) ^ k * chi n * (vonMangoldt n : ℂ) := by
    funext n
    rw [Erdos48.iterate_logMul_apply]
    simp only [a, Pi.mul_apply]
    ring
  rw [← hcoeff]
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((hbound k).trans_lt (by exact_mod_cast hs))

/-- Remove the alternating derivative sign, so that the Dirichlet-series
coefficients are positive logarithmic weights. -/
noncomputable def signedLogDerivative {q : ℕ} [NeZero q]
    (k : ℕ) (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * iteratedDeriv k
    (fun w ↦ -logDeriv (DirichletCharacter.LFunction chi) w) s

theorem signedLogDerivative_eq_LSeries {q : ℕ} [NeZero q]
    (k : ℕ) (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    signedLogDerivative k chi s =
      LSeries (fun n : ℕ ↦ (Real.log n : ℂ) ^ k * chi n * (vonMangoldt n : ℂ)) s := by
  rw [signedLogDerivative,
    Erdos48.iteratedDeriv_neg_logDeriv_LFunction_eq_weighted_LSeries chi hs,
    ← mul_assoc, ← mul_pow]
  simp

/-- Positivity of all high logarithmic derivatives in the four-character
combination. -/
theorem quadratic_four_signedLogDerivatives_nonneg {q : ℕ} [NeZero q]
    (k : ℕ) (chi1 chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    0 ≤ (signedLogDerivative k (1 : DirichletCharacter ℂ q) (sigma : ℂ)).re +
      (signedLogDerivative k chi1 (sigma : ℂ)).re +
      (signedLogDerivative k chi ((sigma : ℂ) + I * t)).re +
      (signedLogDerivative k (chi * chi1) ((sigma : ℂ) + I * t)).re := by
  have hs₀ : 1 < (sigma : ℂ).re := hsigma
  have hs₁ : 1 < ((sigma : ℂ) + I * t).re := by simpa using hsigma
  have hsum₀ := weighted_vonMangoldt_LSeriesSummable (k := k)
    (1 : DirichletCharacter ℂ q) hs₀
  have hsum₁ := weighted_vonMangoldt_LSeriesSummable (k := k) chi1 hs₀
  have hsum₂ := weighted_vonMangoldt_LSeriesSummable (k := k) chi hs₁
  have hsum₃ := weighted_vonMangoldt_LSeriesSummable (k := k) (chi * chi1) hs₁
  rw [signedLogDerivative_eq_LSeries k _ hs₀,
    signedLogDerivative_eq_LSeries k _ hs₀,
    signedLogDerivative_eq_LSeries k _ hs₁,
    signedLogDerivative_eq_LSeries k _ hs₁]
  simp only [LSeries, Complex.re_tsum hsum₀, Complex.re_tsum hsum₁,
    Complex.re_tsum hsum₂, Complex.re_tsum hsum₃]
  have hr₀ := Complex.reCLM.summable hsum₀
  have hr₁ := Complex.reCLM.summable hsum₁
  have hr₂ := Complex.reCLM.summable hsum₂
  have hr₃ := Complex.reCLM.summable hsum₃
  simp only [Complex.reCLM_apply] at hr₀ hr₁ hr₂ hr₃
  rw [← hr₀.tsum_add hr₁, ← (hr₀.add hr₁).tsum_add hr₂,
    ← ((hr₀.add hr₁).add hr₂).tsum_add hr₃]
  exact tsum_nonneg fun n ↦ quadratic_four_weighted_terms_nonneg
    (k := k) (n := n) chi1 chi hchi1 sigma t

end Linnik
