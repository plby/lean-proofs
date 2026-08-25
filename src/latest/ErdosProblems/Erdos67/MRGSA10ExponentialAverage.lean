import ErdosProblems.Erdos67.MRGSA10TailoredCoefficient

/-!
# Exponential averages in the GS A.10 coefficient identity

After expanding the tailored A.10 coefficient at a fixed factorization, its
dependence on the two auxiliary variables is

`exp (-alpha * x) * exp (-(alpha + 2 * beta) * y)`.

This file evaluates the resulting rectangular integral exactly.  The
statement is kept over `ℂ`, matching the arithmetic-function coefficients
used in the Perron argument.
-/

open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The elementary one-dimensional exponential average used twice in A.10. -/
theorem intervalIntegral_cexp_neg_mul_eq
    {a eta : ℝ} (ha : a ≠ 0) :
    (∫ t : ℝ in 0..eta,
      Complex.exp (-((a : ℂ) * (t : ℂ)))) =
      ((1 : ℂ) - Complex.exp (-((a : ℂ) * (eta : ℂ)))) / (a : ℂ) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hneg : -(a : ℂ) ≠ 0 := neg_ne_zero.mpr haC
  rw [show (fun t : ℝ ↦ Complex.exp (-((a : ℂ) * (t : ℂ)))) =
      fun t : ℝ ↦ Complex.exp ((-(a : ℂ)) * (t : ℂ)) by
    funext t
    congr 1
    ring]
  rw [integral_exp_mul_complex hneg]
  field_simp
  simp

/-- The separated rectangular exponential average. -/
theorem intervalIntegral_intervalIntegral_cexp_two_shift
    {x y eta : ℝ} (hx : x + y ≠ 0) (hy : y ≠ 0) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Complex.exp (-(((x + y : ℝ) : ℂ) * (alpha : ℂ))) *
          Complex.exp (-(((2 * y : ℝ) : ℂ) * (beta : ℂ)))) =
      (((1 : ℂ) - Complex.exp (-(((x + y : ℝ) : ℂ) * (eta : ℂ)))) /
          ((x + y : ℝ) : ℂ)) *
        (((1 : ℂ) - Complex.exp (-(((2 * y : ℝ) : ℂ) * (eta : ℂ)))) /
          ((2 * y : ℝ) : ℂ)) := by
  have h2y : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral_cexp_neg_mul_eq hx,
    intervalIntegral_cexp_neg_mul_eq h2y]

/-- The source A.10 two-shift exponential separates into its `alpha` and
`beta` factors. -/
theorem cexp_two_shift_eq_separated (x y alpha beta : ℝ) :
    Complex.exp (-((alpha : ℂ) * (x : ℂ))) *
        Complex.exp (-((((alpha + 2 * beta : ℝ) : ℂ) * (y : ℂ)))) =
      Complex.exp (-(((x + y : ℝ) : ℂ) * (alpha : ℂ))) *
        Complex.exp (-(((2 * y : ℝ) : ℂ) * (beta : ℂ))) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact rectangular average in the original two-shift form occurring in
the tailored A.10 coefficient. -/
theorem intervalIntegral_intervalIntegral_cexp_original_two_shift
    {x y eta : ℝ} (hx : x + y ≠ 0) (hy : y ≠ 0) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Complex.exp (-((alpha : ℂ) * (x : ℂ))) *
          Complex.exp (-((((alpha + 2 * beta : ℝ) : ℂ) * (y : ℂ))))) =
      (((1 : ℂ) - Complex.exp (-(((x + y : ℝ) : ℂ) * (eta : ℂ)))) /
          ((x + y : ℝ) : ℂ)) *
        (((1 : ℂ) - Complex.exp (-(((2 * y : ℝ) : ℂ) * (eta : ℂ)))) /
          ((2 * y : ℝ) : ℂ)) := by
  simp_rw [cexp_two_shift_eq_separated]
  exact intervalIntegral_intervalIntegral_cexp_two_shift hx hy

/-- Positive-denominator form used directly for the logarithms of the
positive A.10 factor indices. -/
theorem intervalIntegral_intervalIntegral_cexp_original_two_shift_of_pos
    {x y eta : ℝ} (hxy : 0 < x + y) (hy : 0 < y) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Complex.exp (-((alpha : ℂ) * (x : ℂ))) *
          Complex.exp (-((((alpha + 2 * beta : ℝ) : ℂ) * (y : ℂ))))) =
      (((1 : ℂ) - Complex.exp (-(((x + y : ℝ) : ℂ) * (eta : ℂ)))) /
          ((x + y : ℝ) : ℂ)) *
        (((1 : ℂ) - Complex.exp (-(((2 * y : ℝ) : ℂ) * (eta : ℂ)))) /
          ((2 * y : ℝ) : ℂ)) := by
  exact intervalIntegral_intervalIntegral_cexp_original_two_shift
    hxy.ne' hy.ne'

/-- Natural-logarithm form matching the real exponential used in
`gsRealShift`.  The hypotheses are precisely what is available for the two
nontrivial generalized-Mangoldt indices in A.10. -/
theorem intervalIntegral_intervalIntegral_realExp_natLog_two_shift
    {m n : ℕ} {eta : ℝ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (Real.exp (-alpha * Real.log m) : ℂ) *
          (Real.exp (-(alpha + 2 * beta) * Real.log n) : ℂ)) =
      (((1 : ℂ) - Complex.exp (-(((Real.log m + Real.log n : ℝ) : ℂ) *
          (eta : ℂ)))) / ((Real.log m + Real.log n : ℝ) : ℂ)) *
        (((1 : ℂ) - Complex.exp (-(((2 * Real.log n : ℝ) : ℂ) *
          (eta : ℂ)))) / ((2 * Real.log n : ℝ) : ℂ)) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlm : 0 < Real.log m := Real.log_pos hmR
  have hln : 0 < Real.log n := Real.log_pos hnR
  have h := intervalIntegral_intervalIntegral_cexp_original_two_shift_of_pos
    (x := Real.log m) (y := Real.log n) (eta := eta) (by positivity) hln
  have hpoint (alpha beta : ℝ) :
      (Real.exp (-alpha * Real.log m) : ℂ) *
          (Real.exp (-(alpha + 2 * beta) * Real.log n) : ℂ) =
        Complex.exp (-((alpha : ℂ) * (Real.log m : ℂ))) *
          Complex.exp (-((((alpha + 2 * beta : ℝ) : ℂ) *
            (Real.log n : ℂ)))) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp]
    congr 1 <;> push_cast <;> ring_nf
  simp_rw [hpoint]
  exact h

end

end Erdos67.MRHalaszBands
