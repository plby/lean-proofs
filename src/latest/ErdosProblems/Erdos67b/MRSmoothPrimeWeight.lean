import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A compact polynomial weight for the prime kernel

On `[1/2, 3]` the weight is a polynomial with double zeros at both
endpoints. It majorizes one on `[1, 2]`. Its first two polynomial
derivatives and uniform bounds are recorded explicitly.
-/

namespace Erdos67b

noncomputable section

def mrPrimeWeightPolynomial (u : ℝ) : ℝ := (u - 1 / 2) ^ 2 * (3 - u) ^ 2

def mrPrimeWeightPolynomialDeriv (u : ℝ) : ℝ :=
  2 * (u - 1 / 2) * (3 - u) ^ 2 - 2 * (u - 1 / 2) ^ 2 * (3 - u)

def mrPrimeWeightPolynomialDerivTwo (u : ℝ) : ℝ :=
  2 * (3 - u) ^ 2 - 8 * (u - 1 / 2) * (3 - u) + 2 * (u - 1 / 2) ^ 2

def mrSmoothPrimeWeight (u : ℝ) : ℝ :=
  if u ∈ Set.Icc (1 / 2 : ℝ) 3 then mrPrimeWeightPolynomial u else 0

theorem mrPrimeWeightPolynomial_nonneg (u : ℝ) : 0 ≤ mrPrimeWeightPolynomial u :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem mrSmoothPrimeWeight_nonneg (u : ℝ) : 0 ≤ mrSmoothPrimeWeight u := by
  unfold mrSmoothPrimeWeight
  split_ifs
  · exact mrPrimeWeightPolynomial_nonneg u
  · exact le_rfl

theorem mrSmoothPrimeWeight_eq_polynomial {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 3) :
    mrSmoothPrimeWeight u = mrPrimeWeightPolynomial u := if_pos hu

theorem mrSmoothPrimeWeight_eq_zero {u : ℝ} (hu : u ∉ Set.Icc (1 / 2 : ℝ) 3) :
    mrSmoothPrimeWeight u = 0 := if_neg hu

theorem mrPrimeWeightPolynomial_ge_one {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    1 ≤ mrPrimeWeightPolynomial u := by
  have hprod : 1 ≤ (u - 1 / 2) * (3 - u) := by
    have hh := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)
    nlinarith
  have hs : 1 ≤ ((u - 1 / 2) * (3 - u)) ^ 2 := by nlinarith
  simpa only [mul_pow, mrPrimeWeightPolynomial] using hs

theorem mrSmoothPrimeWeight_ge_one {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    1 ≤ mrSmoothPrimeWeight u := by
  rw [mrSmoothPrimeWeight_eq_polynomial ⟨by linarith [hu.1], by linarith [hu.2]⟩]
  exact mrPrimeWeightPolynomial_ge_one hu

theorem hasDerivAt_mrPrimeWeightPolynomial (u : ℝ) :
    HasDerivAt mrPrimeWeightPolynomial (mrPrimeWeightPolynomialDeriv u) u := by
  have hh := (((hasDerivAt_id u).sub_const (1 / 2)).pow 2).mul
    (((hasDerivAt_const u (3 : ℝ)).sub (hasDerivAt_id u)).pow 2)
  exact hh.congr_deriv (by dsimp [mrPrimeWeightPolynomialDeriv]; ring)

theorem hasDerivAt_mrPrimeWeightPolynomialDeriv (u : ℝ) :
    HasDerivAt mrPrimeWeightPolynomialDeriv (mrPrimeWeightPolynomialDerivTwo u) u := by
  have ha := (hasDerivAt_id u).sub_const (1 / 2)
  have hb := (hasDerivAt_const u (3 : ℝ)).sub (hasDerivAt_id u)
  have hh := ((ha.const_mul 2).mul (hb.pow 2)).sub (((ha.pow 2).const_mul 2).mul hb)
  exact hh.congr_deriv (by dsimp [mrPrimeWeightPolynomialDerivTwo]; ring)

theorem continuous_mrPrimeWeightPolynomial : Continuous mrPrimeWeightPolynomial := by
  fun_prop [mrPrimeWeightPolynomial]

theorem continuous_mrPrimeWeightPolynomialDeriv : Continuous mrPrimeWeightPolynomialDeriv := by
  fun_prop [mrPrimeWeightPolynomialDeriv]

theorem continuous_mrPrimeWeightPolynomialDerivTwo : Continuous mrPrimeWeightPolynomialDerivTwo := by
  fun_prop [mrPrimeWeightPolynomialDerivTwo]

theorem mrPrimeWeightPolynomial_endpoints :
    mrPrimeWeightPolynomial (1 / 2) = 0 ∧ mrPrimeWeightPolynomial 3 = 0 ∧
    mrPrimeWeightPolynomialDeriv (1 / 2) = 0 ∧ mrPrimeWeightPolynomialDeriv 3 = 0 := by
  norm_num [mrPrimeWeightPolynomial, mrPrimeWeightPolynomialDeriv]

theorem mrPrimeWeightPolynomialDerivTwo_abs_le {u : ℝ}
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) 3) : |mrPrimeWeightPolynomialDerivTwo u| ≤ 75 := by
  have hA : 0 ≤ u - 1 / 2 := by linarith [hu.1]
  have hB : 0 ≤ 3 - u := by linarith [hu.2]
  have hAupper : u - 1 / 2 ≤ 5 / 2 := by linarith [hu.2]
  have hBupper : 3 - u ≤ 5 / 2 := by linarith [hu.1]
  have hAsq : (u - 1 / 2) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hBsq : (3 - u) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hAB : (u - 1 / 2) * (3 - u) ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hABnonneg := mul_nonneg hA hB
  unfold mrPrimeWeightPolynomialDerivTwo
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg (3 - u)]

theorem mrPrimeWeightPolynomial_abs_le {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 3) :
    |mrPrimeWeightPolynomial u| ≤ 40 := by
  have hAsq : (u - 1 / 2) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith [hu.1, hu.2]
  have hBsq : (3 - u) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith [hu.1, hu.2]
  rw [abs_of_nonneg (mrPrimeWeightPolynomial_nonneg u)]
  exact (mul_le_mul hAsq hBsq (sq_nonneg _) (sq_nonneg _)).trans (by norm_num)

theorem mrPrimeWeightPolynomialDeriv_abs_le {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 3) :
    |mrPrimeWeightPolynomialDeriv u| ≤ 64 := by
  have hA : 0 ≤ u - 1 / 2 := by linarith [hu.1]
  have hB : 0 ≤ 3 - u := by linarith [hu.2]
  have hAupper : u - 1 / 2 ≤ 5 / 2 := by linarith [hu.2]
  have hBupper : 3 - u ≤ 5 / 2 := by linarith [hu.1]
  have hAsq : (u - 1 / 2) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hBsq : (3 - u) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hfirst : 2 * (u - 1 / 2) * (3 - u) ^ 2 ≤ 125 / 4 := by
    calc
      _ ≤ (2 * (5 / 2 : ℝ)) * (5 / 2 : ℝ) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAupper (by norm_num)) hBsq
          (sq_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hsecond : 2 * (u - 1 / 2) ^ 2 * (3 - u) ≤ 125 / 4 := by
    calc
      _ ≤ (2 * (5 / 2 : ℝ) ^ 2) * (5 / 2 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAsq (by norm_num)) hBupper hB (by norm_num)
      _ = _ := by norm_num
  have hfNonneg : 0 ≤ 2 * (u - 1 / 2) * (3 - u) ^ 2 := by positivity
  have hsNonneg : 0 ≤ 2 * (u - 1 / 2) ^ 2 * (3 - u) := by positivity
  unfold mrPrimeWeightPolynomialDeriv
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end

end Erdos67b
