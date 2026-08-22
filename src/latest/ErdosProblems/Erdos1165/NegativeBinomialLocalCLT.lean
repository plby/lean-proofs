/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.NegativeBinomial
import ErdosProblems.Erdos1165.StirlingLocalCLT

/-!
# A uniform logarithmic local CLT for the HLOZ negative-binomial mass

This file proves a finite, uniform version of (6.4) in Hao--Li--Okada--Zheng.
The paper writes `bar p(i,j) = p(i,j-i)`.  We work with the failure count
`k = j-i`, whose mean is `i/15`.  Thus the deviation occurring below is
`k-i/15 = j-16i/15`.

No asymptotic local-limit statement is assumed.  The proof starts from the
exact mass in `NegativeBinomial.lean`, applies the Robbins bounds proved in
`StirlingLocalCLT.lean`, and estimates the logarithms by their Taylor series.
-/

open Real
open scoped Nat

namespace Erdos1165.NegativeBinomialLocalCLT

open NegativeBinomial StirlingLocalCLT

/-- The one-step variance in HLOZ's geometric-sum representation. -/
noncomputable def variance : ℝ := 16 / 225

/-- Deviation of the failure count from its mean. -/
noncomputable def deviation (i k : ℕ) : ℝ := (k : ℝ) - (i : ℝ) / 15

/-- The logarithmic error in the Gaussian local approximation to `hlozMass`. -/
noncomputable def logLocalError (i k : ℕ) : ℝ :=
  Real.log (hlozMass i k) + Real.log (2 * Real.pi * variance * i) / 2 +
    deviation i k ^ 2 / (2 * variance * i)

/-- The third-order remainder of `(1+u) log (1+u)`. -/
noncomputable def entropyRemainder (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2

private lemma abs_log_one_add_sub_linear_add_quadratic_le
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
  have hu' : |-u| < 1 := by simpa using hu.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  norm_num [Finset.sum_range_succ, pow_two] at h
  have hden : 0 < 1 - |u| := sub_pos.mpr (hu.trans_lt (by norm_num))
  have hinv : (1 - |u|)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h' : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := by
    convert h using 1
    ring_nf
  calc
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := h'
    _ = |u| ^ 3 * (1 - |u|)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ |u| ^ 3 * 2 := mul_le_mul_of_nonneg_left hinv (pow_nonneg (abs_nonneg u) 3)
    _ = 2 * |u| ^ 3 := by ring

private lemma abs_entropyRemainder_le
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |entropyRemainder u| ≤ 4 * |u| ^ 3 := by
  have hlog := abs_log_one_add_sub_linear_add_quadratic_le hu
  have hu0 : 0 ≤ |u| := abs_nonneg u
  have hu1 : |1 + u| ≤ 3 / 2 := by
    calc
      |1 + u| ≤ 1 + |u| := by simpa using abs_add_le 1 u
      _ ≤ 3 / 2 := by linarith
  have hid : entropyRemainder u =
      (1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2 := by
    unfold entropyRemainder
    ring
  rw [hid]
  calc
    |(1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2| ≤
        |1 + u| * |Real.log (1 + u) - u + u ^ 2 / 2| + |u ^ 3 / 2| :=
      (abs_sub _ _).trans_eq (by rw [abs_mul])
    _ ≤ (3 / 2) * (2 * |u| ^ 3) + |u| ^ 3 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

private lemma abs_log_one_add_le_two_mul_abs
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 2 * |u| := by
  have hrem := abs_log_one_add_sub_linear_add_quadratic_le hu
  have hz : 0 ≤ |u| := abs_nonneg u
  have hid : Real.log (1 + u) =
      (Real.log (1 + u) - u + u ^ 2 / 2) + u - u ^ 2 / 2 := by ring
  rw [hid]
  calc
    |(Real.log (1 + u) - u + u ^ 2 / 2) + u - u ^ 2 / 2| ≤
        |Real.log (1 + u) - u + u ^ 2 / 2| + |u| + |u ^ 2 / 2| := by
      calc
        |(Real.log (1 + u) - u + u ^ 2 / 2) + u - u ^ 2 / 2| ≤
        |(Real.log (1 + u) - u + u ^ 2 / 2) + u| + |u ^ 2 / 2| := abs_sub _ _
        _ ≤ (|Real.log (1 + u) - u + u ^ 2 / 2| + |u|) + |u ^ 2 / 2| :=
          by gcongr; exact abs_add_le _ _
    _ ≤ 2 * |u| ^ 3 + |u| + |u| ^ 2 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ ≤ 2 * |u| := by nlinarith [sq_nonneg (|u| - 1 / 2)]

private lemma coefficient_mul_total {i : ℕ} (hi : 0 < i) (k : ℕ) :
    coefficient i k * (i + k) = (i + k).choose k * i := by
  have h := Nat.choose_mul_succ_eq (i + k - 1) k
  rw [coefficient_eq_choose_add_sub_one hi]
  have htop : i + k - 1 + 1 = i + k := by omega
  have hsub : i + k - k = i := by omega
  simpa only [htop, hsub] using h

/-- Rewriting the stars-and-bars coefficient as a binomial coefficient and
the elementary boundary correction `i/(i+k)`. -/
lemma hlozMass_eq_choose_mul_ratio {i : ℕ} (hi : 0 < i) (k : ℕ) :
    hlozMass i k = ((i + k).choose k : ℝ) * ((i : ℝ) / (i + k)) *
      (15 / 16 : ℝ) ^ i * (1 / 16 : ℝ) ^ k := by
  have hcross : (coefficient i k : ℝ) * (i + k : ℕ) =
      ((i + k).choose k : ℝ) * i := by
    exact_mod_cast coefficient_mul_total hi k
  have htotal : ((i + k : ℕ) : ℝ) ≠ 0 := by positivity
  have hcoef : (coefficient i k : ℝ) =
      ((i + k).choose k : ℝ) * (i : ℝ) / (i + k : ℕ) := by
    apply (eq_div_iff htotal).2
    exact hcross
  unfold hlozMass mass hlozSuccess
  rw [show (1 : ℝ) - 15 / 16 = 1 / 16 by norm_num]
  rw [hcoef]
  norm_num only [Nat.cast_add]
  ring

/-- Exponential (entropy) part of the logarithmic mass. -/
noncomputable def entropyCore (i k : ℕ) : ℝ :=
  ((i + k : ℕ) : ℝ) * Real.log (i + k) - (i : ℝ) * Real.log i -
    (k : ℝ) * Real.log k + (i : ℝ) * Real.log (15 / 16) +
      (k : ℝ) * Real.log (1 / 16)

/-- Square-root prefactor produced by Stirling together with the boundary
factor `i/(i+k)`. -/
noncomputable def prefactorCore (i k : ℕ) : ℝ :=
  (Real.log (i + k) - Real.log i - Real.log k - Real.log (2 * Real.pi)) / 2 +
    Real.log i - Real.log (i + k)

lemma log_hlozMass_eq_core {i k : ℕ} (hi : 0 < i) (hk : 0 < k) :
    Real.log (hlozMass i k) = entropyCore i k + prefactorCore i k +
      logBinomialRemainder (i + k) k := by
  have hchoose : (((i + k).choose k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left k i)).ne'
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have htotal0 : (i : ℝ) + k ≠ 0 := by positivity
  rw [hlozMass_eq_choose_mul_ratio hi]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero hchoose (div_ne_zero hi0 htotal0))
      (pow_ne_zero _ (by norm_num : (15 / 16 : ℝ) ≠ 0)))
      (pow_ne_zero _ (by norm_num : (1 / 16 : ℝ) ≠ 0)),
    Real.log_mul (mul_ne_zero hchoose (div_ne_zero hi0 htotal0))
      (pow_ne_zero _ (by norm_num : (15 / 16 : ℝ) ≠ 0)),
    Real.log_mul hchoose (div_ne_zero hi0 htotal0),
    Real.log_div hi0 htotal0, Real.log_pow, Real.log_pow]
  rw [show Real.log (((i + k).choose k : ℕ) : ℝ) =
      logBinomialMain (i + k) k + logBinomialRemainder (i + k) k by
    simp only [logBinomialRemainder]
    ring]
  simp only [logBinomialMain, logFactorialMain, Nat.cast_add,
    Nat.add_sub_cancel_right]
  unfold entropyCore prefactorCore
  norm_num only [Nat.cast_add]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
  ring

/-- Relative deviation on the total-count scale. -/
noncomputable def totalRelativeDeviation (i k : ℕ) : ℝ :=
  15 * deviation i k / (16 * i)

/-- Relative deviation on the failure-count scale. -/
noncomputable def failureRelativeDeviation (i k : ℕ) : ℝ :=
  15 * deviation i k / i

private lemma total_factorization {i k : ℕ} (hi : 0 < i) :
    (i + k : ℝ) = ((16 / 15 : ℝ) * i) * (1 + totalRelativeDeviation i k) := by
  unfold totalRelativeDeviation deviation
  field_simp
  ring

private lemma failure_factorization {i k : ℕ} (hi : 0 < i) :
    (k : ℝ) = ((1 / 15 : ℝ) * i) * (1 + failureRelativeDeviation i k) := by
  unfold failureRelativeDeviation deviation
  field_simp
  ring

private lemma one_add_totalRelativeDeviation_pos {i k : ℕ} (hi : 0 < i) :
    0 < 1 + totalRelativeDeviation i k := by
  have hbase : (0 : ℝ) < (16 / 15 : ℝ) * i := by positivity
  have hprod : (0 : ℝ) < ((16 / 15 : ℝ) * i) *
      (1 + totalRelativeDeviation i k) := by
    rw [← total_factorization hi]
    positivity
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · exfalso
    linarith

private lemma one_add_failureRelativeDeviation_pos {i k : ℕ}
    (hi : 0 < i) (hk : 0 < k) :
    0 < 1 + failureRelativeDeviation i k := by
  have hbase : (0 : ℝ) < (1 / 15 : ℝ) * i := by positivity
  have hprod : (0 : ℝ) < ((1 / 15 : ℝ) * i) *
      (1 + failureRelativeDeviation i k) := by
    rw [← failure_factorization hi]
    positivity
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · exfalso
    linarith

private lemma log_total_factorization {i k : ℕ} (hi : 0 < i) :
    Real.log (i + k) = Real.log (16 / 15 : ℝ) + Real.log i +
      Real.log (1 + totalRelativeDeviation i k) := by
  rw [total_factorization hi,
    Real.log_mul (by positivity : (16 / 15 : ℝ) * (i : ℝ) ≠ 0)
      (one_add_totalRelativeDeviation_pos hi).ne',
    Real.log_mul (by norm_num : (16 / 15 : ℝ) ≠ 0) (by positivity : (i : ℝ) ≠ 0)]

private lemma log_failure_factorization {i k : ℕ} (hi : 0 < i) (hk : 0 < k) :
    Real.log k = Real.log (1 / 15 : ℝ) + Real.log i +
      Real.log (1 + failureRelativeDeviation i k) := by
  rw [failure_factorization hi,
    Real.log_mul (by positivity : (1 / 15 : ℝ) * (i : ℝ) ≠ 0)
      (one_add_failureRelativeDeviation_pos hi hk).ne',
    Real.log_mul (by norm_num : (1 / 15 : ℝ) ≠ 0) (by positivity : (i : ℝ) ≠ 0)]

private lemma log_success_eq : Real.log (15 / 16 : ℝ) = -Real.log (16 / 15 : ℝ) := by
  rw [show (15 / 16 : ℝ) = (16 / 15 : ℝ)⁻¹ by norm_num, Real.log_inv]

private lemma log_failure_eq : Real.log (1 / 16 : ℝ) =
    Real.log (1 / 15 : ℝ) - Real.log (16 / 15 : ℝ) := by
  rw [← Real.log_div (by norm_num : (1 / 15 : ℝ) ≠ 0)
    (by norm_num : (16 / 15 : ℝ) ≠ 0)]
  norm_num

/-- Exact entropy decomposition: the quadratic Gaussian exponent plus two
third-order Taylor remainders. -/
lemma entropyCore_eq_quadratic_add_remainders {i k : ℕ}
    (hi : 0 < i) (hk : 0 < k) :
    entropyCore i k =
      -(deviation i k ^ 2 / (2 * variance * i)) +
        ((16 / 15 : ℝ) * i) * entropyRemainder (totalRelativeDeviation i k) -
        ((1 / 15 : ℝ) * i) * entropyRemainder (failureRelativeDeviation i k) := by
  rw [entropyCore, log_total_factorization hi, log_failure_factorization hi hk,
    log_success_eq, log_failure_eq]
  unfold entropyRemainder totalRelativeDeviation failureRelativeDeviation deviation variance
  norm_num only [Nat.cast_add]
  field_simp
  ring

/-- Exact variation of the square-root prefactor away from the center. -/
lemma prefactorCore_eq_gaussian_add_log_correction {i k : ℕ}
    (hi : 0 < i) (hk : 0 < k) :
    prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2 =
      -(Real.log (1 + totalRelativeDeviation i k) +
        Real.log (1 + failureRelativeDeviation i k)) / 2 := by
  rw [prefactorCore, log_total_factorization hi, log_failure_factorization hi hk]
  unfold variance
  have hpi : Real.pi ≠ 0 := by positivity
  rw [show (16 / 225 : ℝ) = (16 / 15) * (1 / 15) by norm_num]
  rw [Real.log_mul (by positivity : (2 : ℝ) * Real.pi *
      ((16 / 15 : ℝ) * (1 / 15)) ≠ 0) (by positivity : (i : ℝ) ≠ 0)]
  rw [Real.log_mul (by positivity : (2 : ℝ) * Real.pi ≠ 0)
      (by positivity : (16 / 15 : ℝ) * (1 / 15) ≠ 0)]
  rw [Real.log_mul (by norm_num : (16 / 15 : ℝ) ≠ 0)
      (by norm_num : (1 / 15 : ℝ) ≠ 0)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpi]
  ring

/-- The symmetric moderate window used for the finite local estimate.  It is
strictly inside the support: its lower edge is `i/30 > 0`. -/
def InModerateWindow (i k : ℕ) : Prop :=
  |deviation i k| ≤ (i : ℝ) / 30

private lemma failure_pos_of_window {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) : 0 < k := by
  have hdev : -(i : ℝ) / 30 ≤ deviation i k :=
    by simpa only [neg_div] using (neg_le_of_abs_le hwindow)
  have hkR : (0 : ℝ) < k := by
    unfold deviation at hdev
    have hiR : (0 : ℝ) < i := by positivity
    linarith
  exact_mod_cast hkR

private lemma abs_failureRelativeDeviation_le_half {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |failureRelativeDeviation i k| ≤ 1 / 2 := by
  have hiR : (0 : ℝ) < i := by positivity
  unfold failureRelativeDeviation
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15),
    abs_of_pos hiR]
  calc
    15 * |deviation i k| / (i : ℝ) ≤ 15 * ((i : ℝ) / 30) / i := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwindow (by norm_num)) hiR.le
    _ = 1 / 2 := by field_simp; ring

private lemma abs_totalRelativeDeviation_le_half {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |totalRelativeDeviation i k| ≤ 1 / 2 := by
  have hiR : (0 : ℝ) < i := by positivity
  unfold totalRelativeDeviation
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16), abs_of_pos hiR]
  calc
    15 * |deviation i k| / (16 * (i : ℝ)) ≤
        15 * ((i : ℝ) / 30) / (16 * i) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwindow (by norm_num))
        (by positivity)
    _ ≤ 1 / 2 := by
      field_simp
      nlinarith

/-- Uniform cubic control of the entropy part throughout the moderate window. -/
lemma abs_entropyCore_add_quadratic_le {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |entropyCore i k + deviation i k ^ 2 / (2 * variance * i)| ≤
      904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by
  have hk := failure_pos_of_window hi hwindow
  have ha := abs_entropyRemainder_le (abs_totalRelativeDeviation_le_half hi hwindow)
  have hb := abs_entropyRemainder_le (abs_failureRelativeDeviation_le_half hi hwindow)
  have hiR : (0 : ℝ) < i := by positivity
  rw [entropyCore_eq_quadratic_add_remainders hi hk]
  have hcancel :
      -(deviation i k ^ 2 / (2 * variance * (i : ℝ))) +
          ((16 / 15 : ℝ) * i) * entropyRemainder (totalRelativeDeviation i k) -
          ((1 / 15 : ℝ) * i) * entropyRemainder (failureRelativeDeviation i k) +
          deviation i k ^ 2 / (2 * variance * i) =
        ((16 / 15 : ℝ) * i) * entropyRemainder (totalRelativeDeviation i k) -
          ((1 / 15 : ℝ) * i) * entropyRemainder (failureRelativeDeviation i k) := by ring
  rw [hcancel]
  calc
    |((16 / 15 : ℝ) * i) * entropyRemainder (totalRelativeDeviation i k) -
        ((1 / 15 : ℝ) * i) * entropyRemainder (failureRelativeDeviation i k)| ≤
      |((16 / 15 : ℝ) * i) * entropyRemainder (totalRelativeDeviation i k)| +
        |((1 / 15 : ℝ) * i) * entropyRemainder (failureRelativeDeviation i k)| := abs_sub _ _
    _ = ((16 / 15 : ℝ) * i) * |entropyRemainder (totalRelativeDeviation i k)| +
        ((1 / 15 : ℝ) * i) * |entropyRemainder (failureRelativeDeviation i k)| := by
      simp only [abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 15), abs_of_pos hiR,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 15)]
    _ ≤ ((16 / 15 : ℝ) * i) * (4 * |totalRelativeDeviation i k| ^ 3) +
        ((1 / 15 : ℝ) * i) * (4 * |failureRelativeDeviation i k| ^ 3) := by
      gcongr
    _ = (57825 / 64 : ℝ) * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by
      unfold totalRelativeDeviation failureRelativeDeviation
      simp only [abs_div, abs_mul]
      norm_num [abs_of_pos hiR]
      field_simp
      ring
    _ ≤ 904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by
      have hz : 0 ≤ |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by positivity
      simpa only [div_eq_mul_inv, mul_assoc] using
        (mul_le_mul_of_nonneg_right (by norm_num : (57825 / 64 : ℝ) ≤ 904) hz)

/-- The variation of the Stirling square-root prefactor is linear in the
relative deviation. -/
lemma abs_prefactorCore_add_gaussian_le {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2| ≤
      16 * |deviation i k| / (i : ℝ) := by
  have hk := failure_pos_of_window hi hwindow
  have ha := abs_log_one_add_le_two_mul_abs
    (abs_totalRelativeDeviation_le_half hi hwindow)
  have hb := abs_log_one_add_le_two_mul_abs
    (abs_failureRelativeDeviation_le_half hi hwindow)
  have hiR : (0 : ℝ) < i := by positivity
  rw [prefactorCore_eq_gaussian_add_log_correction hi hk]
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |Real.log (1 + totalRelativeDeviation i k) +
        Real.log (1 + failureRelativeDeviation i k)| / 2 ≤
      (|Real.log (1 + totalRelativeDeviation i k)| +
        |Real.log (1 + failureRelativeDeviation i k)|) / 2 := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (2 * |totalRelativeDeviation i k| +
        2 * |failureRelativeDeviation i k|) / 2 := by gcongr
    _ = (255 / 16 : ℝ) * |deviation i k| / (i : ℝ) := by
      unfold totalRelativeDeviation failureRelativeDeviation
      simp only [abs_div, abs_mul]
      norm_num [abs_of_pos hiR]
      field_simp
      ring
    _ ≤ 16 * |deviation i k| / (i : ℝ) := by
      have hz : 0 ≤ |deviation i k| / (i : ℝ) := by positivity
      simpa only [div_eq_mul_inv, mul_assoc] using
        (mul_le_mul_of_nonneg_right (by norm_num : (255 / 16 : ℝ) ≤ 16) hz)

private lemma failure_lower_bound_of_window {i k : ℕ} (_hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    (i : ℝ) / 30 ≤ k := by
  have hdev : -(i : ℝ) / 30 ≤ deviation i k := by
    simpa only [neg_div] using (neg_le_of_abs_le hwindow)
  unfold deviation at hdev
  linarith

/-- Robbins' three factorial remainders contribute at most `3/i` in the
moderate window. -/
lemma abs_logBinomialRemainder_le_three_div {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |logBinomialRemainder (i + k) k| ≤ 3 / (i : ℝ) := by
  have hk := failure_pos_of_window hi hwindow
  have hb := logBinomialRemainder_robbins_bounds (n := i + k) (k := k)
    hk.ne' (Nat.lt_add_of_pos_left hi)
  have hdiff : (((i + k : ℕ) : ℝ) - k) = (i : ℝ) := by
    push_cast
    ring
  rw [hdiff] at hb
  have hiR : (0 : ℝ) < i := by positivity
  have hkR : (0 : ℝ) < k := by positivity
  have htotalR : (0 : ℝ) < i + k := by positivity
  have hki : (i : ℝ) ≤ 30 * k := by
    linarith [failure_lower_bound_of_window hi hwindow]
  have hinvK : (1 : ℝ) / k ≤ 30 / i := by
    rw [div_le_div_iff₀ hkR hiR]
    linarith
  have hlow : (1 : ℝ) / (12 * k) + 1 / (12 * i) ≤ 3 / i := by
    have hfirst : (1 : ℝ) / (12 * k) ≤ (30 / i) / 12 := by
      calc
        (1 : ℝ) / (12 * k) = ((1 : ℝ) / k) / 12 := by field_simp
        _ ≤ (30 / i) / 12 := by gcongr
    have hsecond : (1 : ℝ) / (12 * i) = ((1 : ℝ) / i) / 12 := by
      field_simp
    calc
      (1 : ℝ) / (12 * k) + 1 / (12 * i) ≤ (30 / i) / 12 + ((1 : ℝ) / i) / 12 :=
        add_le_add hfirst (le_of_eq hsecond)
      _ = (31 / 12 : ℝ) / i := by field_simp; ring
      _ ≤ 3 / i := div_le_div_of_nonneg_right (by norm_num) hiR.le
  have hupp : (1 : ℝ) / (12 * (i + k : ℕ)) ≤ 3 / i := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * (i + k : ℕ)) hiR]
    push_cast
    nlinarith
  rw [abs_le]
  constructor
  · linarith [hb.1, hlow]
  · exact hb.2.trans hupp

/-- Direct finite logarithmic local-CLT estimate, before absorbing the linear
prefactor variation into the conventional HLOZ error scale. -/
lemma abs_logLocalError_le_raw {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |logLocalError i k| ≤
      3 / (i : ℝ) + 16 * |deviation i k| / (i : ℝ) +
        904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by
  have hk := failure_pos_of_window hi hwindow
  have hent := abs_entropyCore_add_quadratic_le hi hwindow
  have hpref := abs_prefactorCore_add_gaussian_le hi hwindow
  have hstir := abs_logBinomialRemainder_le_three_div hi hwindow
  have herr : logLocalError i k =
      (entropyCore i k + deviation i k ^ 2 / (2 * variance * i)) +
        (prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2) +
          logBinomialRemainder (i + k) k := by
    unfold logLocalError
    rw [log_hlozMass_eq_core hi hk]
    ring
  rw [herr]
  calc
    |(entropyCore i k + deviation i k ^ 2 / (2 * variance * i)) +
        (prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2) +
          logBinomialRemainder (i + k) k| ≤
      |entropyCore i k + deviation i k ^ 2 / (2 * variance * i)| +
        |prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2| +
          |logBinomialRemainder (i + k) k| := by
      calc
        |(entropyCore i k + deviation i k ^ 2 / (2 * variance * i)) +
            (prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2) +
              logBinomialRemainder (i + k) k| ≤
          |(entropyCore i k + deviation i k ^ 2 / (2 * variance * i)) +
            (prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2)| +
              |logBinomialRemainder (i + k) k| := abs_add_le _ _
        _ ≤ (|entropyCore i k + deviation i k ^ 2 / (2 * variance * i)| +
            |prefactorCore i k + Real.log (2 * Real.pi * variance * i) / 2|) +
              |logBinomialRemainder (i + k) k| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ 904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 +
        (16 * |deviation i k| / (i : ℝ)) + 3 / (i : ℝ) := by gcongr
    _ = 3 / (i : ℝ) + 16 * |deviation i k| / (i : ℝ) +
        904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by ring

private lemma div_le_inv_sqrt_add_cubic {I x : ℝ} (hI : 1 ≤ I) (hx : 0 ≤ x) :
    x / I ≤ 1 / Real.sqrt I + x ^ 3 / I ^ 2 := by
  have hI0 : 0 ≤ I := hI.trans' zero_le_one
  have hs : 0 < Real.sqrt I := Real.sqrt_pos.2 (zero_lt_one.trans_le hI)
  have hs2 : Real.sqrt I ^ 2 = I := Real.sq_sqrt hI0
  let t : ℝ := x / Real.sqrt I
  have ht0 : 0 ≤ t := div_nonneg hx hs.le
  have ht : t ≤ 1 + t ^ 3 := by
    by_cases ht1 : t ≤ 1
    · exact ht1.trans (le_add_of_nonneg_right (pow_nonneg ht0 3))
    · have h1t : 1 ≤ t := le_of_not_ge ht1
      have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
      calc
        t = t * 1 := by ring
        _ ≤ t * t ^ 2 := mul_le_mul_of_nonneg_left ht2 ht0
        _ = t ^ 3 := by ring
        _ ≤ 1 + t ^ 3 := le_add_of_nonneg_left zero_le_one
  have hscaled : t / Real.sqrt I ≤ (1 + t ^ 3) / Real.sqrt I :=
    div_le_div_of_nonneg_right ht hs.le
  have hleft : t / Real.sqrt I = x / I := by
    dsimp only [t]
    rw [div_div, ← pow_two, hs2]
  have hright : (1 + t ^ 3) / Real.sqrt I =
      1 / Real.sqrt I + x ^ 3 / I ^ 2 := by
    dsimp only [t]
    have hs4 : Real.sqrt I ^ 4 = I ^ 2 := by
      calc
        Real.sqrt I ^ 4 = (Real.sqrt I ^ 2) ^ 2 := by ring
        _ = I ^ 2 := by rw [hs2]
    calc
      (1 + (x / Real.sqrt I) ^ 3) / Real.sqrt I =
          1 / Real.sqrt I + x ^ 3 / Real.sqrt I ^ 4 := by
        field_simp [hs.ne']
      _ = 1 / Real.sqrt I + x ^ 3 / I ^ 2 := by rw [hs4]
  rwa [hleft, hright] at hscaled

/-- **Uniform local CLT in the HLOZ moderate window.**

For every `i ≥ 1` and every failure count within distance `i/30` of its mean,
the logarithm of the exact negative-binomial mass differs from the Gaussian
log-density by at most

`19 / sqrt i + 920 * |k-i/15|^3 / i^2`.

This is an explicit finite form of HLOZ (6.4).  In the paper's shifted
variable `j=i+k`, the deviation is exactly `j-16i/15`. -/
theorem abs_logLocalError_le {i k : ℕ} (hi : 0 < i)
    (hwindow : InModerateWindow i k) :
    |logLocalError i k| ≤ 19 / Real.sqrt i +
      920 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by
  have hraw := abs_logLocalError_le_raw hi hwindow
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hs : 0 < Real.sqrt (i : ℝ) := Real.sqrt_pos.2 (zero_lt_one.trans_le hiR)
  have hsle : Real.sqrt (i : ℝ) ≤ i := Real.sqrt_le_self_iff.mpr (Or.inr hiR)
  have hinv : (1 : ℝ) / i ≤ 1 / Real.sqrt i := by
    exact one_div_le_one_div_of_le hs hsle
  have hlinear := div_le_inv_sqrt_add_cubic hiR (abs_nonneg (deviation i k))
  have hthree : 3 / (i : ℝ) ≤ 3 / Real.sqrt i := by
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hsixteen : 16 * |deviation i k| / (i : ℝ) ≤
      16 * (1 / Real.sqrt i + |deviation i k| ^ 3 / (i : ℝ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 16)
    simpa only [div_eq_mul_inv, mul_assoc] using h
  calc
    |logLocalError i k| ≤
        3 / (i : ℝ) + 16 * |deviation i k| / (i : ℝ) +
          904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := hraw
    _ ≤ 3 / Real.sqrt i +
        16 * (1 / Real.sqrt i + |deviation i k| ^ 3 / (i : ℝ) ^ 2) +
          904 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by
      exact add_le_add (add_le_add hthree hsixteen) le_rfl
    _ = 19 / Real.sqrt i +
        920 * |deviation i k| ^ 3 / (i : ℝ) ^ 2 := by ring

/-! ## The paper's shifted variable -/

/-- HLOZ write `bar p(i,j)=p(i,j-i)`. -/
noncomputable def shiftedMass (i j : ℕ) : ℝ := hlozMass i (j - i)

/-- In the shifted variable, the Gaussian center is `16i/15`. -/
noncomputable def shiftedDeviation (i j : ℕ) : ℝ :=
  (j : ℝ) - 16 * (i : ℝ) / 15

/-- The logarithmic error in exactly the variables of HLOZ (6.4). -/
noncomputable def shiftedLogLocalError (i j : ℕ) : ℝ :=
  Real.log (shiftedMass i j) + Real.log (2 * Real.pi * variance * i) / 2 +
    shiftedDeviation i j ^ 2 / (2 * variance * i)

lemma deviation_sub_eq_shiftedDeviation {i j : ℕ} (hij : i ≤ j) :
    deviation i (j - i) = shiftedDeviation i j := by
  unfold deviation shiftedDeviation
  rw [Nat.cast_sub hij]
  ring

/-- HLOZ (6.4), in its original shifted variable, on the explicit finite
window `|j-16i/15| ≤ i/30`. -/
theorem abs_shiftedLogLocalError_le {i j : ℕ} (hi : 0 < i) (hij : i ≤ j)
    (hwindow : |shiftedDeviation i j| ≤ (i : ℝ) / 30) :
    |shiftedLogLocalError i j| ≤ 19 / Real.sqrt i +
      920 * |shiftedDeviation i j| ^ 3 / (i : ℝ) ^ 2 := by
  have hdev := deviation_sub_eq_shiftedDeviation hij
  have hmoderate : InModerateWindow i (j - i) := by
    unfold InModerateWindow
    rwa [hdev]
  have h := abs_logLocalError_le hi hmoderate
  unfold logLocalError at h
  unfold shiftedLogLocalError shiftedMass
  rwa [hdev] at h

end Erdos1165.NegativeBinomialLocalCLT
