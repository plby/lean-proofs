/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileSmallBall

/-!
# Taylor expansion of the constrained-profile transition kernel

This file supplies the deterministic Taylor step between the finite Stirling
lower kernel in `ProfileSmallBall.lean` and the Gaussian energy in HLOZ
(A.11).  The natural variable for the coefficient

`choose (a + b - 1) b`

is `i = a - 1`; its centered increment is consequently
`d = b - (a - 1)`.  We first give an exact entropy decomposition, then prove
an explicit uniform cubic error bound.  The last section records the exact
recentring of the Gaussian energy along
`m_l = 2*l^2 + Delta_l` and a finite summation bound for its error terms.

No local limit theorem or asymptotic estimate is assumed in this file.
-/

open scoped BigOperators

namespace Erdos1165.ProfileTaylor

noncomputable section

open AppendixFirstMoment ProfileSmallBall StirlingLocalCLT

/-- The centered displacement for the Stirling coefficient
`choose (a+b-1) b`. -/
def edgeDeviation (a b : ℕ) : ℝ := (b : ℝ) - (a - 1 : ℕ)

/-- Entropy contribution of the binomial Stirling main term. -/
def edgeEntropyCore (a b : ℕ) : ℝ :=
  (a + b - 1 : ℕ) * Real.log ((a + b - 1 : ℕ) : ℝ) -
    (b : ℝ) * Real.log b -
      (a - 1 : ℕ) * Real.log ((a - 1 : ℕ) : ℝ) -
      (a + b - 1 : ℕ) * Real.log 2

/-- Square-root contribution of the binomial Stirling main term. -/
def edgePrefactorCore (a b : ℕ) : ℝ :=
  (Real.log ((a + b - 1 : ℕ) : ℝ) - Real.log b -
    Real.log ((a - 1 : ℕ) : ℝ) -
    Real.log (2 * Real.pi)) / 2

/-- The cubic remainder of `(1+u) log (1+u)`. -/
def entropyRemainder (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2

/-- Relative displacement on the total-count scale. -/
def totalRelativeDeviation (a b : ℕ) : ℝ :=
  edgeDeviation a b / (2 * (a - 1 : ℕ))

/-- Relative displacement on the second factorial scale. -/
def rightRelativeDeviation (a b : ℕ) : ℝ :=
  edgeDeviation a b / (a - 1 : ℕ)

lemma edgeBase_pos {a : ℕ} (ha : 2 ≤ a) :
    (0 : ℝ) < (a - 1 : ℕ) := by
  exact_mod_cast (Nat.sub_pos_iff_lt.mpr (by omega : 1 < a))

lemma cast_edgeBase {a : ℕ} (ha : 2 ≤ a) :
    (((a - 1 : ℕ) : ℝ)) = (a : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ a)]
  norm_num

lemma cast_edgeTotal {a b : ℕ} (ha : 2 ≤ a) :
    (((a + b - 1 : ℕ) : ℝ)) = (a : ℝ) + b - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ a + b)]
  push_cast
  ring

private lemma abs_log_one_add_sub_linear_add_quadratic_le
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
  have hu' : |-u| < 1 := by
    simpa using hu.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  norm_num [Finset.sum_range_succ, pow_two] at h
  have hden : 0 < 1 - |u| := sub_pos.mpr (hu.trans_lt (by norm_num))
  have hinv : (1 - |u|)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h' : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := by
    convert h using 1 <;> ring
  calc
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := h'
    _ = |u| ^ 3 * (1 - |u|)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ |u| ^ 3 * 2 :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg (abs_nonneg u) 3)
    _ = 2 * |u| ^ 3 := by ring

lemma abs_entropyRemainder_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
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
    _ ≤ 4 * |u| ^ 3 := by
      nlinarith [pow_nonneg hu0 3]

lemma abs_log_one_add_le_two_mul_abs {u : ℝ} (hu : |u| ≤ 1 / 2) :
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
            |(Real.log (1 + u) - u + u ^ 2 / 2) + u| + |u ^ 2 / 2| :=
          abs_sub _ _
        _ ≤ (|Real.log (1 + u) - u + u ^ 2 / 2| + |u|) + |u ^ 2 / 2| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ 2 * |u| ^ 3 + |u| + |u| ^ 2 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ ≤ 2 * |u| := by
      nlinarith [sq_nonneg (|u| - 1 / 2)]

lemma edgeStirlingExponent_eq_cores {a b : ℕ} (ha : 2 ≤ a) :
    edgeStirlingExponent a b =
      edgeEntropyCore a b + edgePrefactorCore a b - Real.log 2 -
        edgeRobbinsPenalty a b := by
  have hsub : a + b - 1 - b = a - 1 := by omega
  simp only [edgeStirlingExponent, edgeEntropyCore, edgePrefactorCore,
    edgeRobbinsPenalty, logBinomialMain, logFactorialMain, hsub]
  rw [cast_edgeBase ha, cast_edgeTotal ha]
  rw [mul_comm (2 : ℝ) Real.pi]
  ring

lemma total_factorization {a b : ℕ} (ha : 2 ≤ a) :
    ((a + b - 1 : ℕ) : ℝ) = (2 * (a - 1 : ℕ)) *
      (1 + totalRelativeDeviation a b) := by
  unfold totalRelativeDeviation edgeDeviation
  have hai : ((a - 1 : ℕ) : ℝ) ≠ 0 := (edgeBase_pos ha).ne'
  field_simp
  rw [cast_edgeBase ha, cast_edgeTotal ha]
  ring

lemma right_factorization {a b : ℕ} (ha : 2 ≤ a) :
    (b : ℝ) = (a - 1 : ℕ) * (1 + rightRelativeDeviation a b) := by
  unfold rightRelativeDeviation edgeDeviation
  have hai : ((a - 1 : ℕ) : ℝ) ≠ 0 := (edgeBase_pos ha).ne'
  field_simp
  ring

lemma one_add_totalRelativeDeviation_pos {a b : ℕ} (ha : 2 ≤ a) :
    0 < 1 + totalRelativeDeviation a b := by
  have hbase : (0 : ℝ) < 2 * ((a - 1 : ℕ) : ℝ) :=
    mul_pos (by norm_num) (edgeBase_pos ha)
  have hprod : (0 : ℝ) < (2 * ((a - 1 : ℕ) : ℝ)) *
      (1 + totalRelativeDeviation a b) := by
    rw [← total_factorization ha]
    exact_mod_cast (show 0 < a + b - 1 by omega)
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.2
  · exfalso
    linarith [h.1, hbase]

lemma one_add_rightRelativeDeviation_pos {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) :
    0 < 1 + rightRelativeDeviation a b := by
  have hbase : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  have hprod : 0 < (a - 1 : ℕ) * (1 + rightRelativeDeviation a b) := by
    rw [← right_factorization ha]
    positivity
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.2
  · exfalso
    linarith [h.1, hbase]

lemma log_total_factorization {a b : ℕ} (ha : 2 ≤ a) :
    Real.log ((a + b - 1 : ℕ) : ℝ) =
      Real.log 2 + Real.log ((a - 1 : ℕ) : ℝ) +
      Real.log (1 + totalRelativeDeviation a b) := by
  rw [total_factorization (a := a) (b := b) ha,
    Real.log_mul (mul_ne_zero (by norm_num) (edgeBase_pos ha).ne')
      (one_add_totalRelativeDeviation_pos ha).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (edgeBase_pos ha).ne']

lemma log_right_factorization {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    Real.log (b : ℝ) = Real.log ((a - 1 : ℕ) : ℝ) +
      Real.log (1 + rightRelativeDeviation a b) := by
  rw [right_factorization (a := a) (b := b) ha,
    Real.log_mul (edgeBase_pos ha).ne'
      (one_add_rightRelativeDeviation_pos ha hb).ne']

/-- Exact quadratic-plus-cubic decomposition of the edge entropy. -/
lemma edgeEntropyCore_eq_quadratic_add_remainders {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) :
    edgeEntropyCore a b =
      -(edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))) +
        (2 * (a - 1 : ℕ)) * entropyRemainder (totalRelativeDeviation a b) -
          (a - 1 : ℕ) * entropyRemainder (rightRelativeDeviation a b) := by
  rw [edgeEntropyCore, log_total_factorization ha,
    log_right_factorization ha hb,
    total_factorization (a := a) (b := b) ha,
    right_factorization (a := a) (b := b) ha]
  have hrel : rightRelativeDeviation a b =
      2 * totalRelativeDeviation a b := by
    unfold rightRelativeDeviation totalRelativeDeviation
    have hai : ((a - 1 : ℕ) : ℝ) ≠ 0 := (edgeBase_pos ha).ne'
    field_simp
  have hd : edgeDeviation a b =
      ((a - 1 : ℕ) : ℝ) * rightRelativeDeviation a b := by
    unfold rightRelativeDeviation
    have hai : ((a - 1 : ℕ) : ℝ) ≠ 0 := (edgeBase_pos ha).ne'
    field_simp
  rw [hd, hrel]
  unfold entropyRemainder
  field_simp [(edgeBase_pos ha).ne']
  ring

/-- Exact logarithmic correction of the square-root prefactor. -/
lemma edgePrefactorCore_eq_gaussian_add_log_correction {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) :
    edgePrefactorCore a b + Real.log (Real.pi * (a - 1 : ℕ)) / 2 =
      (Real.log (1 + totalRelativeDeviation a b) -
        Real.log (1 + rightRelativeDeviation a b)) / 2 := by
  rw [edgePrefactorCore, log_total_factorization ha,
    log_right_factorization ha hb]
  rw [Real.log_mul (by positivity : Real.pi ≠ 0)
    (edgeBase_pos ha).ne']
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
  ring

/-- The moderate window used for the Taylor expansion. -/
def InEdgeTaylorWindow (a b : ℕ) : Prop :=
  |edgeDeviation a b| ≤ (a - 1 : ℕ) / 2

lemma abs_rightRelativeDeviation_le_half {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    |rightRelativeDeviation a b| ≤ 1 / 2 := by
  have hai : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  unfold rightRelativeDeviation
  rw [abs_div, abs_of_pos hai]
  calc
    |edgeDeviation a b| / ((a - 1 : ℕ) : ℝ) ≤
        (((a - 1 : ℕ) : ℝ) / 2) / ((a - 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hwindow hai.le
    _ = 1 / 2 := by field_simp

lemma abs_totalRelativeDeviation_le_half {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    |totalRelativeDeviation a b| ≤ 1 / 2 := by
  have hai : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  unfold totalRelativeDeviation
  rw [abs_div, abs_mul, abs_of_pos hai, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    |edgeDeviation a b| / (2 * (a - 1 : ℕ)) ≤
        (((a - 1 : ℕ) : ℝ) / 2) / (2 * (a - 1 : ℕ)) := by
      exact div_le_div_of_nonneg_right hwindow (by positivity)
    _ ≤ 1 / 2 := by field_simp; linarith

lemma one_le_b_of_taylorWindow {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) : 1 ≤ b := by
  have hlower := neg_le_of_abs_le hwindow
  have haR : (1 : ℝ) ≤ (a - 1 : ℕ) := by exact_mod_cast (show 1 ≤ a - 1 by omega)
  have hbR : (0 : ℝ) < b := by
    unfold edgeDeviation at hlower
    linarith
  exact_mod_cast hbR

/-- Cubic control of the entropy part in the moderate window. -/
lemma abs_edgeEntropyCore_add_quadratic_le {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    |edgeEntropyCore a b + edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))| ≤
      5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2 := by
  have hb := one_le_b_of_taylorWindow ha hwindow
  have ht := abs_entropyRemainder_le (abs_totalRelativeDeviation_le_half ha hwindow)
  have hr := abs_entropyRemainder_le (abs_rightRelativeDeviation_le_half ha hwindow)
  have hai : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  rw [edgeEntropyCore_eq_quadratic_add_remainders ha hb]
  have hcancel :
      -(edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))) +
          (2 * (a - 1 : ℕ)) * entropyRemainder (totalRelativeDeviation a b) -
          (a - 1 : ℕ) * entropyRemainder (rightRelativeDeviation a b) +
          edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ)) =
        (2 * (a - 1 : ℕ)) * entropyRemainder (totalRelativeDeviation a b) -
          (a - 1 : ℕ) * entropyRemainder (rightRelativeDeviation a b) := by ring
  rw [hcancel]
  calc
    |(2 * (a - 1 : ℕ)) * entropyRemainder (totalRelativeDeviation a b) -
        (a - 1 : ℕ) * entropyRemainder (rightRelativeDeviation a b)| ≤
      |(2 * (a - 1 : ℕ)) * entropyRemainder (totalRelativeDeviation a b)| +
        |(a - 1 : ℕ) * entropyRemainder (rightRelativeDeviation a b)| := abs_sub _ _
    _ = (2 * (a - 1 : ℕ)) * |entropyRemainder (totalRelativeDeviation a b)| +
        (a - 1 : ℕ) * |entropyRemainder (rightRelativeDeviation a b)| := by
      simp only [abs_mul, abs_of_pos hai, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 2 * (a - 1 : ℕ))]
    _ ≤ (2 * (a - 1 : ℕ)) * (4 * |totalRelativeDeviation a b| ^ 3) +
        (a - 1 : ℕ) * (4 * |rightRelativeDeviation a b| ^ 3) := by gcongr
    _ = 5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2 := by
      unfold totalRelativeDeviation rightRelativeDeviation
      rw [abs_div, abs_div, abs_mul, abs_of_pos hai,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      ring

/-- Linear control of the square-root prefactor. -/
lemma abs_edgePrefactorCore_add_gaussian_le {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    |edgePrefactorCore a b + Real.log (Real.pi * (a - 1 : ℕ)) / 2| ≤
      2 * |edgeDeviation a b| / (a - 1 : ℕ) := by
  have hb := one_le_b_of_taylorWindow ha hwindow
  have ht := abs_log_one_add_le_two_mul_abs
    (abs_totalRelativeDeviation_le_half ha hwindow)
  have hr := abs_log_one_add_le_two_mul_abs
    (abs_rightRelativeDeviation_le_half ha hwindow)
  have hai : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  rw [edgePrefactorCore_eq_gaussian_add_log_correction ha hb]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |Real.log (1 + totalRelativeDeviation a b) -
        Real.log (1 + rightRelativeDeviation a b)| / 2 ≤
      (|Real.log (1 + totalRelativeDeviation a b)| +
        |Real.log (1 + rightRelativeDeviation a b)|) / 2 := by
      gcongr
      exact abs_sub _ _
    _ ≤ (2 * |totalRelativeDeviation a b| +
        2 * |rightRelativeDeviation a b|) / 2 := by gcongr
    _ = (3 / 2 : ℝ) * |edgeDeviation a b| / (a - 1 : ℕ) := by
      unfold totalRelativeDeviation rightRelativeDeviation
      rw [abs_div, abs_div, abs_mul, abs_of_pos hai,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      ring
    _ ≤ 2 * |edgeDeviation a b| / (a - 1 : ℕ) := by
      have hz : 0 ≤ |edgeDeviation a b| / (a - 1 : ℕ) := by positivity
      simpa only [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right (by norm_num : (3 / 2 : ℝ) ≤ 2) hz

lemma edgeRobbinsPenalty_le_inv {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    edgeRobbinsPenalty a b ≤ 1 / (a - 1 : ℕ) := by
  have hb := one_le_b_of_taylorWindow ha hwindow
  have hai : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  have hbLower : ((a - 1 : ℕ) : ℝ) / 2 ≤ b := by
    have h := neg_le_of_abs_le hwindow
    unfold edgeDeviation at h
    linarith
  have hinvB : (1 : ℝ) / b ≤ 2 / (a - 1 : ℕ) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < b) hai]
    linarith
  unfold edgeRobbinsPenalty
  rw [show a + b - 1 - b = a - 1 by omega]
  push_cast
  calc
    (1 : ℝ) / (12 * b) + 1 / (12 * (a - 1 : ℕ)) ≤
        (2 / (a - 1 : ℕ)) / 12 + ((1 : ℝ) / (a - 1 : ℕ)) / 12 := by
      have hfirst : (1 : ℝ) / (12 * b) = ((1 : ℝ) / b) / 12 := by field_simp
      have hsecond : (1 : ℝ) / (12 * (a - 1 : ℕ)) =
          ((1 : ℝ) / (a - 1 : ℕ)) / 12 := by field_simp
      rw [hfirst, hsecond]
      gcongr
    _ ≤ 1 / (a - 1 : ℕ) := by
      field_simp
      linarith

/-- Explicit one-edge logarithmic local estimate for the lower Stirling
kernel.  This is the Taylor input used in HLOZ (A.11). -/
theorem abs_edgeStirlingExponent_gaussian_le {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    |edgeStirlingExponent a b +
        Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2 +
        edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))| ≤
      1 / (a - 1 : ℕ) + 2 * |edgeDeviation a b| / (a - 1 : ℕ) +
        5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2 := by
  have hb := one_le_b_of_taylorWindow ha hwindow
  have hent := abs_edgeEntropyCore_add_quadratic_le ha hwindow
  have hpref := abs_edgePrefactorCore_add_gaussian_le ha hwindow
  have hpen := edgeRobbinsPenalty_le_inv ha hwindow
  have hpen0 : 0 ≤ edgeRobbinsPenalty a b := by
    unfold edgeRobbinsPenalty
    positivity
  have hlog : Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2 =
      Real.log 2 + Real.log (Real.pi * (a - 1 : ℕ)) / 2 := by
    have hi : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
    have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [show (4 : ℝ) * Real.pi * (a - 1 : ℕ) =
        4 * (Real.pi * (a - 1 : ℕ)) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (by positivity : Real.pi * (a - 1 : ℕ) ≠ 0),
      hlogFour]
    ring
  rw [edgeStirlingExponent_eq_cores ha, hlog]
  have hrearrange :
      edgeEntropyCore a b + edgePrefactorCore a b - Real.log 2 -
          edgeRobbinsPenalty a b +
          (Real.log 2 + Real.log (Real.pi * (a - 1 : ℕ)) / 2) +
          edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ)) =
        (edgeEntropyCore a b +
          edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))) +
          (edgePrefactorCore a b +
            Real.log (Real.pi * (a - 1 : ℕ)) / 2) -
          edgeRobbinsPenalty a b := by ring
  rw [hrearrange]
  calc
    |(edgeEntropyCore a b + edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))) +
        (edgePrefactorCore a b + Real.log (Real.pi * (a - 1 : ℕ)) / 2) -
        edgeRobbinsPenalty a b| ≤
      |edgeEntropyCore a b + edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))| +
        |edgePrefactorCore a b + Real.log (Real.pi * (a - 1 : ℕ)) / 2| +
          |edgeRobbinsPenalty a b| := by
      calc
        |(edgeEntropyCore a b + edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))) +
            (edgePrefactorCore a b + Real.log (Real.pi * (a - 1 : ℕ)) / 2) -
            edgeRobbinsPenalty a b| ≤
          |(edgeEntropyCore a b + edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))) +
            (edgePrefactorCore a b + Real.log (Real.pi * (a - 1 : ℕ)) / 2)| +
              |edgeRobbinsPenalty a b| := abs_sub _ _
        _ ≤ (|edgeEntropyCore a b +
              edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ))| +
            |edgePrefactorCore a b +
              Real.log (Real.pi * (a - 1 : ℕ)) / 2|) +
              |edgeRobbinsPenalty a b| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ 5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2 +
        2 * |edgeDeviation a b| / (a - 1 : ℕ) +
          1 / (a - 1 : ℕ) := by
      rw [abs_of_nonneg hpen0]
      gcongr
    _ = 1 / (a - 1 : ℕ) + 2 * |edgeDeviation a b| / (a - 1 : ℕ) +
        5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2 := by ring

/-! ## Summing the uniform Taylor remainder -/

/-- The explicit remainder which occurs in the one-edge Taylor estimate. -/
def edgeTaylorError (a b : ℕ) : ℝ :=
  1 / (a - 1 : ℕ) + 2 * |edgeDeviation a b| / (a - 1 : ℕ) +
    5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2

/-- A decreasing-power sum estimate, proved by comparison with its integral.
For the application below, `p = 3 * delta`. -/
lemma sum_rpow_sub_one_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (p - 1)) ≤ (n : ℝ) ^ p / p := by
  let f : ℝ → ℝ := fun x ↦ x ^ (p - 1)
  have hanti : AntitoneOn f
      (Set.Icc ((1 : ℕ) : ℝ) (((n - 1 : ℕ) : ℝ))) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
    intro x hx
    have hxone : (1 : ℝ) ≤ x := by simpa using hx.1
    exact (by simp only [Set.mem_Ioi]; linarith)
  have hsum := AntitoneOn.sum_le_integral_Ico
    (f := f) (a := (1 : ℕ)) (b := n - 1) (by omega) hanti
  have hsum' : (∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (p - 1)) ≤
      ∫ x in (1 : ℝ)..(n - 1 : ℕ), x ^ (p - 1) := by
    have hreindex :
        (∑ i ∈ Finset.Ico 1 (n - 1), f ((i + 1 : ℕ) : ℝ)) =
          ∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (p - 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), f] using
        (Finset.sum_Ico_add' (fun l : ℕ ↦ (l : ℝ) ^ (p - 1)) 1 (n - 1) 1)
    rw [← hreindex]
    simpa only [f, Nat.cast_one] using hsum
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ p / p)
      (Set.Icc (1 : ℝ) (n - 1 : ℕ)) :=
    (Real.continuous_rpow_const hp.le).div_const p |>.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) (n - 1 : ℕ),
      HasDerivAt (fun x : ℝ ↦ x ^ p / p) (x ^ (p - 1)) x := by
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx.1
    have h :=
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl hxpos.ne')).div_const p
    have hcoef : p * x ^ (p - 1) / p = x ^ (p - 1) := by
      field_simp [hp.ne']
    rw [hcoef] at h
    exact h
  have hint : IntervalIntegrable (fun x : ℝ ↦ x ^ (p - 1))
      MeasureTheory.volume (1 : ℝ) (n - 1 : ℕ) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hintEq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (1 : ℝ) ≤ (n - 1 : ℕ) by
      exact_mod_cast (show 1 ≤ n - 1 by omega)) hcont hderiv hint
  rw [hintEq] at hsum'
  have hpow : (((n - 1 : ℕ) : ℝ) ^ p) ≤ (n : ℝ) ^ p := by
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (Nat.sub_le n 1)) hp.le
  have hdrop : ((n - 1 : ℕ) : ℝ) ^ p / p - (1 : ℝ) ^ p / p ≤
      ((n - 1 : ℕ) : ℝ) ^ p / p :=
    sub_le_self _
      (div_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1) p) hp.le)
  have hdiv : ((n - 1 : ℕ) : ℝ) ^ p / p ≤ (n : ℝ) ^ p / p :=
    div_le_div_of_nonneg_right hpow hp.le
  exact hsum'.trans (hdrop.trans hdiv)

/-- At exponents in `[0,1]`, consecutive powers differ by at most a factor
two.  This elementary estimate is used after discrete summation by parts. -/
lemma rpow_succ_le_two_mul {l : ℕ} {delta : ℝ} (hl : 1 ≤ l)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((l + 1 : ℕ) : ℝ) ^ delta ≤ 2 * (l : ℝ) ^ delta := by
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hbase : (((l + 1 : ℕ) : ℝ)) ≤ 2 * (l : ℝ) := by
    push_cast
    exact_mod_cast (show l + 1 ≤ 2 * l by omega)
  calc
    (((l + 1 : ℕ) : ℝ)) ^ delta ≤ (2 * (l : ℝ)) ^ delta :=
      Real.rpow_le_rpow (by positivity) hbase hdelta
    _ = (2 : ℝ) ^ delta * (l : ℝ) ^ delta := by
      rw [Real.mul_rpow (by norm_num) hl0]
    _ ≤ 2 * (l : ℝ) ^ delta := by
      gcongr
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) hdelta1

/-- The explicit one-edge Taylor remainder has scale `l^(3*delta-1)`
whenever the factorial base is at least `l^2` and the centered displacement
is at most `C*l*l^delta`. -/
lemma edgeTaylorError_le_scale {l a b : ℕ} {delta C : ℝ} (hl : 2 ≤ l)
    (hdelta : 0 ≤ delta) (hC : 0 ≤ C)
    (hbase : (l : ℝ) ^ 2 ≤ (a - 1 : ℕ))
    (hdev : |edgeDeviation a b| ≤ C * (l : ℝ) * (l : ℝ) ^ delta) :
    edgeTaylorError a b ≤
      (1 + 2 * C + 5 * C ^ 3) * (l : ℝ) ^ (3 * delta - 1) := by
  let L : ℝ := l
  let I : ℝ := (a - 1 : ℕ)
  let D : ℝ := |edgeDeviation a b|
  let q : ℝ := L ^ delta
  have hL : 0 < L := by simp only [L]; positivity
  have hL1 : 1 ≤ L := by
    simp only [L]
    exact_mod_cast (by omega : 1 ≤ l)
  have hq : 0 ≤ q := by simp only [q]; positivity
  have hI : 0 < I := lt_of_lt_of_le (sq_pos_of_pos hL) hbase
  have hD : 0 ≤ D := by simp only [D]; positivity
  have hInv : 1 / I ≤ 1 / L ^ 2 := by
    apply (div_le_div_iff₀ hI (sq_pos_of_pos hL)).2
    simpa using hbase
  have hInvScale : 1 / L ^ 2 ≤ L ^ (3 * delta - 1) := by
    calc
      1 / L ^ 2 = L ^ (-2 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hL), Real.rpow_two]
        simp only [one_div]
      _ ≤ L ^ (3 * delta - 1) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLinear : 2 * D / I ≤ 2 * C * L ^ (3 * delta - 1) := by
    have hDI : D / I ≤ C * q / L := by
      apply (div_le_div_iff₀ hI hL).2
      calc
        D * L ≤ (C * L * q) * L := by gcongr
        _ ≤ C * q * I := by
          nlinarith [mul_nonneg (mul_nonneg hC hq) (sub_nonneg.mpr hbase)]
    calc
      2 * D / I = 2 * (D / I) := by ring
      _ ≤ 2 * (C * q / L) := by gcongr
      _ = 2 * C * L ^ (delta - 1) := by
        dsimp only [q]
        rw [Real.rpow_sub hL]
        norm_num
        ring
      _ ≤ 2 * C * L ^ (3 * delta - 1) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hCubic : 5 * D ^ 3 / I ^ 2 ≤
      5 * C ^ 3 * L ^ (3 * delta - 1) := by
    have hDpow : D ^ 3 ≤ (C * L * q) ^ 3 := by gcongr
    have hIpow : L ^ 4 ≤ I ^ 2 := by
      calc
        L ^ 4 = (L ^ 2) ^ 2 := by ring
        _ ≤ I ^ 2 := by gcongr
    have hfrac : D ^ 3 / I ^ 2 ≤ (C * L * q) ^ 3 / L ^ 4 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hI) (pow_pos hL 4)).2
      calc
        D ^ 3 * L ^ 4 ≤ (C * L * q) ^ 3 * L ^ 4 := by gcongr
        _ ≤ (C * L * q) ^ 3 * I ^ 2 := by gcongr
    calc
      5 * D ^ 3 / I ^ 2 = 5 * (D ^ 3 / I ^ 2) := by ring
      _ ≤ 5 * ((C * L * q) ^ 3 / L ^ 4) := by gcongr
      _ = 5 * C ^ 3 * L ^ (3 * delta - 1) := by
        dsimp only [q]
        have hq3 : (L ^ delta) ^ 3 = L ^ (3 * delta) := by
          rw [← Real.rpow_natCast (L ^ delta) 3,
            ← Real.rpow_mul (le_of_lt hL)]
          congr 1
          ring
        rw [mul_pow, mul_pow, hq3, Real.rpow_sub hL]
        norm_num
        field_simp
  have hOne : 1 / I ≤ L ^ (3 * delta - 1) := hInv.trans hInvScale
  dsimp only [edgeTaylorError, I, D, L] at hOne hLinear hCubic ⊢
  linarith

/-- Comparison of the factorial-base quadratic with the HLOZ quadratic at
scale `L`.  The assumptions are the two genuine profile envelopes used in
the proof, not a prepackaged error estimate. -/
lemma abs_shiftedQuadratic_sub_parabolic_le
    {L I d delta A C : ℝ} (hL : 1 ≤ L) (hI : L ^ 2 ≤ I)
    (hdelta : 0 ≤ delta) (_hA : 0 ≤ A) (hC : 0 ≤ C)
    (hclose : |2 * L ^ 2 - I| ≤ A * L * L ^ delta)
    (hd : |d| ≤ C * L * L ^ delta) :
    |(d + 1) ^ 2 / (4 * I) - d ^ 2 / (8 * L ^ 2)| ≤
      (1 / 4 + C / 2 + A * C ^ 2 / 8) * L ^ (3 * delta - 1) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hIpos : 0 < I := lt_of_lt_of_le (sq_pos_of_pos hLpos) hI
  have hsplit :
      (d + 1) ^ 2 / (4 * I) - d ^ 2 / (8 * L ^ 2) =
        ((d + 1) ^ 2 - d ^ 2) / (4 * I) +
          d ^ 2 * (2 * L ^ 2 - I) / (8 * I * L ^ 2) := by
    field_simp
    ring
  rw [hsplit]
  have hfirst : |((d + 1) ^ 2 - d ^ 2) / (4 * I)| ≤
      (1 / 4 + C / 2) * L ^ (3 * delta - 1) := by
    rw [abs_div, abs_mul, abs_of_pos hIpos,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    have hnum : |(d + 1) ^ 2 - d ^ 2| ≤ 2 * |d| + 1 := by
      rw [show (d + 1) ^ 2 - d ^ 2 = 2 * d + 1 by ring]
      calc
        |2 * d + 1| ≤ |2 * d| + |1| := abs_add_le _ _
        _ = 2 * |d| + 1 := by norm_num
    calc
      |(d + 1) ^ 2 - d ^ 2| / (4 * I) ≤
          (2 * |d| + 1) / (4 * I) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * (C * L * L ^ delta) + 1) / (4 * L ^ 2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hn : 0 ≤ 2 * |d| + 1 := by positivity
        have hdn : 2 * |d| + 1 ≤ 2 * (C * L * L ^ delta) + 1 := by
          gcongr
        nlinarith [mul_le_mul_of_nonneg_left hI hn,
          mul_le_mul_of_nonneg_right hdn (sq_nonneg L)]
      _ = C / 2 * L ^ (delta - 1) + 1 / 4 * L ^ (-2 : ℝ) := by
        rw [Real.rpow_sub hLpos, Real.rpow_one,
          Real.rpow_neg (le_of_lt hLpos), Real.rpow_two]
        field_simp
        ring
      _ ≤ C / 2 * L ^ (3 * delta - 1) +
          1 / 4 * L ^ (3 * delta - 1) := by
        have hr1 := Real.rpow_le_rpow_of_exponent_le hL
          (show delta - 1 ≤ 3 * delta - 1 by linarith)
        have hr2 := Real.rpow_le_rpow_of_exponent_le hL
          (show (-2 : ℝ) ≤ 3 * delta - 1 by linarith)
        exact add_le_add
          (mul_le_mul_of_nonneg_left hr1 (by positivity))
          (mul_le_mul_of_nonneg_left hr2 (by norm_num))
      _ = (1 / 4 + C / 2) * L ^ (3 * delta - 1) := by ring
  have hsecond : |d ^ 2 * (2 * L ^ 2 - I) / (8 * I * L ^ 2)| ≤
      (A * C ^ 2 / 8) * L ^ (3 * delta - 1) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 8 * I * L ^ 2),
      abs_mul, abs_pow]
    have hdsq : |d| ^ 2 ≤ (C * L * L ^ delta) ^ 2 := by gcongr
    calc
      |d| ^ 2 * |2 * L ^ 2 - I| / (8 * I * L ^ 2) ≤
          (C * L * L ^ delta) ^ 2 * (A * L * L ^ delta) /
            (8 * L ^ 2 * L ^ 2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hnum0 : 0 ≤ |d| ^ 2 * |2 * L ^ 2 - I| := by positivity
        have hnum : |d| ^ 2 * |2 * L ^ 2 - I| ≤
            (C * L * L ^ delta) ^ 2 * (A * L * L ^ delta) := by
          exact mul_le_mul hdsq hclose (abs_nonneg _) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hI hnum0,
          mul_le_mul_of_nonneg_right hnum (sq_nonneg L)]
      _ = (A * C ^ 2 / 8) * L ^ (3 * delta - 1) := by
        have hq3 : (L ^ delta) ^ 3 = L ^ (3 * delta) := by
          rw [← Real.rpow_natCast (L ^ delta) 3,
            ← Real.rpow_mul (le_of_lt hLpos)]
          congr 1
          ring
        rw [Real.rpow_sub hLpos, Real.rpow_one]
        field_simp
        rw [← hq3]
        ring
  calc
    |((d + 1) ^ 2 - d ^ 2) / (4 * I) +
        d ^ 2 * (2 * L ^ 2 - I) / (8 * I * L ^ 2)| ≤
      |((d + 1) ^ 2 - d ^ 2) / (4 * I)| +
        |d ^ 2 * (2 * L ^ 2 - I) / (8 * I * L ^ 2)| := abs_add_le _ _
    _ ≤ (1 / 4 + C / 2) * L ^ (3 * delta - 1) +
        (A * C ^ 2 / 8) * L ^ (3 * delta - 1) := add_le_add hfirst hsecond
    _ = (1 / 4 + C / 2 + A * C ^ 2 / 8) *
        L ^ (3 * delta - 1) := by ring

/-- Comparison of the Stirling square-root normalizer with the HLOZ
normalizer `sqrt (8*pi*L^2)`. -/
lemma abs_logNormalizer_sub_parabolic_le
    {L I delta A : ℝ} (hL : 1 ≤ L) (hI : L ^ 2 ≤ I)
    (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hclose : |I - 2 * L ^ 2| ≤ A * L * L ^ delta)
    (hmoderate : A * L * L ^ delta ≤ L ^ 2) :
    |Real.log (4 * Real.pi * I) / 2 -
        Real.log (8 * Real.pi * L ^ 2) / 2| ≤
      A / 2 * L ^ (3 * delta - 1) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hIpos : 0 < I := lt_of_lt_of_le (sq_pos_of_pos hLpos) hI
  let u : ℝ := (I - 2 * L ^ 2) / (2 * L ^ 2)
  have hu : |u| ≤ 1 / 2 := by
    dsimp only [u]
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hLpos,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |I - 2 * L ^ 2| / (2 * L ^ 2) ≤
          (A * L * L ^ delta) / (2 * L ^ 2) :=
        div_le_div_of_nonneg_right hclose (by positivity)
      _ ≤ 1 / 2 := by
        apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
        nlinarith
  have hupos : 0 < 1 + u := by
    have heq : 1 + u = I / (2 * L ^ 2) := by
      dsimp only [u]
      field_simp
      ring
    rw [heq]
    positivity
  have hfactor : 4 * Real.pi * I =
      (8 * Real.pi * L ^ 2) * (1 + u) := by
    dsimp only [u]
    field_simp
    ring
  have hlog : Real.log (4 * Real.pi * I) -
      Real.log (8 * Real.pi * L ^ 2) = Real.log (1 + u) := by
    rw [hfactor, Real.log_mul (by positivity) hupos.ne']
    ring
  have hurel : |u| ≤ A / 2 * L ^ (delta - 1) := by
    dsimp only [u]
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hLpos,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |I - 2 * L ^ 2| / (2 * L ^ 2) ≤
          (A * L * L ^ delta) / (2 * L ^ 2) :=
        div_le_div_of_nonneg_right hclose (by positivity)
      _ = A / 2 * L ^ (delta - 1) := by
        rw [Real.rpow_sub hLpos, Real.rpow_one]
        field_simp
  have hlogBound := abs_log_one_add_le_two_mul_abs hu
  have hlocal : |Real.log (4 * Real.pi * I) / 2 -
      Real.log (8 * Real.pi * L ^ 2) / 2| ≤
      A / 2 * L ^ (delta - 1) := by
    rw [show Real.log (4 * Real.pi * I) / 2 -
        Real.log (8 * Real.pi * L ^ 2) / 2 =
      (Real.log (4 * Real.pi * I) -
        Real.log (8 * Real.pi * L ^ 2)) / 2 by ring,
      hlog, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |Real.log (1 + u)| / 2 ≤ (2 * |u|) / 2 := by gcongr
      _ = |u| := by ring
      _ ≤ A / 2 * L ^ (delta - 1) := hurel
  calc
    _ ≤ A / 2 * L ^ (delta - 1) := hlocal
    _ ≤ A / 2 * L ^ (3 * delta - 1) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

/-- The actual increment in the transition from `a` to `b`. -/
def parabolicTransitionIncrement (a b : ℕ) : ℝ := (b : ℝ) - a

/-- One-edge Taylor estimate in exactly the normalization and quadratic
energy of the HLOZ Gaussian kernel at scale `l`. -/
theorem abs_edgeStirlingExponent_parabolic_le
    {l a b : ℕ} {delta A C : ℝ} (hl : 2 ≤ l) (ha : 2 ≤ a)
    (hdelta : 0 ≤ delta) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hwindow : InEdgeTaylorWindow a b)
    (hbase : (l : ℝ) ^ 2 ≤ (a - 1 : ℕ))
    (hclose : |2 * (l : ℝ) ^ 2 - (a - 1 : ℕ)| ≤
      A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : |parabolicTransitionIncrement a b| ≤
      C * (l : ℝ) * (l : ℝ) ^ delta) :
    |edgeStirlingExponent a b +
        Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
        parabolicTransitionIncrement a b ^ 2 / (8 * (l : ℝ) ^ 2)| ≤
      ((1 + 2 * (C + 1) + 5 * (C + 1) ^ 3) +
        A / 2 + (1 / 4 + C / 2 + A * C ^ 2 / 8)) *
          (l : ℝ) ^ (3 * delta - 1) := by
  have hL : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hqOne : (1 : ℝ) ≤ (l : ℝ) ^ delta := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL hdelta
  have hLq : (1 : ℝ) ≤ (l : ℝ) * (l : ℝ) ^ delta := by
    nlinarith [mul_le_mul hL hqOne (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ l)]
  have hdevEq : edgeDeviation a b =
      parabolicTransitionIncrement a b + 1 := by
    unfold edgeDeviation parabolicTransitionIncrement
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    ring
  have hdev : |edgeDeviation a b| ≤
      (C + 1) * (l : ℝ) * (l : ℝ) ^ delta := by
    rw [hdevEq]
    calc
      |parabolicTransitionIncrement a b + 1| ≤
          |parabolicTransitionIncrement a b| + |1| := abs_add_le _ _
      _ ≤ C * (l : ℝ) * (l : ℝ) ^ delta + 1 := by
        norm_num
        gcongr
      _ ≤ (C + 1) * (l : ℝ) * (l : ℝ) ^ delta := by
        nlinarith [mul_nonneg hC (by positivity :
          (0 : ℝ) ≤ (l : ℝ) * (l : ℝ) ^ delta)]
  have htaylor := (abs_edgeStirlingExponent_gaussian_le ha hwindow).trans
    (edgeTaylorError_le_scale hl hdelta (by positivity : (0 : ℝ) ≤ C + 1)
      hbase hdev)
  have hlog := abs_logNormalizer_sub_parabolic_le hL hbase hdelta hA
    (by rw [abs_sub_comm]; exact hclose) hmoderate
  have hquad := abs_shiftedQuadratic_sub_parabolic_le hL hbase hdelta hA hC
    hclose hinc
  rw [hdevEq] at htaylor
  have hrearrange :
      edgeStirlingExponent a b + Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement a b ^ 2 / (8 * (l : ℝ) ^ 2) =
        (edgeStirlingExponent a b +
          Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2 +
          (parabolicTransitionIncrement a b + 1) ^ 2 /
            (4 * (a - 1 : ℕ))) +
        (Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 -
          Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2) +
        (parabolicTransitionIncrement a b ^ 2 / (8 * (l : ℝ) ^ 2) -
          (parabolicTransitionIncrement a b + 1) ^ 2 /
            (4 * (a - 1 : ℕ))) := by ring
  rw [hrearrange]
  calc
    _ ≤ |edgeStirlingExponent a b +
          Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2 +
          (parabolicTransitionIncrement a b + 1) ^ 2 /
            (4 * (a - 1 : ℕ))| +
        |Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 -
          Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2| +
        |parabolicTransitionIncrement a b ^ 2 / (8 * (l : ℝ) ^ 2) -
          (parabolicTransitionIncrement a b + 1) ^ 2 /
            (4 * (a - 1 : ℕ))| := by
      calc
        _ ≤ |(edgeStirlingExponent a b +
              Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2 +
              (parabolicTransitionIncrement a b + 1) ^ 2 /
                (4 * (a - 1 : ℕ))) +
            (Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 -
              Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2)| +
            |parabolicTransitionIncrement a b ^ 2 / (8 * (l : ℝ) ^ 2) -
              (parabolicTransitionIncrement a b + 1) ^ 2 /
                (4 * (a - 1 : ℕ))| := abs_add_le _ _
        _ ≤ _ := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (1 + 2 * (C + 1) + 5 * (C + 1) ^ 3) *
          (l : ℝ) ^ (3 * delta - 1) +
        (A / 2) * (l : ℝ) ^ (3 * delta - 1) +
        (1 / 4 + C / 2 + A * C ^ 2 / 8) *
          (l : ℝ) ^ (3 * delta - 1) := by
      exact add_le_add
        (add_le_add htaylor (by simpa only [abs_sub_comm] using hlog))
        (by simpa only [abs_sub_comm] using hquad)
    _ = _ := by ring

/-- The explicit coefficient in the accumulated HLOZ-normalized Taylor
error. -/
def parabolicTaylorCoefficient (A C : ℝ) : ℝ :=
  (1 + 2 * (C + 1) + 5 * (C + 1) ^ 3) +
    A / 2 + (1 / 4 + C / 2 + A * C ^ 2 / 8)

/-- **Full finite edge-sum estimate in HLOZ form.**

The logarithmic Stirling exponents along `m` are compared directly with the
Gaussian-kernel normalizers and increment energies at scales `l`.  The
`n^(3*delta)` error follows from the preceding one-edge estimates and the
proved decreasing-power sum; no accumulated estimate is assumed. -/
theorem abs_sum_edgeStirlingExponent_parabolic_le
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ → ℕ) {delta A C : ℝ}
    (hdelta : 0 < delta) (hdeltaThird : delta ≤ 1 / 3)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico 2 n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico 2 n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico 2 n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico 2 n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico 2 n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico 2 n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    |∑ l ∈ Finset.Ico 2 n,
        (edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2))| ≤
      parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
        (3 * delta) := by
  have hcoeff : 0 ≤ parabolicTaylorCoefficient A C := by
    unfold parabolicTaylorCoefficient
    positivity
  calc
    |∑ l ∈ Finset.Ico 2 n,
        (edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2))| ≤
      ∑ l ∈ Finset.Ico 2 n,
        |edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Ico 2 n,
        parabolicTaylorCoefficient A C *
          (l : ℝ) ^ (3 * delta - 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact abs_edgeStirlingExponent_parabolic_le
        (Finset.mem_Ico.mp hl).1 (hpos l hl) hdelta.le hA hC
        (hwindow l hl) (hbase l hl) (hclose l hl) (hmoderate l hl)
        (hinc l hl)
    _ = parabolicTaylorCoefficient A C *
        (∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (3 * delta - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ parabolicTaylorCoefficient A C *
        ((n : ℝ) ^ (3 * delta) / (3 * delta)) := by
      gcongr
      exact sum_rpow_sub_one_le (by positivity) (by linarith) n hn
    _ = parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
        (3 * delta) := by ring

/-- Finite form of the accumulated `O(n^(3*delta))` Taylor error in HLOZ
(A.11).  All hypotheses are pointwise scale estimates; the target error is
derived by summation rather than assumed. -/
theorem abs_sum_edgeStirlingExponent_gaussian_le
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ → ℕ) {delta C : ℝ}
    (hdelta : 0 < delta) (hdeltaThird : delta ≤ 1 / 3) (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico 2 n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico 2 n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico 2 n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hdev : ∀ l ∈ Finset.Ico 2 n,
      |edgeDeviation (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    |∑ l ∈ Finset.Ico 2 n,
        (edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (4 * Real.pi * (m l - 1 : ℕ)) / 2 +
          edgeDeviation (m l) (m (l + 1)) ^ 2 /
            (4 * (m l - 1 : ℕ)))| ≤
      (1 + 2 * C + 5 * C ^ 3) * (n : ℝ) ^ (3 * delta) / (3 * delta) := by
  have hcoeff : 0 ≤ 1 + 2 * C + 5 * C ^ 3 := by positivity
  calc
    |∑ l ∈ Finset.Ico 2 n,
        (edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (4 * Real.pi * (m l - 1 : ℕ)) / 2 +
          edgeDeviation (m l) (m (l + 1)) ^ 2 /
            (4 * (m l - 1 : ℕ)))| ≤
      ∑ l ∈ Finset.Ico 2 n,
        |edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (4 * Real.pi * (m l - 1 : ℕ)) / 2 +
          edgeDeviation (m l) (m (l + 1)) ^ 2 /
            (4 * (m l - 1 : ℕ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Ico 2 n, edgeTaylorError (m l) (m (l + 1)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact abs_edgeStirlingExponent_gaussian_le (hpos l hl) (hwindow l hl)
    _ ≤ ∑ l ∈ Finset.Ico 2 n,
        (1 + 2 * C + 5 * C ^ 3) * (l : ℝ) ^ (3 * delta - 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact edgeTaylorError_le_scale (Finset.mem_Ico.mp hl).1 hdelta.le hC
        (hbase l hl) (hdev l hl)
    _ = (1 + 2 * C + 5 * C ^ 3) *
        (∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (3 * delta - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 + 2 * C + 5 * C ^ 3) * ((n : ℝ) ^ (3 * delta) / (3 * delta)) := by
      gcongr
      exact sum_rpow_sub_one_le (by positivity) (by linarith) n hn
    _ = (1 + 2 * C + 5 * C ^ 3) * (n : ℝ) ^ (3 * delta) /
        (3 * delta) := by ring

/-! ## Recentring at the parabolic profile -/

/-- Gaussian energy of a finite real deviation profile. -/
def gaussianEnergy (n : ℕ) (Delta : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico 2 n, (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2)

/-- The exact edge increment after writing `m_l = 2*l^2 + Delta_l`. -/
lemma parabolic_increment (l : ℕ) (Delta : ℕ → ℝ) :
    (2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
        (2 * (l : ℝ) ^ 2 + Delta l) =
      4 * l + 2 + (Delta (l + 1) - Delta l) := by
  push_cast
  ring

/-- Exact one-edge recentering identity behind (A.11). -/
lemma parabolic_edge_energy_expansion {l : ℕ} (hl : l ≠ 0)
    (Delta : ℕ → ℝ) :
    ((2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
        (2 * (l : ℝ) ^ 2 + Delta l)) ^ 2 / (8 * (l : ℝ) ^ 2) =
      2 + 2 / l + 1 / (2 * (l : ℝ) ^ 2) +
        (Delta (l + 1) - Delta l) / l +
        (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2) +
        (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2) := by
  rw [parabolic_increment]
  exact quadratic_increment_expansion (by exact_mod_cast hl)

/-- The energy of the successive increments along the real parabolic profile
`2*l^2 + Delta_l`. -/
def parabolicEnergy (n : ℕ) (Delta : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico 2 n,
    ((2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
      (2 * (l : ℝ) ^ 2 + Delta l)) ^ 2 / (8 * (l : ℝ) ^ 2)

/-- The reference energy which is the deterministic parabolic cost plus the
Gaussian energy of the centered increments. -/
def parabolicReferenceEnergy (n : ℕ) (Delta : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico 2 n,
    (2 + (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2))

lemma parabolicReferenceEnergy_eq (n : ℕ) (hn : 2 ≤ n)
    (Delta : ℕ → ℝ) :
    parabolicReferenceEnergy n Delta =
      2 * (n - 2) + gaussianEnergy n Delta := by
  unfold parabolicReferenceEnergy gaussianEnergy
  rw [Finset.sum_add_distrib]
  simp [Nat.card_Ico, hn]
  ring

/-- Exact global decomposition of the parabolic-energy error.  The third
term is deliberately kept as a whole so that summation by parts, rather than
a wasteful termwise triangle inequality, controls it. -/
lemma parabolicEnergy_sub_reference_eq (n : ℕ) (Delta : ℕ → ℝ) :
    parabolicEnergy n Delta - parabolicReferenceEnergy n Delta =
      (∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) +
      (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)) +
      (∑ l ∈ Finset.Ico 2 n, (Delta (l + 1) - Delta l) / (l : ℝ)) +
      ∑ l ∈ Finset.Ico 2 n,
        (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2) := by
  unfold parabolicEnergy parabolicReferenceEnergy
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ l ∈ Finset.Ico 2 n,
      ((2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
          (2 * (l : ℝ) ^ 2 + Delta l)) ^ 2 / (8 * (l : ℝ) ^ 2) -
        (2 + (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2)) =
      2 / (l : ℝ) + 1 / (2 * (l : ℝ) ^ 2) +
        (Delta (l + 1) - Delta l) / (l : ℝ) +
        (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2) := by
    intro l hl
    have hl2 := (Finset.mem_Ico.mp hl).1
    rw [parabolic_edge_energy_expansion (by omega : l ≠ 0)]
    ring
  calc
    ∑ l ∈ Finset.Ico 2 n,
        (((2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
          (2 * (l : ℝ) ^ 2 + Delta l)) ^ 2 / (8 * (l : ℝ) ^ 2) -
        (2 + (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2))) =
      ∑ l ∈ Finset.Ico 2 n,
        (2 / (l : ℝ) + 1 / (2 * (l : ℝ) ^ 2) +
          (Delta (l + 1) - Delta l) / (l : ℝ) +
          (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

/-- Discrete summation by parts for the linear energy correction. -/
lemma sum_increment_div_eq (n : ℕ) (Delta : ℕ → ℝ) :
    (∑ l ∈ Finset.Ico 2 n, (Delta (l + 1) - Delta l) / (l : ℝ)) =
      (∑ l ∈ Finset.Ico 2 n,
        (Delta (l + 1) / (l + 1 : ℕ) - Delta l / (l : ℝ))) +
      ∑ l ∈ Finset.Ico 2 n, Delta (l + 1) / ((l : ℝ) * (l + 1)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hl0 : (l : ℝ) ≠ 0 := by
    have : 2 ≤ l := (Finset.mem_Ico.mp hl).1
    positivity
  have hls0 : ((l + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The telescoping part of the linear correction. -/
lemma sum_telescoping_delta_div (n : ℕ) (hn : 2 ≤ n) (Delta : ℕ → ℝ) :
    (∑ l ∈ Finset.Ico 2 n,
      (Delta (l + 1) / (l + 1 : ℕ) - Delta l / (l : ℝ))) =
      Delta n / n - Delta 2 / 2 := by
  let f : ℕ → ℝ := fun l ↦ Delta l / (l : ℝ)
  change (∑ l ∈ Finset.Ico 2 n, (f (l + 1) - f l)) = f n - f 2
  rw [Finset.sum_Ico_eq_sub _ hn, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- A finite bound for the linear correction under a linear envelope. -/
lemma abs_sum_increment_div_le (n : ℕ) (hn : 2 ≤ n) (Delta : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hDelta : ∀ l ∈ Finset.Icc 2 n, |Delta l| ≤ B * l) :
    |∑ l ∈ Finset.Ico 2 n, (Delta (l + 1) - Delta l) / (l : ℝ)| ≤
      2 * B + B * (n - 2) := by
  rw [sum_increment_div_eq, sum_telescoping_delta_div n hn]
  calc
    |Delta n / n - Delta 2 / 2 +
        ∑ l ∈ Finset.Ico 2 n, Delta (l + 1) / ((l : ℝ) * (l + 1))| ≤
      |Delta n / n| + |Delta 2 / 2| +
        ∑ l ∈ Finset.Ico 2 n, |Delta (l + 1) / ((l : ℝ) * (l + 1))| := by
      calc
        |Delta n / n - Delta 2 / 2 +
            ∑ l ∈ Finset.Ico 2 n, Delta (l + 1) / ((l : ℝ) * (l + 1))| ≤
          |Delta n / n - Delta 2 / 2| +
            |∑ l ∈ Finset.Ico 2 n,
              Delta (l + 1) / ((l : ℝ) * (l + 1))| := abs_add_le _ _
        _ ≤ (|Delta n / n| + |Delta 2 / 2|) +
            ∑ l ∈ Finset.Ico 2 n,
              |Delta (l + 1) / ((l : ℝ) * (l + 1))| := by
          gcongr
          · exact abs_sub _ _
          · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ B + B + ∑ _l ∈ Finset.Ico 2 n, B := by
      gcongr with l hl
      · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
        have hn0 : (0 : ℝ) < n := by positivity
        exact (div_le_iff₀ hn0).2 (by
          simpa only [mul_comm] using hDelta n (by simp [hn]))
      · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        have hd := hDelta 2 (by simp [hn])
        norm_num at hd ⊢
        exact hd
      · rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ l),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ l + 1)]
        have hlpos : (0 : ℝ) < l := by
          have : 2 ≤ l := (Finset.mem_Ico.mp hl).1
          positivity
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (l : ℝ) * (l + 1))]
        have hmem : l + 1 ∈ Finset.Icc 2 n := by
          rw [Finset.mem_Icc]
          have hlLower := (Finset.mem_Ico.mp hl).1
          exact ⟨by omega, (Finset.mem_Ico.mp hl).2⟩
        have hd := hDelta (l + 1) hmem
        have hBmul : B * ((l : ℝ) + 1) ≤ B * ((l : ℝ) * ((l : ℝ) + 1)) := by
          have hl1 : (1 : ℝ) ≤ l := by
            have hlNat : 1 ≤ l := le_trans (by omega : 1 ≤ 2)
              (Finset.mem_Ico.mp hl).1
            exact_mod_cast hlNat
          nlinarith [mul_nonneg hB (sub_nonneg.mpr hl1),
            mul_nonneg hB (show (0 : ℝ) ≤ (l : ℝ) + 1 by positivity)]
        push_cast at hd
        exact hd.trans hBmul
    _ = 2 * B + B * (n - 2) := by
      simp [Nat.card_Ico, hn]
      ring

/-- The sharp power-envelope version of summation by parts.  This is the
finite `O(n^delta)` estimate for the linear correction in HLOZ (A.11). -/
lemma abs_sum_increment_div_le_rpow (n : ℕ) (hn : 2 ≤ n)
    (Delta : ℕ → ℝ) {delta B : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hB : 0 ≤ B)
    (hDelta : ∀ l ∈ Finset.Icc 2 n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta) :
    |∑ l ∈ Finset.Ico 2 n, (Delta (l + 1) - Delta l) / (l : ℝ)| ≤
      4 * B * (n : ℝ) ^ delta / delta := by
  rw [sum_increment_div_eq, sum_telescoping_delta_div n hn]
  have hnpos : (0 : ℝ) < n := by positivity
  have hnPow : 0 ≤ (n : ℝ) ^ delta := by positivity
  have htwoPow : (2 : ℝ) ^ delta ≤ (n : ℝ) ^ delta :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn) hdelta.le
  have hBoundaryN : |Delta n / n| ≤ B * (n : ℝ) ^ delta := by
    rw [abs_div, abs_of_pos hnpos]
    apply (div_le_iff₀ hnpos).2
    have hd := hDelta n (by simp [hn])
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hd
  have hBoundaryTwo : |Delta 2 / 2| ≤ B * (n : ℝ) ^ delta := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hd := hDelta 2 (by simp [hn])
    have hmul := mul_le_mul_of_nonneg_left htwoPow hB
    norm_num at hd ⊢
    nlinarith
  have hterm : ∀ l ∈ Finset.Ico 2 n,
      |Delta (l + 1) / ((l : ℝ) * (l + 1))| ≤
        2 * B * (l : ℝ) ^ (delta - 1) := by
    intro l hl
    have hlNat : 1 ≤ l := by
      have := (Finset.mem_Ico.mp hl).1
      omega
    have hlpos : (0 : ℝ) < l := by positivity
    have hmem : l + 1 ∈ Finset.Icc 2 n := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, (Finset.mem_Ico.mp hl).2⟩
    have hd := hDelta (l + 1) hmem
    have hp := rpow_succ_le_two_mul hlNat hdelta.le hdelta1
    rw [abs_div, abs_mul, abs_of_pos hlpos,
      abs_of_pos (by positivity : (0 : ℝ) < (l : ℝ) + 1)]
    rw [div_le_iff₀
      (mul_pos hlpos (by positivity : (0 : ℝ) < (l : ℝ) + 1))]
    push_cast at hd ⊢
    rw [Real.rpow_sub hlpos]
    norm_num
    field_simp
    calc
      |Delta (l + 1)| ≤ B * ((l : ℝ) + 1) *
          (((l : ℝ) + 1) ^ delta) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hd
      _ ≤ B * ((l : ℝ) + 1) * (2 * (l : ℝ) ^ delta) := by
        have hp' : ((l : ℝ) + 1) ^ delta ≤ 2 * (l : ℝ) ^ delta := by
          simpa only [Nat.cast_add, Nat.cast_one] using hp
        exact mul_le_mul_of_nonneg_left hp'
          (mul_nonneg hB (by positivity))
      _ = 2 * B * (l : ℝ) ^ delta * ((l : ℝ) + 1) := by ring
  calc
    |Delta n / n - Delta 2 / 2 +
        ∑ l ∈ Finset.Ico 2 n, Delta (l + 1) / ((l : ℝ) * (l + 1))| ≤
      |Delta n / n| + |Delta 2 / 2| +
        ∑ l ∈ Finset.Ico 2 n,
          |Delta (l + 1) / ((l : ℝ) * (l + 1))| := by
      calc
        _ ≤ |Delta n / n - Delta 2 / 2| +
            |∑ l ∈ Finset.Ico 2 n,
              Delta (l + 1) / ((l : ℝ) * (l + 1))| := abs_add_le _ _
        _ ≤ (|Delta n / n| + |Delta 2 / 2|) +
            ∑ l ∈ Finset.Ico 2 n,
              |Delta (l + 1) / ((l : ℝ) * (l + 1))| := by
          gcongr
          · exact abs_sub _ _
          · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ B * (n : ℝ) ^ delta + B * (n : ℝ) ^ delta +
        ∑ l ∈ Finset.Ico 2 n, 2 * B * (l : ℝ) ^ (delta - 1) := by
      gcongr with l hl
      exact hterm l hl
    _ = 2 * B * (n : ℝ) ^ delta +
        2 * B * (∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (delta - 1)) := by
      rw [Finset.mul_sum]
      ring
    _ ≤ 2 * B * (n : ℝ) ^ delta +
        2 * B * ((n : ℝ) ^ delta / delta) := by
      gcongr
      exact sum_rpow_sub_one_le hdelta hdelta1 n hn
    _ ≤ 4 * B * (n : ℝ) ^ delta / delta := by
      have hmul : B * (n : ℝ) ^ delta ≥ 0 := by positivity
      have hX : B * (n : ℝ) ^ delta ≤
          B * (n : ℝ) ^ delta / delta := by
        apply (le_div_iff₀ hdelta).2
        nlinarith [mul_le_mul_of_nonneg_left hdelta1 hmul]
      have htwice :=
        mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
      calc
        2 * B * (n : ℝ) ^ delta + 2 * B * ((n : ℝ) ^ delta / delta) =
            2 * (B * (n : ℝ) ^ delta) +
              2 * (B * (n : ℝ) ^ delta / delta) := by ring
        _ ≤ 2 * (B * (n : ℝ) ^ delta / delta) +
              2 * (B * (n : ℝ) ^ delta / delta) :=
          add_le_add htwice (le_refl _)
        _ = 4 * B * (n : ℝ) ^ delta / delta := by ring

/-- A reciprocal is dominated by the decreasing power used in all the
finite remainder sums. -/
lemma one_div_le_rpow_sub_one {l : ℕ} (hl : 1 ≤ l) {delta : ℝ}
    (hdelta : 0 ≤ delta) :
    1 / (l : ℝ) ≤ (l : ℝ) ^ (delta - 1) := by
  have hL : (0 : ℝ) < l := by positivity
  rw [Real.rpow_sub hL, Real.rpow_one]
  apply (div_le_div_iff_of_pos_right hL).2
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast hl) hdelta

/-- **Finite parabolic-to-Gaussian energy estimate.**

Under the actual profile envelope `|Delta_l| <= B*l*l^delta` and its
consequence-sized increment envelope, the full parabolic increment energy
differs from the deterministic cost plus `gaussianEnergy` by at most an
explicit multiple of `n^(3*delta)`.  The potentially large linear term is
controlled by `abs_sum_increment_div_le_rpow`. -/
theorem abs_parabolicEnergy_sub_reference_le (n : ℕ) (hn : 2 ≤ n)
    (Delta : ℕ → ℝ) {delta B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hDelta : ∀ l ∈ Finset.Icc 2 n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hInc : ∀ l ∈ Finset.Ico 2 n,
      |Delta (l + 1) - Delta l| ≤ C * (l : ℝ) * (l : ℝ) ^ delta) :
    |parabolicEnergy n Delta - parabolicReferenceEnergy n Delta| ≤
      (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by
  have hdelta1 : delta ≤ 1 := by linarith
  have hlinear :=
    abs_sum_increment_div_le_rpow n hn Delta hdelta hdelta1 hB hDelta
  rw [parabolicEnergy_sub_reference_eq]
  have hFirst : (∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) ≤
      2 * ((n : ℝ) ^ delta / delta) := by
    calc
      (∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) ≤
          ∑ l ∈ Finset.Ico 2 n, 2 * (l : ℝ) ^ (delta - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl1 : 1 ≤ l := by
          have := (Finset.mem_Ico.mp hl).1
          omega
        calc
          2 / (l : ℝ) = 2 * (1 / (l : ℝ)) := by ring
          _ ≤ 2 * (l : ℝ) ^ (delta - 1) := by
            exact mul_le_mul_of_nonneg_left
              (one_div_le_rpow_sub_one hl1 hdelta.le) (by norm_num)
      _ = 2 * (∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (delta - 1)) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * ((n : ℝ) ^ delta / delta) := by
        gcongr
        exact sum_rpow_sub_one_le hdelta hdelta1 n hn
  have hSecond : (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)) ≤
      (n : ℝ) ^ delta / delta := by
    calc
      (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)) ≤
          ∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (delta - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl1 : 1 ≤ l := by
          have := (Finset.mem_Ico.mp hl).1
          omega
        have hL : (0 : ℝ) < l := by positivity
        calc
          1 / (2 * (l : ℝ) ^ 2) ≤ 1 / (l : ℝ) := by
            apply (div_le_div_iff₀ (by positivity) hL).2
            nlinarith [show (1 : ℝ) ≤ l by exact_mod_cast hl1,
              sq_nonneg ((l : ℝ) - 1)]
          _ ≤ (l : ℝ) ^ (delta - 1) :=
            one_div_le_rpow_sub_one hl1 hdelta.le
      _ ≤ (n : ℝ) ^ delta / delta :=
        sum_rpow_sub_one_le hdelta hdelta1 n hn
  have hExtraTerm : ∀ l ∈ Finset.Ico 2 n,
      |(Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
        C / 2 * (l : ℝ) ^ (delta - 1) := by
    intro l hl
    have hl2 := (Finset.mem_Ico.mp hl).1
    have hL : (0 : ℝ) < l := by positivity
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hL,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |Delta (l + 1) - Delta l| / (2 * (l : ℝ) ^ 2) ≤
          (C * (l : ℝ) * (l : ℝ) ^ delta) / (2 * (l : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (hInc l hl) (by positivity)
      _ = C / 2 * (l : ℝ) ^ (delta - 1) := by
        rw [Real.rpow_sub hL, Real.rpow_one]
        field_simp
  have hExtra : |∑ l ∈ Finset.Ico 2 n,
      (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
      C / 2 * ((n : ℝ) ^ delta / delta) := by
    calc
      |∑ l ∈ Finset.Ico 2 n,
          (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
        ∑ l ∈ Finset.Ico 2 n,
          |(Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ Finset.Ico 2 n,
          C / 2 * (l : ℝ) ^ (delta - 1) := by
        apply Finset.sum_le_sum
        exact hExtraTerm
      _ = C / 2 * (∑ l ∈ Finset.Ico 2 n,
          (l : ℝ) ^ (delta - 1)) := by rw [Finset.mul_sum]
      _ ≤ C / 2 * ((n : ℝ) ^ delta / delta) := by
        gcongr
        exact sum_rpow_sub_one_le hdelta hdelta1 n hn
  have hFirst0 : 0 ≤ ∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ) := by positivity
  have hSecond0 : 0 ≤ ∑ l ∈ Finset.Ico 2 n,
      1 / (2 * (l : ℝ) ^ 2) := by positivity
  have hTotalDelta :
      |(∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) +
          (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)) +
          (∑ l ∈ Finset.Ico 2 n,
            (Delta (l + 1) - Delta l) / (l : ℝ)) +
          ∑ l ∈ Finset.Ico 2 n,
            (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
        (3 + 4 * B + C / 2) * ((n : ℝ) ^ delta / delta) := by
    calc
      _ ≤ |∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)| +
          |∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)| +
          |∑ l ∈ Finset.Ico 2 n,
            (Delta (l + 1) - Delta l) / (l : ℝ)| +
          |∑ l ∈ Finset.Ico 2 n,
            (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| := by
        calc
          _ ≤ |(∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) +
                (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)) +
                (∑ l ∈ Finset.Ico 2 n,
                  (Delta (l + 1) - Delta l) / (l : ℝ))| +
              |∑ l ∈ Finset.Ico 2 n,
                (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| :=
            abs_add_le _ _
          _ ≤ (|(∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) +
                (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2))| +
              |∑ l ∈ Finset.Ico 2 n,
                (Delta (l + 1) - Delta l) / (l : ℝ)|) +
              |∑ l ∈ Finset.Ico 2 n,
                (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ (|∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)| +
                |∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)| +
              |∑ l ∈ Finset.Ico 2 n,
                (Delta (l + 1) - Delta l) / (l : ℝ)|) +
              |∑ l ∈ Finset.Ico 2 n,
                (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| := by
            gcongr
            exact abs_add_le _ _
      _ = (∑ l ∈ Finset.Ico 2 n, 2 / (l : ℝ)) +
          (∑ l ∈ Finset.Ico 2 n, 1 / (2 * (l : ℝ) ^ 2)) +
          |∑ l ∈ Finset.Ico 2 n,
            (Delta (l + 1) - Delta l) / (l : ℝ)| +
          |∑ l ∈ Finset.Ico 2 n,
            (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| := by
        rw [abs_of_nonneg hFirst0, abs_of_nonneg hSecond0]
      _ ≤ 2 * ((n : ℝ) ^ delta / delta) +
          ((n : ℝ) ^ delta / delta) +
          4 * B * (n : ℝ) ^ delta / delta +
          C / 2 * ((n : ℝ) ^ delta / delta) := by gcongr
      _ = (3 + 4 * B + C / 2) * ((n : ℝ) ^ delta / delta) := by ring
  calc
    _ ≤ (3 + 4 * B + C / 2) * ((n : ℝ) ^ delta / delta) := hTotalDelta
    _ ≤ (3 + 4 * B + C / 2) * ((n : ℝ) ^ (3 * delta) / delta) := by
      gcongr
      · exact_mod_cast (show 1 ≤ n by omega)
      · linarith
    _ = (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by ring

end

end Erdos1165.ProfileTaylor
