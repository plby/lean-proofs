/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovNumerics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Erdős Problem 446: the analytic core of Ford's Smirnov comparison

This file proves the pointwise inequality used in Ford's continuous
first-crossing argument.  The useful change of variable writes the quotient
as `(1 - x) / (1 + x)`.  The first term of the power series for
`atanh x = log ((1+x)/(1-x))/2` then gives the entire estimate, including
the endpoint-uniform dependence on the crossing parameter.
-/

namespace Erdos446

open Real

/-- The logarithmic estimate at the heart of Ford's first-crossing
comparison.  The hypotheses say that the numerator is positive and that
the crossing parameter belongs to `[0,1]`.

The slightly more symmetric real-variable form is useful independently of
the later application with `n = k - l` and integral `w`. -/
theorem fordSmirnovRatio_log_le
    {n w lam : ℝ} (hw : 0 ≤ w) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hn : w + 2 - lam < n) :
    Real.log ((n - w - 2 + lam) / (n + w + lam)) ≤
      -(2 * w + 2) / n := by
  let A : ℝ := w + 2 - lam
  let B : ℝ := w + lam
  let a : ℝ := A + B
  let d : ℝ := 2 * n + B - A
  let x : ℝ := a / d
  have hA0 : 0 ≤ A := by dsimp [A]; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hBA : B ≤ A := by dsimp [A, B]; linarith
  have ha : a = 2 * w + 2 := by dsimp [a, A, B]; ring
  have ha0 : 0 < a := by rw [ha]; linarith
  have hnA : A < n := by simpa [A] using hn
  have hn0 : 0 < n := lt_of_le_of_lt hA0 hnA
  have hd : d = 2 * n + B - A := rfl
  have hd0 : 0 < d := by
    dsimp [d]
    linarith
  have hxdiff : d - a = 2 * (n - A) := by
    dsimp [d, a]
    ring
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    apply (div_lt_one hd0).2
    have : 0 < d - a := by rw [hxdiff]; linarith
    linarith
  have h1mx : 0 < 1 - x := sub_pos.mpr hx1
  have h1px : 0 < 1 + x := by linarith
  have hratio : (n - w - 2 + lam) / (n + w + lam) =
      (1 - x) / (1 + x) := by
    have hnB : 0 < n + B := by linarith
    have habstract : (n - A) / (n + B) =
        (1 - x) / (1 + x) := by
      dsimp [x]
      field_simp [hd0.ne', hnB.ne', h1px.ne']
      dsimp [d, a]
      ring
    calc
      (n - w - 2 + lam) / (n + w + lam) =
          (n - A) / (n + B) := by dsimp [A, B]; congr 1 <;> ring
      _ = (1 - x) / (1 + x) := habstract
  have hatanh := Real.sum_range_le_log_div hx0 hx1 1
  have hxlog : 2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
    norm_num at hatanh
    nlinarith
  have hlogratio :
      Real.log ((1 - x) / (1 + x)) =
        -Real.log ((1 + x) / (1 - x)) := by
    rw [Real.log_div h1mx.ne' h1px.ne',
      Real.log_div h1px.ne' h1mx.ne']
    ring
  have hlogx : Real.log ((1 - x) / (1 + x)) ≤ -2 * x := by
    rw [hlogratio]
    linarith
  rw [hratio]
  calc
    Real.log ((1 - x) / (1 + x)) ≤ -2 * x := hlogx
    _ ≤ -a / n := by
      dsimp [x]
      have hcross : a * d ≤ (2 * a) * n := by
        dsimp [d]
        nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hBA)]
      have hdiv : a / n ≤ (2 * a) / d :=
        (div_le_div_iff₀ hn0 hd0).2 hcross
      calc
        -2 * (a / d) = -((2 * a) / d) := by ring
        _ ≤ -(a / n) := neg_le_neg hdiv
        _ = -a / n := by ring
    _ = -(2 * w + 2) / n := by rw [ha]

/-- Ford's pointwise power comparison.  This is equation (32b) in the
mathematical writeup, with `i = k-l`.

The weak common-range assumption also covers the zero-numerator endpoint;
the positive-numerator case is the logarithmic estimate above. -/
theorem fordSmirnovRatio_pow_le_exp_neg
    {i : ℕ} {w lam : ℝ} (hw : 0 ≤ w) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hi : w + 2 - lam ≤ i) :
    (((i : ℝ) - w - 2 + lam) / ((i : ℝ) + w + lam)) ^ i ≤
      Real.exp (-(2 * w + 2)) := by
  have hi0 : 0 < i := by
    have : (0 : ℝ) < i := by linarith
    exact_mod_cast this
  rcases hi.eq_or_lt with heq | hlt
  · have hnum : (i : ℝ) - w - 2 + lam = 0 := by linarith
    rw [hnum, zero_div, zero_pow (Nat.ne_of_gt hi0)]
    positivity
  · have hden : 0 < (i : ℝ) + w + lam := by positivity
    have hnum : 0 < (i : ℝ) - w - 2 + lam := by linarith
    have hratioPos : 0 <
        ((i : ℝ) - w - 2 + lam) / ((i : ℝ) + w + lam) :=
      div_pos hnum hden
    have hlog := fordSmirnovRatio_log_le hw hlam0 hlam1 hlt
    have hmul :
        (i : ℝ) * Real.log
            (((i : ℝ) - w - 2 + lam) / ((i : ℝ) + w + lam)) ≤
          -(2 * w + 2) := by
      have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
      calc
        (i : ℝ) * Real.log
            (((i : ℝ) - w - 2 + lam) / ((i : ℝ) + w + lam)) ≤
            (i : ℝ) * (-(2 * w + 2) / (i : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog hiR.le
        _ = -(2 * w + 2) := by field_simp
    calc
      (((i : ℝ) - w - 2 + lam) / ((i : ℝ) + w + lam)) ^ i =
          Real.exp ((i : ℝ) * Real.log
            (((i : ℝ) - w - 2 + lam) / ((i : ℝ) + w + lam))) := by
        rw [Real.exp_nat_mul, Real.exp_log hratioPos]
      _ ≤ Real.exp (-(2 * w + 2)) := Real.exp_le_exp.mpr hmul

end Erdos446
