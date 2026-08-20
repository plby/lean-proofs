/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovOccupancy

/-!
# Erdős Problem 446: the numerical end of the Smirnov estimate

Ford's first-crossing comparison bounds the normalized ordered-simplex
volume by

`1 - exp (2 * w + 2) * (1 - (2 * w + 2) / v) ^ k`,

where `u + v = k + w`.  In the central range the expression has the
required order `(u + 1) * (w + 1)^2 / k`.  This file isolates that purely
real-variable estimate from the finite occupancy argument.
-/

namespace Erdos446

open Real

/-- The elementary logarithm estimate used at the end of Ford's Smirnov
argument. -/
theorem neg_log_one_sub_le_div {x : ℝ} (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hid : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
    field_simp [hpos.ne']
    ring
  rw [hid] at h
  linarith

/-- In Ford's central range the exponential comparison has the precise
scale needed by the uniform Smirnov estimate.  The deliberately generous
constant `24` keeps all later estimates integral and uniform. -/
theorem fordSmirnovExponentialComplement_le
    {k u v w : ℕ} (hk : 100 ≤ k) (hu : 10 * u ≤ k)
    (hw : w * w ≤ k) (hrel : u + v = k + w) :
    1 - Real.exp (2 * (w : ℝ) + 2) *
          (1 - (2 * (w : ℝ) + 2) / (v : ℝ)) ^ k ≤
      24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
  have hkR : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by positivity
  have huR : 10 * (u : ℝ) ≤ k := by exact_mod_cast hu
  have hwR : (w : ℝ) * w ≤ k := by exact_mod_cast hw
  have hrelR : (u : ℝ) + v = k + w := by exact_mod_cast hrel
  have hwk : 10 * (w : ℝ) ≤ k := by
    by_contra hnot
    have hlt : (k : ℝ) < 10 * w := lt_of_not_ge hnot
    nlinarith
  let a : ℝ := 2 * (w : ℝ) + 2
  have haPos : 0 < a := by dsimp [a]; positivity
  have haLe : 4 * a ≤ k := by
    dsimp [a]
    nlinarith
  have hvLower : 10 * (v : ℝ) ≥ 9 * k := by
    nlinarith
  have hvPos : (0 : ℝ) < v := by nlinarith
  have hvaLower : (k : ℝ) / 2 ≤ v - a := by
    nlinarith
  have hvaPos : 0 < (v : ℝ) - a := lt_of_lt_of_le (by positivity) hvaLower
  let x : ℝ := a / (v : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    rw [div_lt_one hvPos]
    linarith
  have hbasePos : 0 < 1 - x := sub_pos.mpr hx1
  have hexpRewrite :
      Real.exp a * (1 - x) ^ k =
        Real.exp (a + (k : ℝ) * Real.log (1 - x)) := by
    have hp : (1 - x) ^ k =
        Real.exp ((k : ℝ) * Real.log (1 - x)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbasePos]
    rw [hp, ← Real.exp_add]
  have hlinear :
      1 - Real.exp (a + (k : ℝ) * Real.log (1 - x)) ≤
        -(a + (k : ℝ) * Real.log (1 - x)) := by
    linarith [Real.add_one_le_exp (a + (k : ℝ) * Real.log (1 - x))]
  have hlog := neg_log_one_sub_le_div hx1
  have hlogMul :
      -(a + (k : ℝ) * Real.log (1 - x)) ≤
        (k : ℝ) * (x / (1 - x)) - a := by
    nlinarith
  have hratio : x / (1 - x) = a / ((v : ℝ) - a) := by
    dsimp [x]
    field_simp [hvPos.ne', hvaPos.ne']
  have hcoarse :
      (k : ℝ) * (a / ((v : ℝ) - a)) - a ≤
        24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
    have hdenInv : 1 / ((v : ℝ) - a) ≤ 2 / (k : ℝ) := by
      calc
        1 / ((v : ℝ) - a) ≤ 1 / ((k : ℝ) / 2) :=
          one_div_le_one_div_of_le (by positivity) hvaLower
        _ = 2 / (k : ℝ) := by field_simp [hkPos.ne']
    have hleft :
        (k : ℝ) * (a / ((v : ℝ) - a)) - a =
          a * ((u : ℝ) - w + a) / ((v : ℝ) - a) := by
      field_simp [hvaPos.ne']
      nlinarith
    rw [hleft]
    have hnumNonneg : 0 ≤ (u : ℝ) - w + a := by
      dsimp [a]
      nlinarith
    have hfirst :
        a * ((u : ℝ) - w + a) / ((v : ℝ) - a) ≤
          2 * a * ((u : ℝ) - w + a) / (k : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        a * ((u : ℝ) - w + a) * ((v : ℝ) - a)⁻¹ ≤
            a * ((u : ℝ) - w + a) * (2 / (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hdenInv)
            (mul_nonneg haPos.le hnumNonneg)
        _ = 2 * a * ((u : ℝ) - w + a) * (k : ℝ)⁻¹ := by ring
    calc
      a * ((u : ℝ) - w + a) / ((v : ℝ) - a) ≤
          2 * a * ((u : ℝ) - w + a) / (k : ℝ) := hfirst
      _ ≤ 24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
        apply (div_le_div_iff_of_pos_right hkPos).2
        dsimp [a]
        nlinarith [sq_nonneg ((u : ℝ) * w),
          sq_nonneg ((w : ℝ) + 1), sq_nonneg ((u : ℝ) + 1)]
  rw [show
    Real.exp (2 * (w : ℝ) + 2) *
        (1 - (2 * (w : ℝ) + 2) / (v : ℝ)) ^ k =
      Real.exp (a + (k : ℝ) * Real.log (1 - x)) by
        simpa [a, x] using hexpRewrite]
  exact hlinear.trans (hlogMul.trans (by simpa [hratio] using hcoarse))

end Erdos446
