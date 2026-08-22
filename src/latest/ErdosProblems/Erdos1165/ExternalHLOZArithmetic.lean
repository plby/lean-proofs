/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Arithmetic at the HLOZ external-walk scale

This file contains the purely real-variable calculation used to pass from
the sharp retained-block Green-function estimate to the one-point local-time
tail estimate.  It is deliberately independent of the random-walk API.
-/

namespace Erdos1165.ExternalHLOZArithmetic

noncomputable section

/-- The elementary numerical inequality used in the external-walk one-point
tail argument.  The variable `t` is the HLOZ error scale `L ^ (5 / 8)`.

The lower bound on `r` is written with the original power `L ^ (13 / 8)` so
that the lemma can be applied directly to the probabilistic estimate. -/
theorem external_tail_lower_bound
    (L t D eps : ℝ) (r : ℕ)
    (hL : 0 < L)
    (ht : t = L ^ (5 / 8 : ℝ))
    (hscale : 8 * t ≤ L)
    (hten : 10 ≤ t)
    (hD : 0 < D)
    (hD_upper :
      D ≤ (15 / (16 * Real.pi) : ℝ) * L + t / 4)
    (heps_nonneg : 0 ≤ eps)
    (heps_upper : eps ≤ 1 / L)
    (hr :
      (15 / (16 * Real.pi) : ℝ) * L ^ 2 -
          2 * L ^ (13 / 8 : ℝ) - 1 ≤ (r : ℝ)) :
    (1 - eps) / D * (r : ℝ) ≥ L - 8 * t := by
  let c : ℝ := 15 / (16 * Real.pi)

  have hL_eighty : 80 ≤ L := by
    nlinarith
  have hL_one : 1 ≤ L := by
    linarith
  have ht_nonneg : 0 ≤ t := by
    linarith

  have hc_lower : (9 / 32 : ℝ) ≤ c := by
    dsimp [c]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Real.pi)]
    nlinarith [Real.pi_lt_d2]
  have hc_upper : c ≤ 1 := by
    dsimp [c]
    rw [div_le_one₀ (by positivity : (0 : ℝ) < 16 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hc_nonneg : 0 ≤ c := by
    positivity

  have hpower : L ^ (13 / 8 : ℝ) = L * t := by
    calc
      L ^ (13 / 8 : ℝ) = L ^ ((1 : ℝ) + 5 / 8) := by norm_num
      _ = L ^ (1 : ℝ) * L ^ (5 / 8 : ℝ) := Real.rpow_add hL 1 (5 / 8)
      _ = L * t := by rw [Real.rpow_one, ← ht]

  have ht_sq : t ^ 2 = L * L ^ (1 / 4 : ℝ) := by
    rw [ht, ← Real.rpow_natCast]
    rw [← Real.rpow_mul hL.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add hL, Real.rpow_one]
  have hquarter : 1 ≤ L ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hL_one (by norm_num)
  have hL_le_t_sq : L ≤ t ^ 2 := by
    rw [ht_sq]
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hquarter)]

  have hLt_nonneg : 0 ≤ L * t := mul_nonneg hL.le ht_nonneg
  have hL_sq_scale : 8 * L * t ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hL.le]
  have hLt_large : 800 ≤ L * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL_eighty)
      (sub_nonneg.mpr hten)]

  have hbase_nonneg : 0 ≤ c * L ^ 2 - 2 * L * t - 1 := by
    have hc_sq : (9 / 32 : ℝ) * L ^ 2 ≤ c * L ^ 2 :=
      mul_le_mul_of_nonneg_right hc_lower (sq_nonneg L)
    nlinarith

  have hinv_nonneg : 0 ≤ 1 / L := by positivity
  have hinv_le_one : 1 / L ≤ 1 := by
    exact (div_le_one₀ hL).2 hL_one
  have hfactor_nonneg : 0 ≤ 1 - eps := by
    nlinarith

  have hr' : c * L ^ 2 - 2 * L * t - 1 ≤ (r : ℝ) := by
    change (15 / (16 * Real.pi) : ℝ) * L ^ 2 - 2 * L * t - 1 ≤ (r : ℝ)
    calc
      (15 / (16 * Real.pi) : ℝ) * L ^ 2 - 2 * L * t - 1 =
          (15 / (16 * Real.pi) : ℝ) * L ^ 2 -
            2 * L ^ (13 / 8 : ℝ) - 1 := by rw [hpower]; ring
      _ ≤ (r : ℝ) := hr
  have hfactor_order : 1 - 1 / L ≤ 1 - eps := by
    linarith
  have hbase_to_r :
      (1 - 1 / L) * (c * L ^ 2 - 2 * L * t - 1) ≤
        (1 - eps) * (r : ℝ) := by
    calc
      (1 - 1 / L) * (c * L ^ 2 - 2 * L * t - 1)
          ≤ (1 - eps) * (c * L ^ 2 - 2 * L * t - 1) :=
        mul_le_mul_of_nonneg_right hfactor_order hbase_nonneg
      _ ≤ (1 - eps) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hr' hfactor_nonneg

  have hcoefficient : 0 ≤ 8 * c - 9 / 4 := by
    nlinarith
  have hfirst_term : 0 ≤ (8 * c - 9 / 4) * L * t := by
    positivity
  have hcL_le_t_sq : c * L ≤ t ^ 2 := by
    calc
      c * L ≤ 1 * L := mul_le_mul_of_nonneg_right hc_upper hL.le
      _ = L := one_mul L
      _ ≤ t ^ 2 := hL_le_t_sq
  have hsecond_term :
      0 ≤ 2 * t ^ 2 - c * L + 2 * t - 1 + 1 / L := by
    nlinarith [sq_nonneg t]

  have harithmetic :
      (c * L + t / 4) * (L - 8 * t) ≤
        (1 - 1 / L) * (c * L ^ 2 - 2 * L * t - 1) := by
    have hid :
        (1 - 1 / L) * (c * L ^ 2 - 2 * L * t - 1) -
            (c * L + t / 4) * (L - 8 * t) =
          (8 * c - 9 / 4) * L * t +
            (2 * t ^ 2 - c * L + 2 * t - 1 + 1 / L) := by
      field_simp [hL.ne']
      ring
    nlinarith

  have htarget_nonneg : 0 ≤ L - 8 * t := sub_nonneg.mpr hscale
  have hD_product :
      D * (L - 8 * t) ≤ (c * L + t / 4) * (L - 8 * t) := by
    apply mul_le_mul_of_nonneg_right
    · simpa [c] using hD_upper
    · exact htarget_nonneg
  have hproduct : D * (L - 8 * t) ≤ (1 - eps) * (r : ℝ) :=
    hD_product.trans (harithmetic.trans hbase_to_r)

  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hD).2 (by simpa [mul_comm] using hproduct)

end

end Erdos1165.ExternalHLOZArithmetic
