/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# A quantitative harmonic-number remainder

This file records the elementary `O(1 / n)` form of the convergence of
`H_n - log n` to the Euler--Mascheroni constant.  It also extracts the
corresponding identity and remainder estimate for the sum of odd
reciprocals.  These estimates are useful when identifying the constant in
the potential kernel on a coordinate axis.
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialHarmonicRate

/-- The sum of the first `n` positive odd reciprocals. -/
noncomputable def oddReciprocalSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / (2 * k + 1 : ℝ)

/-- Quantitative convergence of `H_n - log n` to Euler's constant. -/
theorem abs_harmonic_sub_log_sub_eulerMascheroni_le {n : ℕ} (hn : 0 < n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤
      1 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlower :
      0 ≤ (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    rw [Real.eulerMascheroniSeq', if_neg hn.ne'] at h
    linarith
  rw [abs_of_nonneg hlower]
  have hupper := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  rw [Real.eulerMascheroniSeq] at hupper
  have hlog : Real.log (n + 1 : ℝ) - Real.log n ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div (by positivity : (n + 1 : ℝ) ≠ 0) hn0]
    have hrewrite : (n + 1 : ℝ) / n = 1 + 1 / (n : ℝ) := by
      field_simp
    rw [hrewrite]
    convert Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + 1 / (n : ℝ)) using 1
    all_goals ring_nf
  linarith

/-- Splitting `H_(2n)` into its even and odd summands. -/
theorem oddReciprocalSum_eq (n : ℕ) :
    oddReciprocalSum n =
      (harmonic (2 * n) : ℝ) - (1 / 2 : ℝ) * (harmonic n : ℝ) := by
  induction n with
  | zero => simp [oddReciprocalSum]
  | succ n ih =>
      rw [oddReciprocalSum, Finset.sum_range_succ]
      change oddReciprocalSum n + 1 / (2 * n + 1 : ℝ) = _
      rw [ih]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [harmonic_succ, harmonic_succ, harmonic_succ]
      rw [Rat.cast_add, Rat.cast_add, Rat.cast_add]
      norm_num only [Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      simp only [one_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
        Rat.cast_natCast, Rat.cast_one]
      field_simp
      ring

/-- The odd harmonic sum has the expected logarithmic main term, with an
explicit error bounded by `1 / n`. -/
theorem abs_oddReciprocalSum_sub_asymptotic_le {n : ℕ} (hn : 0 < n) :
    |oddReciprocalSum n - (1 / 2 : ℝ) * Real.log n - Real.log 2 -
        (1 / 2 : ℝ) * Real.eulerMascheroniConstant| ≤
      1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : 0 < 2 * n := by omega
  have hrate2 := abs_harmonic_sub_log_sub_eulerMascheroni_le h2n
  have hraten := abs_harmonic_sub_log_sub_eulerMascheroni_le hn
  have hlog : Real.log (2 * n : ℝ) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnR)]
  rw [oddReciprocalSum_eq]
  calc
    |(harmonic (2 * n) : ℝ) - (1 / 2 : ℝ) * (harmonic n : ℝ) -
          (1 / 2 : ℝ) * Real.log n - Real.log 2 -
          (1 / 2 : ℝ) * Real.eulerMascheroniConstant| =
        |((harmonic (2 * n) : ℝ) - Real.log (2 * n) -
            Real.eulerMascheroniConstant) -
          (1 / 2 : ℝ) * ((harmonic n : ℝ) - Real.log n -
          Real.eulerMascheroniConstant)| := by rw [hlog]; ring_nf
    _ ≤ |(harmonic (2 * n) : ℝ) - Real.log (2 * n) -
          Real.eulerMascheroniConstant| +
        |(1 / 2 : ℝ) * ((harmonic n : ℝ) - Real.log n -
          Real.eulerMascheroniConstant)| := abs_sub _ _
    _ ≤ 1 / (2 * n : ℝ) + (1 / 2 : ℝ) * (1 / (n : ℝ)) := by
      have hrate2' :
          |(harmonic (2 * n) : ℝ) - Real.log (2 * n : ℝ) -
              Real.eulerMascheroniConstant| ≤ 1 / (2 * n : ℝ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrate2
      have hscaled :
          |(1 / 2 : ℝ) * ((harmonic n : ℝ) - Real.log n -
              Real.eulerMascheroniConstant)| ≤
            (1 / 2 : ℝ) * (1 / (n : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left hraten (by norm_num)
      exact add_le_add hrate2' hscaled
    _ = 1 / (n : ℝ) := by field_simp; ring

/-- In particular, the centered odd reciprocal sums converge to
`log 2 + γ / 2`. -/
theorem tendsto_oddReciprocalSum_sub_half_log :
    Tendsto (fun n : ℕ ↦ oddReciprocalSum n - (1 / 2 : ℝ) * Real.log n)
      atTop
      (𝓝 (Real.log 2 + (1 / 2 : ℝ) * Real.eulerMascheroniConstant)) := by
  have hzero : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hcomp := tendsto_inv_atTop_zero.comp hcast
    apply hcomp.congr'
    exact Filter.Eventually.of_forall (fun n ↦ by simp [Function.comp_apply])
  have habs : Tendsto
      (fun n : ℕ ↦
        |(oddReciprocalSum n - (1 / 2 : ℝ) * Real.log n) -
          (Real.log 2 + (1 / 2 : ℝ) * Real.eulerMascheroniConstant)|)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n ↦ abs_nonneg _)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      convert abs_oddReciprocalSum_sub_asymptotic_le hn using 1
      all_goals ring_nf
    · exact hzero
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

end PotentialHarmonicRate
end Erdos1165
