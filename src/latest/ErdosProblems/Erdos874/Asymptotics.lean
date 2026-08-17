/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Erdős Problem 874: asymptotics of the exact formula

This file contains the analytic final step in the resolution of Problem 874.
It proves directly that

`Nat.sqrt (4 * N + 1) - 1 = (2 + o(1)) * Real.sqrt N`

and packages transfer of the limit along eventual equality.  The proof only
uses the elementary floor-square-root inequalities.  For every positive `N`,
the normalized exact formula lies between `2 - 2 / Real.sqrt N` and `2`.
-/

open Filter

namespace Erdos874

/-- The closed formula for `k(N)` supplied by the eventual resolution of
Erdős Problem 874. -/
def closedForm (N : ℕ) : ℕ := Nat.sqrt (4 * N + 1) - 1

/-- The elementary squeeze bounds for the normalized closed formula. -/
lemma closedForm_normalized_bounds {N : ℕ} (hN : 1 ≤ N) :
    2 - 2 / Real.sqrt N ≤ (closedForm N : ℝ) / Real.sqrt N ∧
      (closedForm N : ℝ) / Real.sqrt N ≤ 2 := by
  let q := Nat.sqrt (4 * N + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.sqrt_pos.mpr (by omega)
  have hq_sq_nat : q * q ≤ 4 * N + 1 := by
    simpa [q] using Nat.sqrt_le (4 * N + 1)
  have hq_next_nat : 4 * N + 1 < (q + 1) * (q + 1) := by
    simpa [q, pow_two] using Nat.lt_succ_sqrt' (4 * N + 1)
  have hq_sq : (q : ℝ) ^ 2 ≤ 4 * (N : ℝ) + 1 := by
    norm_num [pow_two]
    exact_mod_cast hq_sq_nat
  have hq_next : 4 * (N : ℝ) + 1 < ((q : ℝ) + 1) ^ 2 := by
    norm_num [pow_two]
    exact_mod_cast hq_next_nat
  have hsqrt_sq : (Real.sqrt N) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  have hsqrt_nonneg : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsqrt_pos : 0 < Real.sqrt N :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega))
  have hq_nonneg : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hq_lower : 2 * Real.sqrt N < (q : ℝ) + 1 := by
    nlinarith
  have hq_upper : (q : ℝ) - 1 ≤ 2 * Real.sqrt N := by
    nlinarith
  have hcast : (closedForm N : ℝ) = (q : ℝ) - 1 := by
    rw [closedForm, show Nat.sqrt (4 * N + 1) = q by rfl]
    simpa using (Nat.cast_sub (R := ℝ) (Nat.succ_le_iff.mpr hqpos))
  rw [hcast]
  constructor
  · calc
      2 - 2 / Real.sqrt N = (2 * Real.sqrt N - 2) / Real.sqrt N := by
        field_simp
      _ ≤ ((q : ℝ) - 1) / Real.sqrt N :=
        (div_le_div_iff_of_pos_right hsqrt_pos).2 (by linarith)
  · apply (div_le_iff₀ hsqrt_pos).2
    exact hq_upper

/-- The reciprocal of the real square root tends to zero along the natural
numbers. -/
lemma tendsto_inv_real_sqrt_nat :
    Tendsto (fun N : ℕ ↦ 1 / Real.sqrt N) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- The exact closed formula is asymptotic to `2 * Real.sqrt N`. -/
theorem tendsto_closedForm_normalized :
    Tendsto (fun N : ℕ ↦ (closedForm N : ℝ) / Real.sqrt N) atTop (nhds 2) := by
  have hlower :
      Tendsto (fun N : ℕ ↦ (2 : ℝ) - 2 / Real.sqrt N) atTop (nhds 2) := by
    have hzero :
        Tendsto (fun N : ℕ ↦ (2 : ℝ) / Real.sqrt N) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds.sub hzero :
      Tendsto (fun N : ℕ ↦ (2 : ℝ) - 2 / Real.sqrt N) atTop (nhds (2 - 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (closedForm_normalized_bounds hN).1
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (closedForm_normalized_bounds hN).2

/-- Any natural-valued function which eventually equals the exact formula
has the same normalized limit. -/
theorem tendsto_normalized_of_eventuallyEq_closedForm {f : ℕ → ℕ}
    (hf : f =ᶠ[atTop] closedForm) :
    Tendsto (fun N : ℕ ↦ (f N : ℝ) / Real.sqrt N) atTop (nhds 2) := by
  apply tendsto_closedForm_normalized.congr'
  filter_upwards [hf] with N hN
  rw [hN]

/-- Expression-level version of `tendsto_closedForm_normalized`. -/
theorem tendsto_sqrt_formula_normalized :
    Tendsto
      (fun N : ℕ ↦ ((Nat.sqrt (4 * N + 1) - 1 : ℕ) : ℝ) / Real.sqrt N)
      atTop (nhds 2) := by
  simpa [closedForm] using tendsto_closedForm_normalized

/-- Expression-level transfer theorem: eventual equality with the exact
integer formula implies the asymptotic claimed in Problem 874. -/
theorem tendsto_normalized_of_eventuallyEq_sqrt_formula {f : ℕ → ℕ}
    (hf : f =ᶠ[atTop] fun N ↦ Nat.sqrt (4 * N + 1) - 1) :
    Tendsto (fun N : ℕ ↦ (f N : ℝ) / Real.sqrt N) atTop (nhds 2) := by
  apply tendsto_normalized_of_eventuallyEq_closedForm
  filter_upwards [hf] with N hN
  simpa [closedForm] using hN

end Erdos874
