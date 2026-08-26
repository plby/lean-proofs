/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The convergent logarithmic series in the sharp counting constant.
Informal source: BBMST's arithmetic-frame ordering and counting formula.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Statements
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

namespace Erdos1189

open Finset

/-- The paper's `log((e+1)/e)`, with zero-based index `t=e-1`. -/
noncomputable def logIncrement (t : ℕ) : ℝ := Real.log (1 + 1 / ((t : ℝ) + 1))

lemma logIncrement_pos (t : ℕ) : 0 < logIncrement t := by
  apply Real.log_pos
  have : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
  linarith

lemma logIncrement_le_inv (t : ℕ) : logIncrement t ≤ ((t : ℝ) + 1)⁻¹ := by
  have h := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 1 + 1 / ((t : ℝ) + 1) by positivity)
  simpa only [logIncrement, add_sub_cancel_left, one_div] using h

lemma logIncrement_strictAnti : StrictAnti logIncrement := by
  intro i j hij
  apply Real.log_lt_log (by positivity)
  have hcast : (i : ℝ) + 1 < (j : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hij 1
  have hdiv := one_div_lt_one_div_of_lt (show (0 : ℝ) < i + 1 by positivity) hcast
  linarith

lemma logIncrement_eq_log_sub (t : ℕ) :
    logIncrement t = Real.log ((t : ℝ) + 2) - Real.log ((t : ℝ) + 1) := by
  unfold logIncrement
  have heq : (1 : ℝ) + 1 / ((t : ℝ) + 1) = ((t : ℝ) + 2) / ((t : ℝ) + 1) := by
    field_simp
    ring
  rw [heq, Real.log_div (by positivity) (by positivity)]

lemma sum_logIncrement (n : ℕ) : (∑ t ∈ range n, logIncrement t) = Real.log (n + 1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih, logIncrement_eq_log_sub]
      norm_num only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      ring

lemma summable_logIncrement_sq : Summable (fun t : ℕ => logIncrement t ^ 2) := by
  have hs : Summable (fun t : ℕ => (((t : ℝ) + 1)⁻¹) ^ 2) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num))
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using h
  apply Summable.of_nonneg_of_le (fun t => sq_nonneg _) (fun t => ?_) hs
  exact pow_le_pow_left₀ (logIncrement_pos t).le (logIncrement_le_inv t) 2

lemma tau_eq_tsum_logIncrement : tau = ∑' t : ℕ, logIncrement t ^ 2 := rfl

theorem tau_pos : 0 < tau := by
  rw [tau_eq_tsum_logIncrement]
  exact summable_logIncrement_sq.tsum_pos (fun t => sq_nonneg _) 0
    (sq_pos_of_pos (logIncrement_pos 0))

lemma sum_logIncrement_sq_le_tau (n : ℕ) : (∑ t ∈ range n, logIncrement t ^ 2) ≤ tau := by
  rw [tau_eq_tsum_logIncrement]
  exact summable_logIncrement_sq.sum_le_tsum (range n) (fun _ _ => sq_nonneg _)

end Erdos1189
