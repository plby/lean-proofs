/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A summable envelope for the digit-exponent contributions.
Informal argument: u^2(1-log u) is bounded by a constant times u^(3/2) on (0,1].
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Tau
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos1189

lemma logIncrement_le_one (t : ℕ) : logIncrement t ≤ 1 := by
  apply (logIncrement_le_inv t).trans
  apply inv_le_one_of_one_le₀
  have h := Nat.cast_nonneg (α := ℝ) t
  linarith

lemma logarithmic_weight_bound {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ 2 * (1 - Real.log u) ≤ 3 * u ^ (3 / 2 : ℝ) := by
  have hlog := Real.log_le_rpow_div (inv_nonneg.mpr hu.le) (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog' : -Real.log u ≤ 2 * u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hu.le]
    rw [Real.log_inv, Real.inv_rpow hu.le] at hlog
    norm_num at hlog
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog' (sq_nonneg u)
  have hid : u ^ 2 * (2 * u ^ (-(1 / 2 : ℝ))) = 2 * u ^ (3 / 2 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hu]
    norm_num
  rw [hid] at hmul
  have hpow : u ^ 2 ≤ u ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hu hu1 (by norm_num)
  nlinarith

theorem summable_logIncrement_log_weight :
    Summable (fun t : ℕ => logIncrement t ^ 2 * (1 - Real.log (logIncrement t))) := by
  have hs : Summable (fun t : ℕ => 3 * (((t : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    have h := (summable_nat_add_iff
      (f := fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num))
    have h' : Summable (fun t : ℕ => (((t : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h
    exact h'.mul_left 3
  apply Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_) hs
  · have hl : Real.log (logIncrement t) ≤ 0 := by
      simpa using Real.log_le_log (logIncrement_pos t) (logIncrement_le_one t)
    exact mul_nonneg (sq_nonneg _) (by linarith)
  · apply (logarithmic_weight_bound (logIncrement_pos t) (logIncrement_le_one t)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have h := Real.rpow_le_rpow (logIncrement_pos t).le (logIncrement_le_inv t)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    simpa only [Real.inv_rpow (by positivity : (0 : ℝ) ≤ (t : ℝ) + 1)] using h

end Erdos1189
