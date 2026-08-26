/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The exact asymptotic divisor entropy of score-cutoff coordinate sets.
Informal source: the prime-number-theorem calculation in BBMST Lemma 6.3.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CoordinateKnapsack
import ErdosProblems.Erdos1189.PrimeCountDomination
import Mathlib.Analysis.Normed.Group.Tannery

namespace Erdos1189

open Finset Filter

lemma primeCounting_exponent_zero {x : ℝ} {e : ℕ} (he : Nat.ceil x ≤ e) :
    Nat.primeCounting (Nat.ceil (x * logIncrement e)) = 0 := by
  apply primeCounting_ceil_zero_of_le_one
  have he' : (Nat.ceil x : ℝ) ≤ e := by exact_mod_cast he
  have hx := Nat.le_ceil x
  have hprod : logIncrement e * ((e : ℝ) + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (by simpa only [one_div] using logIncrement_le_inv e)
  have hpos := logIncrement_pos e
  nlinarith

lemma countingMass_normalized_tsum (x : ℝ) :
    (∑' e : ℕ, (Nat.primeCounting (Nat.ceil (x * logIncrement e)) : ℝ) * logIncrement e /
      realLogPower 1 x) = coordinateMass (countingCoordinates x) / realLogPower 1 x := by
  rw [tsum_eq_sum (s := range (Nat.ceil x)) (fun e he => by
    rw [primeCounting_exponent_zero (by simpa only [mem_range, not_lt] using he),
      Nat.cast_zero, zero_mul, zero_div]), ← sum_div]
  congr 1
  rw [coordinateMass, sum_countingCoordinates_by_exponent]
  simp only [sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting]

theorem countingMass_asymptotic :
    Tendsto (fun x : ℝ => coordinateMass (countingCoordinates x) / realLogPower 1 x)
      atTop (nhds tau) := by
  obtain ⟨C, _, hdom⟩ := exists_counting_mass_domination
  have hterm : ∀ e : ℕ, Tendsto (fun x : ℝ =>
      (Nat.primeCounting (Nat.ceil (x * logIncrement e)) : ℝ) * logIncrement e /
        realLogPower 1 x) atTop (nhds (logIncrement e ^ 2)) := by
    intro e
    have ht := (tendsto_moment_scaling (logIncrement_pos e) real_primeCounting_ratio).mul_const
      (logIncrement e)
    simp only [pow_one, one_mul, ← pow_two] at ht
    apply ht.congr'
    exact Eventually.of_forall fun x => by dsimp only; ring
  have ht := tendsto_tsum_of_dominated_convergence
    (summable_logIncrement_log_weight.mul_left C) hterm
    ((eventually_ge_atTop (2 : ℝ)).mono fun x hx => hdom x hx)
  rw [← tau_eq_tsum_logIncrement] at ht
  apply ht.congr'
  exact Eventually.of_forall countingMass_normalized_tsum

end Erdos1189
