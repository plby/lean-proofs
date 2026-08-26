/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite-exponent prime moments for the entropy lower bound.
Informal source: the BBMST frame entropy, evaluated using finite truncations.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ScaledPrimeMoments

namespace Erdos1189

open Finset Filter

noncomputable def partialTau (T : ℕ) : ℝ := ∑ e ∈ range T, logIncrement e ^ 2

lemma partialTau_nonneg (T : ℕ) : 0 ≤ partialTau T := sum_nonneg fun _ _ => sq_nonneg _

lemma partialTau_tendsto : Tendsto partialTau atTop (nhds tau) :=
  summable_logIncrement_sq.hasSum.tendsto_sum_nat

noncomputable def truncatedPrimeMass (T : ℕ) (x : ℝ) : ℝ :=
  ∑ e ∈ range T, (Nat.primeCounting (Nat.ceil (x * logIncrement e)) : ℝ) * logIncrement e

noncomputable def truncatedScoreMoment (T : ℕ) (x : ℝ) : ℝ :=
  ∑ e ∈ range T, (∑ p ∈ Nat.primesLE (Nat.ceil (x * logIncrement e)),
    ((p : ℝ) - 1) ^ 2) / logIncrement e

lemma truncatedPrimeMass_nonneg (T : ℕ) (x : ℝ) : 0 ≤ truncatedPrimeMass T x :=
  sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (logIncrement_pos e).le

lemma real_primeCounting_ratio :
    Tendsto (fun x : ℝ => (Nat.primeCounting (Nat.ceil x) : ℝ) / realLogPower 1 x)
      atTop (nhds 1) := by
  apply tendsto_moment_at_real_cutoff (f := fun n => (Nat.primeCounting n : ℝ))
  simpa only [pow_zero, one_mul, zero_add] using primeCounting_endpoint_ratio 0

lemma truncatedPrimeMass_asymptotic (T : ℕ) :
    Tendsto (fun x : ℝ => truncatedPrimeMass T x / realLogPower 1 x)
      atTop (nhds (partialTau T)) := by
  have ht : ∀ e : ℕ, Tendsto (fun x : ℝ =>
      ((Nat.primeCounting (Nat.ceil (x * logIncrement e)) : ℝ) / realLogPower 1 x) *
        logIncrement e) atTop (nhds (logIncrement e ^ 2)) := by
    intro e
    have h := (tendsto_moment_scaling (logIncrement_pos e) real_primeCounting_ratio).mul_const
      (logIncrement e)
    simpa only [pow_one, one_mul, ← pow_two] using h
  have hsum := tendsto_finsetSum (range T) (fun e _ => ht e)
  apply hsum.congr'
  exact Eventually.of_forall fun x => by
    dsimp [truncatedPrimeMass]
    rw [sum_div]
    apply sum_congr rfl
    intro e _
    ring

lemma truncatedScoreMoment_asymptotic (T : ℕ) :
    Tendsto (fun x : ℝ => truncatedScoreMoment T x / realLogPower 3 x)
      atTop (nhds (partialTau T / 3)) := by
  have ht : ∀ e : ℕ, Tendsto (fun x : ℝ =>
      ((∑ p ∈ Nat.primesLE (Nat.ceil (x * logIncrement e)), ((p : ℝ) - 1) ^ 2) /
        realLogPower 3 x) / logIncrement e) atTop (nhds (logIncrement e ^ 2 / 3)) := by
    intro e
    have h := (tendsto_moment_scaling (logIncrement_pos e)
      real_prime_weight_square_sum_ratio).div_const (logIncrement e)
    convert h using 1
    congr 1
    field_simp
  have hsum := tendsto_finsetSum (range T) (fun e _ => ht e)
  rw [← sum_div] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun x => by
    dsimp [truncatedScoreMoment]
    rw [sum_div]
    apply sum_congr rfl
    intro e _
    ring

end Erdos1189
