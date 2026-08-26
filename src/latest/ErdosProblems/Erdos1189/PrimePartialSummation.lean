/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite partial summation for weighted prime sums.
Informal argument: discrete Abel summation, used for the sharp counting estimates.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeEstimates
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace Erdos1189

open Finset

lemma primeCounting_succ (N : ℕ) :
    Nat.primeCounting (N + 1) = Nat.primeCounting N + if (N + 1).Prime then 1 else 0 := by
  exact Nat.count_succ (p := Nat.Prime) (N + 1)

lemma sum_primesLE_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), f p) =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  have hnot : N + 1 ∉ Nat.primesLE N := fun h =>
    Nat.not_succ_le_self N (Nat.le_of_mem_primesLE h)
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [sum_insert hnot, add_comm]
  · simp

theorem prime_partial_summation (f : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, f p) = f N * Nat.primeCounting N -
      ∑ i ∈ range N, (Nat.primeCounting i : ℝ) * (f (i + 1) - f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_primesLE_succ, ih, primeCounting_succ, sum_range_succ]
      split_ifs <;> push_cast <;> ring

lemma prime_power_sum (r N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ r) = (N : ℝ) ^ r * Nat.primeCounting N -
      ∑ i ∈ range N, (Nat.primeCounting i : ℝ) * (((i : ℝ) + 1) ^ r - (i : ℝ) ^ r) := by
  simpa only [Nat.cast_add, Nat.cast_one] using prime_partial_summation (fun p => (p : ℝ) ^ r) N

end Erdos1189
