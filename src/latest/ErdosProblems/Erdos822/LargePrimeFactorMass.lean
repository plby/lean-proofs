/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-!
# Elementary mass of prime factors above a cutoff
-/

namespace Erdos822

open scoped BigOperators

def primeFactorsAbove (n y : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => y < p

@[simp]
theorem mem_primeFactorsAbove_iff {n y p : ℕ} :
    p ∈ primeFactorsAbove n y ↔ p ∈ n.primeFactors ∧ y < p := by
  simp [primeFactorsAbove]

theorem card_primeFactorsAbove_le_log
    {n y : ℕ} (hn : 0 < n) :
    (primeFactorsAbove n y).card ≤ Nat.log 2 n := by
  have hprod : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    simpa using (Finset.prod_le_prod (fun _p _hp => Nat.zero_le 2) (fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le) :
        (∏ _p ∈ n.primeFactors, 2) ≤ ∏ p ∈ n.primeFactors, p)
  have hpow : 2 ^ n.primeFactors.card ≤ n :=
    hprod.trans (Nat.le_of_dvd hn n.prod_primeFactors_dvd)
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (Nat.le_log_of_pow_le (by norm_num) hpow)

/-- Reciprocal mass of prime factors above `y` is at most their number
divided by `y`; the logarithmic factor-count bound makes this explicit. -/
theorem sum_inv_primeFactorsAbove_le_log_div
    {n y : ℕ} (hn : 0 < n) (hy : 1 ≤ y) :
    ∑ p ∈ primeFactorsAbove n y, (1 : ℝ) / p ≤
      (Nat.log 2 n : ℝ) / y := by
  calc
    (∑ p ∈ primeFactorsAbove n y, (1 : ℝ) / p) ≤
        ∑ _p ∈ primeFactorsAbove n y, (1 : ℝ) / y := by
      apply Finset.sum_le_sum
      intro p hp
      have hyp : y ≤ p := (mem_primeFactorsAbove_iff.mp hp).2.le
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hyp)
    _ = ((primeFactorsAbove n y).card : ℝ) / y := by
      rw [Finset.sum_const]
      simp
      ring
    _ ≤ (Nat.log 2 n : ℝ) / y := by
      gcongr
      exact_mod_cast card_primeFactorsAbove_le_log hn

end Erdos822
