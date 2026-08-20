/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockEstimates

/-!
# Erdős Problem 446: short reciprocal-prime windows

The largest-differing-prime argument confines one prime to an interval whose
endpoint ratio is at most four.  Such a window is the union of two dyadic
prime intervals and therefore has reciprocal mass `O(1 / log x)`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Primes in `(x,4x]`. -/
def quadruplePrimes (x : ℕ) : Finset ℕ :=
  Nat.primesLE (4 * x) \ Nat.primesLE x

noncomputable def quadruplePrimeMass (x : ℕ) : ℝ :=
  ∑ p ∈ quadruplePrimes x, 1 / (p : ℝ)

theorem mem_quadruplePrimes {x p : ℕ} :
    p ∈ quadruplePrimes x ↔ x < p ∧ p ≤ 4 * x ∧ p.Prime := by
  simp only [quadruplePrimes, Finset.mem_sdiff, Nat.mem_primesLE,
    not_and_or, not_le]
  aesop

theorem quadruplePrimes_subset_dyadic_union (x : ℕ) :
    quadruplePrimes x ⊆ dyadicPrimes x ∪ dyadicPrimes (2 * x) := by
  intro p hp
  have hp' := mem_quadruplePrimes.mp hp
  by_cases hp2 : p ≤ 2 * x
  · exact Finset.mem_union_left _ (mem_dyadicPrimes.mpr
      ⟨hp'.1, hp2, hp'.2.2⟩)
  · exact Finset.mem_union_right _ (mem_dyadicPrimes.mpr
      ⟨lt_of_not_ge hp2, by omega, hp'.2.2⟩)

theorem quadruplePrimeMass_le_dyadic (x : ℕ) :
    quadruplePrimeMass x ≤ dyadicPrimeMass x + dyadicPrimeMass (2 * x) := by
  rw [quadruplePrimeMass, dyadicPrimeMass, dyadicPrimeMass]
  calc
    (∑ p ∈ quadruplePrimes x, 1 / (p : ℝ)) ≤
        ∑ p ∈ dyadicPrimes x ∪ dyadicPrimes (2 * x), 1 / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (quadruplePrimes_subset_dyadic_union x)
      intro p hp hpnot
      positivity
    _ = (∑ p ∈ dyadicPrimes x, 1 / (p : ℝ)) +
        ∑ p ∈ dyadicPrimes (2 * x), 1 / (p : ℝ) := by
      rw [Finset.sum_union]
      rw [Finset.disjoint_left]
      intro p hpx hp2x
      have hxData := mem_dyadicPrimes.mp hpx
      have h2xData := mem_dyadicPrimes.mp hp2x
      omega

theorem quadruplePrimeMass_upper
    {N x : ℕ} (hN : 3 ≤ N) (hx : N ≤ x)
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    quadruplePrimeMass x ≤ 6 / Real.log (x : ℝ) := by
  have hx3 : 3 ≤ x := hN.trans hx
  have hxlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have h2x : N ≤ 2 * x := hx.trans (by omega)
  have hlogmono : Real.log (x : ℝ) ≤ Real.log (2 * x : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show x ≤ 2 * x by omega)
  calc
    quadruplePrimeMass x ≤
        dyadicPrimeMass x + dyadicPrimeMass (2 * x) :=
      quadruplePrimeMass_le_dyadic x
    _ ≤ 3 / Real.log (x : ℝ) +
        3 / Real.log ((2 * x : ℕ) : ℝ) :=
      add_le_add (hprime x hx) (hprime (2 * x) h2x)
    _ ≤ 3 / Real.log (x : ℝ) + 3 / Real.log (x : ℝ) := by
      gcongr
      omega
    _ = 6 / Real.log (x : ℝ) := by ring

/-- A quadruple window beginning at the `j`th block endpoint has mass at
most an explicit multiple of `2^{-j}`. -/
theorem quadruplePrimeMass_blockEndpoint_upper
    {N j : ℕ} (hN : 3 ≤ N) (hendpoint : N ≤ blockEndpoint j)
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    quadruplePrimeMass (blockEndpoint j) ≤
      6 / ((2 : ℝ) ^ j * Real.log 2) := by
  simpa only [log_blockEndpoint] using
    quadruplePrimeMass_upper hN hendpoint hprime

/-- Reciprocal mass of an arbitrary finite prime set. -/
noncomputable def primeSetMass (Q : Finset ℕ) : ℝ :=
  ∑ p ∈ Q, 1 / (p : ℝ)

/-- A set of primes lying in one block and mutually within a factor four has
mass `O(1 / log(blockEndpoint j))`.  This form avoids choosing integer
endpoints for the interval imposed by the close-divisor inequality. -/
theorem comparable_primeSetMass_upper
    {N j : ℕ} (hN : 3 ≤ N) (hendpoint : N ≤ blockEndpoint j)
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    {Q : Finset ℕ} (hQblock : Q ⊆ primeBlock j)
    (hcomp : ∀ p ∈ Q, ∀ q ∈ Q, p ≤ 4 * q) :
    primeSetMass Q ≤ 7 / Real.log (blockEndpoint j : ℝ) := by
  classical
  by_cases hQ : Q.Nonempty
  · let q : ℕ := Q.min' hQ
    have hqQ : q ∈ Q := Finset.min'_mem Q hQ
    have hqBlock := hQblock hqQ
    have hqPrime : q.Prime := (mem_primeBlock.mp hqBlock).1
    have hqLower : blockEndpoint j < q := (mem_primeBlock.mp hqBlock).2.1
    have hqN : N ≤ q := hendpoint.trans hqLower.le
    have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    have hendpointPos : (0 : ℝ) < blockEndpoint j := by
      exact_mod_cast blockEndpoint_pos j
    have herase : Q.erase q ⊆ quadruplePrimes q := by
      intro p hp
      have hpQ := Finset.mem_of_mem_erase hp
      have hpne : p ≠ q := Finset.ne_of_mem_erase hp
      have hqp : q < p := lt_of_le_of_ne (Finset.min'_le Q p hpQ) hpne.symm
      exact mem_quadruplePrimes.mpr
        ⟨hqp, hcomp p hpQ q hqQ,
          (mem_primeBlock.mp (hQblock hpQ)).1⟩
    have heraseMass :
        (∑ p ∈ Q.erase q, 1 / (p : ℝ)) ≤ quadruplePrimeMass q := by
      rw [quadruplePrimeMass]
      apply Finset.sum_le_sum_of_subset_of_nonneg herase
      intro p hp hpnot
      positivity
    have hqWindow : quadruplePrimeMass q ≤ 6 / Real.log (q : ℝ) :=
      quadruplePrimeMass_upper hN hqN hprime
    have hlogEndpoint : 0 < Real.log (blockEndpoint j : ℝ) :=
      Real.log_pos (by
        exact_mod_cast (show 1 < blockEndpoint j by
          exact lt_of_lt_of_le (by omega : 1 < N) hendpoint))
    have hlogMono : Real.log (blockEndpoint j : ℝ) ≤ Real.log (q : ℝ) := by
      exact Real.log_le_log hendpointPos (by exact_mod_cast hqLower.le)
    have hinvQ : 1 / (q : ℝ) ≤ 1 / (blockEndpoint j : ℝ) :=
      one_div_le_one_div_of_le hendpointPos (by exact_mod_cast hqLower.le)
    have hlogLeEndpoint :
        Real.log (blockEndpoint j : ℝ) ≤ (blockEndpoint j : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hendpointPos
      linarith
    have hendpointInv :
        1 / (blockEndpoint j : ℝ) ≤
          1 / Real.log (blockEndpoint j : ℝ) :=
      one_div_le_one_div_of_le hlogEndpoint hlogLeEndpoint
    calc
      primeSetMass Q =
          (∑ p ∈ Q.erase q, 1 / (p : ℝ)) + 1 / (q : ℝ) := by
        rw [primeSetMass]
        exact (Finset.sum_erase_add Q
          (fun p : ℕ ↦ 1 / (p : ℝ)) hqQ).symm
      _ ≤ quadruplePrimeMass q + 1 / (q : ℝ) :=
        add_le_add heraseMass le_rfl
      _ ≤ 6 / Real.log (q : ℝ) + 1 / (q : ℝ) :=
        add_le_add hqWindow le_rfl
      _ ≤ 6 / Real.log (blockEndpoint j : ℝ) +
          1 / (blockEndpoint j : ℝ) := by
        apply add_le_add
        · gcongr
        · exact hinvQ
      _ ≤ 6 / Real.log (blockEndpoint j : ℝ) +
          1 / Real.log (blockEndpoint j : ℝ) :=
        add_le_add le_rfl hendpointInv
      _ = 7 / Real.log (blockEndpoint j : ℝ) := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp [primeSetMass]
    positivity

end Erdos446
