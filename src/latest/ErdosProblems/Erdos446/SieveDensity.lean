/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.WeightedCluster
import ErdosProblems.Erdos697.Erdos697Cover

/-!
# Erdős Problem 446: exact finite prime-pattern densities

Ford's rough-factor construction is most transparent at the level of natural
density.  Divisibility by finitely many distinct primes is an independent
Bernoulli model by the Chinese remainder theorem.  This module packages that
model for the primes up to a natural cutoff.
-/

namespace Erdos446

open Finset Set MeasureTheory Real
open scoped BigOperators ENNReal NNReal Topology

/-- The finite set of primes at most `N`. -/
def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter Nat.Prime

/-- A prime, together with the proof that it is at most the cutoff. -/
abbrev PrimeIndex (N : ℕ) := {p : ℕ // p ∈ primesUpTo N}

/-- The primes up to `N` which divide `m`. -/
def primePattern (N m : ℕ) : Finset (PrimeIndex N) :=
  Finset.univ.filter fun p ↦ p.1 ∣ m

/-- The Bernoulli probability of an exact divisibility pattern. -/
noncomputable def primePatternWeight (N : ℕ) (T : Finset (PrimeIndex N)) : ℝ :=
  Erdos697.Bernoulli.weight (primesUpTo N).attach (fun p ↦ 1 / (p.1 : ℝ)) T

theorem primeIndex_prime {N : ℕ} (p : PrimeIndex N) : p.1.Prime := by
  exact (Finset.mem_filter.mp p.2).2

theorem primeIndex_pos {N : ℕ} (p : PrimeIndex N) : 0 < p.1 :=
  (primeIndex_prime p).pos

theorem primeIndex_pairwise_coprime (N : ℕ) :
    Pairwise (Function.onFun Nat.Coprime (fun p : PrimeIndex N ↦ p.1)) := by
  intro p q hpq
  exact (Nat.coprime_primes (primeIndex_prime p) (primeIndex_prime q)).mpr
    (fun hpqv ↦ hpq (Subtype.ext hpqv))

theorem mem_primePattern_iff {N m : ℕ} {p : PrimeIndex N} :
    p ∈ primePattern N m ↔ p.1 ∣ m := by
  simp [primePattern]

/-- Every predicate on the exact set of small prime divisors has the density
given by the corresponding finite Bernoulli sum. -/
theorem primePattern_event_hasDensity (N : ℕ)
    (Good : Finset (PrimeIndex N) → Prop) [DecidablePred Good] :
    {m : ℕ | Good (primePattern N m)}.HasDensity
      (∑ T ∈ (Finset.univ : Finset (Finset (PrimeIndex N))).filter Good,
        primePatternWeight N T) := by
  let q : PrimeIndex N → ℕ := fun p ↦ p.1
  have h := Erdos697.Cover.eventSet_hasDensity
    (I := PrimeIndex N) 1 (by norm_num) q
    (fun p ↦ primeIndex_pos p)
    (primeIndex_pairwise_coprime N)
    (fun p ↦ Nat.coprime_one_left p.1)
    Good
  norm_num at h
  simpa only [Erdos697.Cover.eventSet, one_dvd, true_and,
    Erdos697.Cover.selected, q, primePattern, one_div, one_mul,
    primePatternWeight] using h

/-- Density of one exact small-prime divisibility pattern. -/
theorem primePattern_eq_hasDensity (N : ℕ) (T : Finset (PrimeIndex N)) :
    {m : ℕ | primePattern N m = T}.HasDensity (primePatternWeight N T) := by
  have h := primePattern_event_hasDensity N (fun U ↦ U = T)
  have hfilter :
      (Finset.univ : Finset (Finset (PrimeIndex N))).filter (fun U ↦ U = T) = {T} := by
    ext U
    simp
  rw [hfilter] at h
  simpa using h

theorem primePatternWeight_nonneg (N : ℕ) (T : Finset (PrimeIndex N))
    (hT : T ⊆ Finset.univ) :
    0 ≤ primePatternWeight N T := by
  apply Erdos697.Bernoulli.weight_nonneg
  · intro p hp
    positivity
  · intro p hp
    have hp2 : 2 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp p.2).1).1
    rw [one_div]
    exact inv_le_one_of_one_le₀ (by
      exact_mod_cast (Nat.succ_le_of_lt (primeIndex_pos p)))
  · exact Finset.mem_powerset.mpr hT

/-- The density of avoiding every prime up to `N`. -/
noncomputable def smallPrimeEulerDensity (N : ℕ) : ℝ :=
  ∏ p : PrimeIndex N, (1 - 1 / (p.1 : ℝ))

theorem smallPrimeEulerDensity_nonneg (N : ℕ) :
    0 ≤ smallPrimeEulerDensity N := by
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p.1 := by
    exact_mod_cast (Nat.succ_le_of_lt (primeIndex_pos p))
  exact sub_nonneg.mpr (by
    rw [one_div]
    exact inv_le_one_of_one_le₀ hp1)

theorem smallPrimeEulerDensity_pos (N : ℕ) :
    0 < smallPrimeEulerDensity N := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast (primeIndex_prime p).one_lt
  exact sub_pos.mpr (by
    rw [one_div]
    exact inv_lt_one_of_one_lt₀ hp1)

end Erdos446
