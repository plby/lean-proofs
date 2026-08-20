/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.BadRootMass
import ErdosProblems.Erdos48.GoodBranchSelection

/-!
# Exact finite output of one analytic FLP scale

This structure is deliberately independent of the totient/divisor-sum
assembly in `Erdos48.lean`.  It is the finite target of the analytic proof:
a sparse bad-root set, enough usable shifted-smooth primes, and the raw
divisibility counts after budgeting the prime-chain collision loss.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- All finite information which the analytic good-scale argument must
produce at requested cardinality `K`. -/
structure FLPAnalyticScale (K : ℕ) where
  x : ℕ
  smoothBound : ℕ
  badRoots : Finset ℕ
  badRoots_prime_bound : ∀ q ∈ badRoots, q.Prime ∧ q ≤ smoothBound
  usable_card : K ≤
    (avoidingShiftedDivisors (smoothShiftedPrimes x smoothBound)
      (primeChainClosureTargets smoothBound badRoots)).card
  raw_counts : ∀ q : ℕ, q.Prime →
    q ∉ primeChainClosure (badRoots : Set ℕ) →
    q ≤ smoothBound →
    ((smoothBound / (q - 1) + 1 : ℕ) : ℝ) +
        ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
          ∑ t ∈ primeChainClosureTargets smoothBound badRoots,
            (t : ℝ)⁻¹ ≤
      ((((smoothShiftedPrimes x smoothBound).filter
        fun p ↦ q ∣ p + 1).card : ℕ) : ℝ)

/-- A more source-like interface: lower bounds for every nonbad root plus
two explicit numerical inequalities imply an `FLPAnalyticScale`. -/
noncomputable def FLPAnalyticScale.of_raw_lower_bounds
    {K x u : ℕ} {bad : Finset ℕ} {L : ℕ → ℝ}
    (hu : 2 ≤ u)
    (hbad : ∀ q ∈ bad, q.Prime ∧ q ≤ u)
    (htwo : 2 ∉ primeChainClosure (bad : Set ℕ))
    (hlower : ∀ q : ℕ, q.Prime → q ∉ bad → q ≤ u →
      L q ≤ ((((smoothShiftedPrimes x u).filter
        fun p ↦ q ∣ p + 1).card : ℕ) : ℝ))
    (hcard : (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) *
        ∑ t ∈ primeChainClosureTargets u bad, (t : ℝ)⁻¹ ≤ L 2)
    (hcounts : ∀ q : ℕ, q.Prime →
      q ∉ primeChainClosure (bad : Set ℕ) → q ≤ u →
      ((u / (q - 1) + 1 : ℕ) : ℝ) +
          ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
            ∑ t ∈ primeChainClosureTargets u bad, (t : ℝ)⁻¹ ≤ L q) :
    FLPAnalyticScale K := by
  classical
  let A := smoothShiftedPrimes x u
  let T := primeChainClosureTargets u bad
  let S := avoidingShiftedDivisors A T
  have htwoBad : 2 ∉ bad := by
    intro hmem
    exact htwo (mem_primeChainClosure_of_mem Nat.prime_two hmem)
  have htwoLower := hlower 2 Nat.prime_two htwoBad hu
  have htwoRaw : (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) *
        ∑ t ∈ T, (t : ℝ)⁻¹ ≤
      (((A.filter fun p ↦ 2 ∣ p + 1).card : ℕ) : ℝ) := by
    have hcard' : (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) *
          ∑ t ∈ T, (t : ℝ)⁻¹ ≤ L 2 := by
      simpa only [T] using hcard
    exact hcard'.trans htwoLower
  have hfiltered : K ≤ (S.filter fun p ↦ 2 ∣ p + 1).card := by
    apply le_card_avoiding_filter_of_real_harmonic_loss_le
      (A := A) (T := T) (x := x) (q := 2)
    · intro p hp
      exact (mem_smoothShiftedPrimes.mp (by simpa only [A] using hp)).1
    · exact Nat.prime_two
    · intro t ht
      change t ∈ primeChainClosureTargets u bad at ht
      rw [mem_primeChainClosureTargets] at ht
      obtain ⟨r, hr, htu, htPrime, hreach⟩ := ht
      exact htPrime
    · intro htwoT
      change 2 ∈ primeChainClosureTargets u bad at htwoT
      rw [mem_primeChainClosureTargets] at htwoT
      obtain ⟨r, hr, hru, hprime, hreach⟩ := htwoT
      exact htwo ⟨hprime, r, hr, hreach⟩
    · exact htwoRaw
  refine
    { x := x
      smoothBound := u
      badRoots := bad
      badRoots_prime_bound := hbad
      usable_card := ?_
      raw_counts := ?_ }
  · change K ≤ S.card
    exact hfiltered.trans (Finset.card_filter_le _ _)
  · intro q hq hqClosure hqu
    have hqBad : q ∉ bad := by
      intro hqBad
      exact hqClosure (mem_primeChainClosure_of_mem hq hqBad)
    exact (hcounts q hq hqClosure hqu).trans (hlower q hq hqBad hqu)

end

end Erdos48
