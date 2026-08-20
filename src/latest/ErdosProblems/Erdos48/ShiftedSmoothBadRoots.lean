/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GoodScaleInput

/-!
# Bad roots for shifted smooth primes

This file turns a family of desired lower bounds into the literal finite set
of prime moduli where the bounds fail.  It then combines prefix sparsity of
that set with the weighted prime-chain estimate and the exact finite
good-scale constructor.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Prime moduli at most `u` for which the requested shifted-smooth-prime
lower bound fails. -/
noncomputable def shiftedSmoothBadRoots
    (x u : ℕ) (L : ℕ → ℝ) : Finset ℕ :=
  (Nat.primesLE u).filter fun q ↦
    ((((smoothShiftedPrimes x u).filter
      fun p ↦ q ∣ p + 1).card : ℕ) : ℝ) < L q

@[simp] theorem mem_shiftedSmoothBadRoots
    {x u : ℕ} {L : ℕ → ℝ} {q : ℕ} :
    q ∈ shiftedSmoothBadRoots x u L ↔
      q ≤ u ∧ q.Prime ∧
        ((((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℕ) : ℝ) < L q := by
  classical
  rw [shiftedSmoothBadRoots, Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem shiftedSmoothBadRoots_prime_bound
    {x u : ℕ} {L : ℕ → ℝ} {q : ℕ}
    (hq : q ∈ shiftedSmoothBadRoots x u L) :
    q.Prime ∧ q ≤ u := by
  have h := mem_shiftedSmoothBadRoots.mp hq
  exact ⟨h.2.1, h.1⟩

/-- Outside the bad-root set, the defining lower bound holds. -/
theorem shiftedSmoothLowerBound_of_not_mem_badRoots
    {x u : ℕ} {L : ℕ → ℝ} {q : ℕ}
    (hq : q.Prime) (hqu : q ≤ u)
    (hqBad : q ∉ shiftedSmoothBadRoots x u L) :
    L q ≤ ((((smoothShiftedPrimes x u).filter
      fun p ↦ q ∣ p + 1).card : ℕ) : ℝ) := by
  by_contra hnot
  have hlt :
      ((((smoothShiftedPrimes x u).filter
        fun p ↦ q ∣ p + 1).card : ℕ) : ℝ) < L q :=
    lt_of_not_ge hnot
  exact hqBad (mem_shiftedSmoothBadRoots.mpr ⟨hqu, hq, hlt⟩)

/-- If two is not a bad root, then it is not in the upward prime-chain
closure of the bad roots.  A chain ending at two must have started at two. -/
theorem two_not_mem_badRoot_primeChainClosure
    {x u : ℕ} {L : ℕ → ℝ}
    (htwo : 2 ∉ shiftedSmoothBadRoots x u L) :
    2 ∉ primeChainClosure
      (shiftedSmoothBadRoots x u L : Set ℕ) := by
  rintro ⟨_htwoPrime, q, hqBad, hqTwo⟩
  have hqPrime :=
    (shiftedSmoothBadRoots_prime_bound hqBad).1
  have hqLe : q ≤ 2 := primeChainReachable_le hqTwo
  have hqEq : q = 2 := by
    have hqTwoLe := hqPrime.two_le
    omega
  exact htwo (hqEq ▸ hqBad)

/-- Exact assembly from a harmonic upper bound for the closure of the
literal bad-root set.  The two displayed numerical premises are the only
remaining parameter inequalities. -/
noncomputable def FLPAnalyticScale.of_badRoot_harmonic_bound
    {K x u : ℕ} {L : ℕ → ℝ} {H : ℝ}
    (hu : 2 ≤ u)
    (htwo : 2 ∉ shiftedSmoothBadRoots x u L)
    (hmass :
      (∑ t ∈ primeChainClosureTargets u
          (shiftedSmoothBadRoots x u L), (t : ℝ)⁻¹) ≤ H)
    (hcard :
      (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) * H ≤ L 2)
    (hcounts : ∀ q : ℕ, q.Prime →
      q ∉ primeChainClosure
        (shiftedSmoothBadRoots x u L : Set ℕ) →
      q ≤ u →
      ((u / (q - 1) + 1 : ℕ) : ℝ) +
          ((x + 1 : ℕ) : ℝ) / (q : ℝ) * H ≤ L q) :
    FLPAnalyticScale K := by
  let bad := shiftedSmoothBadRoots x u L
  apply FLPAnalyticScale.of_raw_lower_bounds
      (x := x) (u := u) (bad := bad) (L := L) hu
  · intro q hq
    exact shiftedSmoothBadRoots_prime_bound hq
  · exact two_not_mem_badRoot_primeChainClosure htwo
  · intro q hq hqBad hqu
    exact shiftedSmoothLowerBound_of_not_mem_badRoots hq hqu hqBad
  · calc
      (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) *
          ∑ t ∈ primeChainClosureTargets u bad, (t : ℝ)⁻¹ ≤
          (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) * H := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hmass (by positivity))
      _ ≤ L 2 := hcard
  · intro q hq hqClosure hqu
    calc
      ((u / (q - 1) + 1 : ℕ) : ℝ) +
          ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
            ∑ t ∈ primeChainClosureTargets u bad, (t : ℝ)⁻¹ ≤
          ((u / (q - 1) + 1 : ℕ) : ℝ) +
            ((x + 1 : ℕ) : ℝ) / (q : ℝ) * H := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hmass (by positivity))
      _ ≤ L q := hcounts q hq hqClosure hqu

/-- Prefix sparsity of the literal bad roots implies one exact analytic
scale once the FKL constants and the two elementary parameter inequalities
are supplied. -/
noncomputable def FLPAnalyticScale.of_sparse_badRoots
    {K x u : ℕ} {L : ℕ → ℝ}
    {epsilon rho C : ℝ} {Q : ℕ}
    (hu : 2 ≤ u)
    (hQ : 2 ≤ Q)
    (hbadLarge : ∀ q ∈ shiftedSmoothBadRoots x u L, Q < q)
    (hprefix : ∀ y : ℕ,
      ((((shiftedSmoothBadRoots x u L).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤ rho * y)
    (hclosure : ∀ (E : Finset ℕ) (v : ℕ) (r : ℝ),
      (∀ q ∈ E, q.Prime ∧ Q < q ∧ q ≤ v) →
      (∀ y : ℕ, (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤ r * y) →
      (∑ t ∈ primeChainClosureTargets v E, (t : ℝ)⁻¹) ≤
        C * (v : ℝ) ^ epsilon * ((Nat.log 2 v : ℝ) * (2 * r)))
    (hcard :
      (K : ℝ) + ((x + 1 : ℕ) : ℝ) / (2 : ℝ) *
          (C * (u : ℝ) ^ epsilon *
            ((Nat.log 2 u : ℝ) * (2 * rho))) ≤ L 2)
    (hcounts : ∀ q : ℕ, q.Prime →
      q ∉ primeChainClosure
        (shiftedSmoothBadRoots x u L : Set ℕ) →
      q ≤ u →
      ((u / (q - 1) + 1 : ℕ) : ℝ) +
          ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
            (C * (u : ℝ) ^ epsilon *
              ((Nat.log 2 u : ℝ) * (2 * rho))) ≤ L q) :
    FLPAnalyticScale K := by
  apply FLPAnalyticScale.of_badRoot_harmonic_bound hu
  · intro htwoBad
    have hlarge := hbadLarge 2 htwoBad
    omega
  · apply hclosure (shiftedSmoothBadRoots x u L) u rho
    · intro q hq
      have hqData := shiftedSmoothBadRoots_prime_bound hq
      exact ⟨hqData.1, hbadLarge q hq, hqData.2⟩
    · exact hprefix
  · exact hcard
  · exact hcounts

end

end Erdos48
