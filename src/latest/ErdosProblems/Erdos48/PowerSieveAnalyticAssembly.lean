/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveGoodScaleNumerics

/-!
# Eventual assembly of a power-sieve analytic scale

This module is the final deterministic interface for the good branch.  It
combines eventual prefix sparsity and escape of the literal bad roots with
the prime-chain harmonic estimate and the elementary endpoint numerics.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Eventual bad-root sparsity, escape beyond every fixed cutoff, and a raw
shifted-smooth lower bound produce an `FLPAnalyticScale` of any prescribed
finite size. -/
theorem eventually_nonempty_FLPAnalyticScale_of_powerSieve_badRoots
    (K L : ℕ) (hL : 1 ≤ L) (A : ℝ) (hA : 0 < A)
    (rawLower : ℕ → ℕ → ℝ)
    (hlarge : ∀ Q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (rawLower n), Q < q)
    (hprefix : ∀ᶠ n : ℕ in atTop, ∀ y : ℕ,
      ((((shiftedSmoothBadRoots (powerSieveX n L)
        (powerSieveSmoothBound n L) (rawLower n)).filter
          fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (A / Real.sqrt (n : ℝ)) * y)
    (hraw : ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime →
      q ≤ powerSieveSmoothBound n L →
        powerSieveRawLower n L q ≤ rawLower n q) :
    ∀ᶠ n : ℕ in atTop, Nonempty (FLPAnalyticScale K) := by
  obtain ⟨Q, C, hC, hclosure⟩ :=
    exists_powerSievePrimeChainClosure_eventually_le
      L hL A hA rawLower
  have hmass := hclosure (hlarge Q) hprefix
  have htwoLarge := hlarge 2
  have hnumeric := eventually_powerSieve_goodScale_numerics K L hL
  filter_upwards [hmass, htwoLarge, hraw, hnumeric,
      eventually_ge_atTop 2] with n hmass htwoLarge hraw hnumeric hn
  have hu : 2 ≤ powerSieveSmoothBound n L := by
    unfold powerSieveSmoothBound
    have hexp : 0 < 120 * L - 6 := by omega
    exact hn.trans (Nat.le_pow hexp)
  have htwo : 2 ∉ shiftedSmoothBadRoots (powerSieveX n L)
      (powerSieveSmoothBound n L) (rawLower n) := by
    intro hbad
    have := htwoLarge 2 hbad
    omega
  refine ⟨FLPAnalyticScale.of_powerSievePrimeChainAssembly
    hL hu htwo hmass hraw hnumeric.1 ?_⟩
  intro q hq _hqClosure hqu
  exact hnumeric.2 q hq hqu

end

end Erdos48
