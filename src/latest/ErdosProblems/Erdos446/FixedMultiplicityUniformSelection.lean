/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedMultiplicityExactFamily
import ErdosProblems.Erdos446.IsolatedPrimeSelectionMass

/-!
# Erdős Problem 446: zero-safe fixed-multiplicity selection

The pointwise sampling estimate in `FixedMultiplicityExactFamily` compares
the largest atom with half the total mass of the isolated prime windows.
That formulation is inconvenient when the isolated-divisor count is zero.
The zero-safe estimate from `IsolatedPrimeSelectionMass` instead uses the
uniform bound `r a / y ≤ 1 / (8 log y)` and proves the zero case directly.

This file combines that estimate with the exact-multiplicity CRT family.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The zero-safe isolated-divisor moment passes directly to the density of
integers having exactly `r` divisors in the dyadic interval. -/
theorem isolatedPowerMass_density_lower
    {N y r L : ℕ} (A : Finset ℕ)
    (hy : 0 < y) (hr : 1 ≤ r)
    (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAsmall : ∀ a ∈ A, 2 * a * a < y)
    (hAbound : ∀ a ∈ A, a ≤ 2 * y)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hatom : ∀ a ∈ A,
      (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
        1 / (8 * Real.log (y : ℝ))) :
    smallPrimeEulerDensity (2 * y) *
        ((((1 / (8 * Real.log (y : ℝ))) ^ r) /
            (r.factorial : ℝ)) *
          (∑ a ∈ A,
            ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ))) ≤
      epsilonR r y (2 * y) := by
  have hinj : Set.InjOn smallOuterModulus
      (smallOuterPairs A (fun a ↦ isolatedPrimeSubsets y a r)) := by
    simpa [isolatedPrimeSubsets, isolatedOuterPrimeSets] using
      (isolatedExactModuli_factorization_injective
        y r L A hApos hAsq hAcut houter)
  have hmass := isolatedPowerMass_le_isolatedPrimeModuliMass
    hN hprime hy hr hApos hscale hatom hinj
  have hdensity := isolatedExactModuli_density_lower (r := r) A hy hApos hAsq
    hAsmall hAbound hAcut houter
  have heuler : 0 ≤ smallPrimeEulerDensity (2 * y) :=
    smallPrimeEulerDensity_nonneg _
  calc
    smallPrimeEulerDensity (2 * y) *
          ((((1 / (8 * Real.log (y : ℝ))) ^ r) /
              (r.factorial : ℝ)) *
            (∑ a ∈ A,
              ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ))) ≤
        smallPrimeEulerDensity (2 * y) *
          (∑ c ∈ smallOuterModuli A
              (fun a ↦ isolatedPrimeSubsets y a r), 1 / (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass heuler
    _ = smallPrimeEulerDensity (2 * y) *
          (∑ c ∈ isolatedExactModuli y r A, 1 / (c : ℝ)) := by
      simp only [isolatedExactModuli, isolatedPrimeSubsets,
        isolatedOuterPrimeSets]
    _ ≤ epsilonR r y (2 * y) := hdensity

end Erdos446
