/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CofactorRepresentation
import ErdosProblems.Erdos822.QuadraticPrimeClasses

/-!
# Quadratic large-prime classes for the rough common divisor

The honest common-divisor split is now threaded into the reciprocal
large-prime class estimate.  The theorem below is the summation-ready form:
the modulus is the rough part of an arbitrary common shifted divisor, so its
squarefreeness and large-prime support are consequences rather than
assumptions.
-/

namespace Erdos822

open scoped BigOperators

/-- Reciprocal mass in the quadratic large-prime classes attached to the
rough part of a common shifted divisor. -/
theorem sum_inv_quadraticLargePrimeClasses_roughPart_le_two_pow
    {N y h m m' u v : ℕ}
    (hN : 2 ≤ N)
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
        (1 : ℝ) / q ≤
      ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) *
        (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ)) := by
  apply sum_inv_quadraticLargePrimeClasses_le_two_pow
    hN (Nat.pos_of_ne_zero (roughPart_ne_zero h y)) hm
    (roughPart_dvd_shiftedCoefficientGcd hh)
  intro p hp hpdvd
  exact prime_dvd_roughPart_gt hp hpdvd

/-- For two supported corrected-B4 cofactors with the same small factor,
the first cofactor's large prime lies in the quadratic class union modulo
the honest rough part of any shared common divisor. -/
theorem largePrime_mem_quadraticClasses_of_rough_commonDivisor
    {N y x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hyN : y < N ^ 21)
    (hm₁ : m₁ ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hm₂ : m₂ ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂)
    (hq₁mem : q₁ ∈ largePrimes N) :
    q₁ ∈ quadraticLargePrimeClasses N (roughPart h y)
      (r₂ * q₂) (r₂ + q₂) y := by
  have hroot :=
    (supported_pair_mod_mem_quadraticAssignments_of_roughPart
      hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge'
      hne₁ hne₂ hh₁ hh₂ hmul₁ hmul₂
      hr₁ hq₁ hr₂ hq₂ hr₁k hq₁kr₁ hr₂k hq₂kr₂).2
  exact mem_quadraticLargePrimeClasses_of_mod_mem hyN hq₁mem hroot

end Erdos822
