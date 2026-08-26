/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.GrowingCommonDivisorResidues
import ErdosProblems.Erdos822.SquarefreeQuadraticCRT

/-!
# The corrected medium-range quadratic classes

On the B4 layer with repeated large shifted prime factors removed, a common
divisor supported above the cutoff is squarefree.  The two prime variables
therefore lie in the explicit CRT family of at most two choices per prime
factor.
-/

namespace Erdos822

/-- The common divisor appearing in a corrected B4 collision is squarefree
as soon as all of its prime factors are above the cutoff. -/
theorem commonDivisor_squarefree_of_squarefreeLargeGcdFree
    {N y h m m' : ℕ}
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Squarefree h := by
  apply squarefree_of_dvd_shiftedTotient_of_squarefreeLargeGcdFree hm
  · exact dvd_trans hh (by
      unfold shiftedCoefficientGcd
      exact Nat.gcd_dvd_left _ _)
  · exact hprimeLarge

/-- Both new prime variables of a supported corrected-B4 pair lie in the
same explicit CRT family of quadratic root classes modulo h. -/
theorem supported_pair_mod_mem_quadraticAssignments_of_squarefreeLargeGcdFree
    {N y x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
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
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p)
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂) :
    r₁ % h ∈ quadraticAssignmentResidues (r₂ * q₂) (r₂ + q₂) h ∧
      q₁ % h ∈ quadraticAssignmentResidues (r₂ * q₂) (r₂ + q₂) h := by
  have hm₁B4 : m₁ ∈ largeGcdFreeOddCofactors N y :=
    squarefreeLargeGcdFreeOddCofactors_subset_largeGcdFree N y hm₁
  have hm₂B4 : m₂ ∈ largeGcdFreeOddCofactors N y :=
    squarefreeLargeGcdFreeOddCofactors_subset_largeGcdFree N y hm₂
  have hroots :=
    supported_pair_roots_of_largeGcdFree_commonDivisor
      hm₁B4 hm₂B4 hm' hlarge₁ hlarge₂ hlarge'
      hne₁ hne₂ hh₁ hh₂ hprimeLarge hmul₁ hmul₂
      hr₁ hq₁ hr₂ hq₂ hr₁k hq₁kr₁ hr₂k hq₂kr₂
  have hsquare : Squarefree h :=
    commonDivisor_squarefree_of_squarefreeLargeGcdFree
      hm₁ hh₁ hprimeLarge
  constructor
  · exact (squarefree_quadratic_modEq_iff_mod_mem hsquare).mp hroots.1
  · exact (squarefree_quadratic_modEq_iff_mod_mem hsquare).mp hroots.2

/-- The explicit CRT family used above has at most one factor two for
each prime divisor of the squarefree common modulus. -/
theorem quadraticAssignments_card_le_two_pow_of_corrected_commonDivisor
    {N y h m m' u v : ℕ}
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    (quadraticAssignmentResidues u v h).card ≤
      2 ^ h.primeFactors.card := by
  exact quadraticAssignmentResidues_card_le_two_pow
    (commonDivisor_squarefree_of_squarefreeLargeGcdFree
      hm hh hprimeLarge)

end Erdos822
