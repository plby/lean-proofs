/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.TripleShiftedFormula

/-!
# The quadratic residue relation

Once `r*q` and `r+q` are fixed modulo a common divisor, each of `r,q` is a
root of the same monic quadratic congruence.  This is the purely algebraic
input to the odd-prime-power root count in the medium range.
-/

namespace Erdos822

/-- Product and sum residues put the first factor on the corresponding
monic quadratic congruence. -/
theorem square_add_product_modEq_mul_sum
    {h r q u v : ℕ}
    (hprod : r * q ≡ u [MOD h])
    (hsum : r + q ≡ v [MOD h]) :
    r ^ 2 + u ≡ v * r [MOD h] := by
  calc
    r ^ 2 + u ≡ r ^ 2 + r * q [MOD h] :=
      hprod.symm.add_left (r ^ 2)
    _ = (r + q) * r := by ring
    _ ≡ v * r [MOD h] := hsum.mul_right r

/-- The second factor satisfies the same quadratic congruence. -/
theorem square_add_product_modEq_mul_sum_right
    {h r q u v : ℕ}
    (hprod : r * q ≡ u [MOD h])
    (hsum : r + q ≡ v [MOD h]) :
    q ^ 2 + u ≡ v * q [MOD h] := by
  have hprod' : q * r ≡ u [MOD h] := by
    simpa [Nat.mul_comm] using hprod
  have hsum' : q + r ≡ v [MOD h] := by
    simpa [Nat.add_comm] using hsum
  exact square_add_product_modEq_mul_sum hprod' hsum'

/-- Relative to a reference pair `(r₀,q₀)`, every pair with the same sum
and product residues gives two roots of one fixed quadratic congruence. -/
theorem pair_roots_of_sum_product_modEq
    {h r q r₀ q₀ : ℕ}
    (hprod : r * q ≡ r₀ * q₀ [MOD h])
    (hsum : r + q ≡ r₀ + q₀ [MOD h]) :
    r ^ 2 + r₀ * q₀ ≡ (r₀ + q₀) * r [MOD h] ∧
      q ^ 2 + r₀ * q₀ ≡ (r₀ + q₀) * q [MOD h] := by
  exact ⟨square_add_product_modEq_mul_sum hprod hsum,
    square_add_product_modEq_mul_sum_right hprod hsum⟩

/-- For supported B4 cofactors with fixed `k,m',h`, both new prime
factors satisfy the reference quadratic congruence. -/
theorem supported_pair_roots_of_commonDivisor
    {N x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ coprimeTotientOddCofactors N)
    (hm₂ : m₂ ∈ coprimeTotientOddCofactors N)
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
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂) :
    r₁ ^ 2 + r₂ * q₂ ≡ (r₂ + q₂) * r₁ [MOD h] ∧
      q₁ ^ 2 + r₂ * q₂ ≡ (r₂ + q₂) * q₁ [MOD h] := by
  have hprod := cofactorProducts_modEq_of_supported_commonDivisor
    hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge' hne₁ hne₂
    hh₁ hh₂ hmul₁ hmul₂
  have hsum := cofactorSums_modEq_of_supported_commonDivisor
    hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge' hne₁ hne₂
    hh₁ hh₂ hmul₁ hmul₂ hr₁ hq₁ hr₂ hq₂
    hr₁k hq₁kr₁ hr₂k hq₂kr₂
  exact pair_roots_of_sum_product_modEq hprod hsum

end Erdos822
