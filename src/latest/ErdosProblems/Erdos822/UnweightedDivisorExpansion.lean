/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.UnweightedGcdReduction
import ErdosProblems.Erdos822.AnchorCommonDivisorMass

/-!
# Divisor expansion of the unweighted supported gcd scale

Once the determinant singular factor has been removed, the remaining gcd is
expanded with `sum_totient`.  This file also gives the exact fixed-modulus,
fixed-anchor expression to which the quadratic residue-class estimate applies.
-/

namespace Erdos822

open scoped BigOperators

/-- The contribution of one divisor of the shifted-coefficient gcd. -/
noncomputable def commonDivisorScaleTerm (N m m' h : ℕ) : ℝ :=
  ((N ^ 60 : ℕ) : ℝ) * (Nat.totient h : ℝ) /
    ((m * m' : ℕ) : ℝ)

/-- The finite divisor expansion of `supportedGcdScale`. -/
noncomputable def supportedGcdDivisorExpansion (N m m' : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty then
    ∑ h ∈ (shiftedCoefficientGcd m m').divisors,
      commonDivisorScaleTerm N m m' h
  else 0

theorem commonDivisorScaleTerm_nonneg (N m m' h : ℕ) :
    0 ≤ commonDivisorScaleTerm N m m' h := by
  unfold commonDivisorScaleTerm
  positivity

theorem supportedGcdDivisorExpansion_nonneg (N m m' : ℕ) :
    0 ≤ supportedGcdDivisorExpansion N m m' := by
  unfold supportedGcdDivisorExpansion
  split_ifs
  · exact Finset.sum_nonneg fun h hh =>
      commonDivisorScaleTerm_nonneg N m m' h
  · exact le_rfl

/-- Exact divisor expansion, with no positivity hypothesis on the gcd needed. -/
theorem supportedGcdScale_eq_divisorExpansion (N m m' : ℕ) :
    supportedGcdScale N m m' = supportedGcdDivisorExpansion N m m' := by
  unfold supportedGcdScale supportedGcdDivisorExpansion
  by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
  · rw [if_pos hne, if_pos hne]
    let g := shiftedCoefficientGcd m m'
    let D : ℝ := ((m * m' : ℕ) : ℝ)
    have hsumNat : ∑ h ∈ g.divisors, Nat.totient h = g := Nat.sum_totient g
    have hsumReal :
        ∑ h ∈ g.divisors, (Nat.totient h : ℝ) = (g : ℝ) := by
      exact_mod_cast hsumNat
    change ((N ^ 60 * g : ℕ) : ℝ) / D =
      ∑ h ∈ g.divisors,
        (((N ^ 60 : ℕ) : ℝ) * (Nat.totient h : ℝ) / D)
    push_cast
    rw [← hsumReal, Finset.mul_sum, Finset.sum_div]
  · rw [if_neg hne, if_neg hne]

/-- Summed exact divisor expansion on an off-diagonal finite family. -/
theorem sum_supportedGcdScale_eq_sum_divisorExpansion
    (B : Finset ℕ) (N : ℕ) :
    (∑ m ∈ B, ∑ m' ∈ B.erase m, supportedGcdScale N m m') =
      ∑ m ∈ B, ∑ m' ∈ B.erase m,
        supportedGcdDivisorExpansion N m m' := by
  simp_rw [supportedGcdScale_eq_divisorExpansion]

/-- For one anchor and one modulus, the divisor contribution factors as a
constant times the reciprocal mass of its supported common-divisor fiber. -/
theorem sum_fixedCommonDivisorScaleTerm_eq
    (B : Finset ℕ) (N m' h : ℕ) :
    (∑ m ∈ B,
        if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
            h ∣ shiftedCoefficientGcd m m' then
          commonDivisorScaleTerm N m m' h
        else 0) =
      (((N ^ 60 : ℕ) : ℝ) * (Nat.totient h : ℝ) / (m' : ℝ)) *
        ∑ m ∈ B,
          if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
              h ∣ shiftedCoefficientGcd m m' then
            (1 : ℝ) / m
          else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hcond :
      (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
        h ∣ shiftedCoefficientGcd m m'
  · rw [if_pos hcond, if_pos hcond]
    unfold commonDivisorScaleTerm
    push_cast
    ring
  · rw [if_neg hcond, if_neg hcond, mul_zero]

/-- The already-proved rough quadratic class estimate, now stated directly
for the fixed-divisor contribution to the unweighted gcd scale. -/
theorem sum_fixedCommonDivisorScaleTerm_le_roughPairMass
    {B : Finset ℕ} {N y m' h : ℕ}
    (hN : 2 ≤ N) (hyN : y < N ^ 21)
    (hB : B ⊆ squarefreeLargeGcdFreeOddCofactors N y)
    (hm'B : m' ∈ B) :
    (∑ m ∈ B,
        if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
            h ∣ shiftedCoefficientGcd m m' then
          commonDivisorScaleTerm N m m' h
        else 0) ≤
      (((N ^ 60 : ℕ) : ℝ) * (Nat.totient h : ℝ) / (m' : ℝ)) *
        ((∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
          roughQuadraticPairMassBound N y h) := by
  rw [sum_fixedCommonDivisorScaleTerm_eq]
  exact mul_le_mul_of_nonneg_left
    (sum_inv_supported_commonDivisor_le_roughPairMass
      hN rfl hyN hB hm'B)
    (by positivity)

end Erdos822
