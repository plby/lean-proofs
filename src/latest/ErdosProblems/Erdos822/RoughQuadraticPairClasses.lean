/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.RoughQuadraticPrimeClasses
import ErdosProblems.Erdos822.MiddlePrimeResidueClasses

/-!
# Both structured prime layers in rough quadratic classes

The corrected CRT argument constrains the middle and large structured prime
simultaneously.  This file packages the union of middle-prime classes and
the corresponding reciprocal bound, parallel to the already checked
large-prime class union.
-/

namespace Erdos822

open scoped BigOperators

/-- Middle-layer primes whose residue modulo h is one of the quadratic CRT
root classes. -/
noncomputable def quadraticMiddlePrimeClasses
    (N h u v : ℕ) : Finset ℕ :=
  (quadraticAssignmentResidues u v h).biUnion fun a =>
    middlePrimeResidueClass N h a

@[simp]
theorem mem_quadraticMiddlePrimeClasses_iff
    {N h u v r : ℕ} :
    r ∈ quadraticMiddlePrimeClasses N h u v ↔
      ∃ a ∈ quadraticAssignmentResidues u v h,
        r ∈ middlePrimeResidueClass N h a := by
  simp [quadraticMiddlePrimeClasses]

/-- A middle prime whose reduced residue is a quadratic assignment belongs
to the corresponding union of middle-prime classes. -/
theorem mem_quadraticMiddlePrimeClasses_of_mod_mem
    {N h u v r : ℕ}
    (hr : r ∈ middlePrimes N)
    (hroot : r % h ∈ quadraticAssignmentResidues u v h) :
    r ∈ quadraticMiddlePrimeClasses N h u v := by
  rw [mem_quadraticMiddlePrimeClasses_iff]
  refine ⟨r % h, hroot, ?_⟩
  rw [mem_middlePrimeResidueClass_iff]
  exact ⟨hr, by simp⟩

/-- The reciprocal mass of the middle quadratic union is at most its root
count times the elementary one-class estimate. -/
theorem sum_inv_quadraticMiddlePrimeClasses_le_card_mul
    {N h u v : ℕ} (hN : 2 ≤ N) (hh : 0 < h) :
    ∑ r ∈ quadraticMiddlePrimeClasses N h u v,
        (1 : ℝ) / r ≤
      ((quadraticAssignmentResidues u v h).card : ℝ) *
        (((1 : ℝ) / h + (1 : ℝ) / (N ^ 4 : ℕ)) *
          (harmonic N : ℝ)) := by
  classical
  let E : ℝ :=
    ((1 : ℝ) / h + (1 : ℝ) / (N ^ 4 : ℕ)) *
      (harmonic N : ℝ)
  have hE : 0 ≤ E := by
    dsimp [E]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity
  calc
    (∑ r ∈ quadraticMiddlePrimeClasses N h u v,
        (1 : ℝ) / r) ≤
        ∑ a ∈ quadraticAssignmentResidues u v h,
          ∑ r ∈ middlePrimeResidueClass N h a,
            (1 : ℝ) / r := by
      unfold quadraticMiddlePrimeClasses
      apply sum_biUnion_le_sum
      intro a ha r hr
      positivity
    _ ≤ ∑ a ∈ quadraticAssignmentResidues u v h, E := by
      apply Finset.sum_le_sum
      intro a ha
      dsimp [E]
      exact sum_inv_middlePrimeResidueClass_le_harmonic_of_pos hN hh
    _ = ((quadraticAssignmentResidues u v h).card : ℝ) * E := by
      rw [Finset.sum_const]
      simp
    _ = ((quadraticAssignmentResidues u v h).card : ℝ) *
        (((1 : ℝ) / h + (1 : ℝ) / (N ^ 4 : ℕ)) *
          (harmonic N : ℝ)) := by rfl

/-- Honest rough-modulus version of the middle quadratic-class bound. -/
theorem sum_inv_quadraticMiddlePrimeClasses_roughPart_le_two_pow
    {N y h m m' u v : ℕ}
    (hN : 2 ≤ N)
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    ∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
        (1 : ℝ) / r ≤
      ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) *
        (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
          (harmonic N : ℝ)) := by
  have hbase :=
    sum_inv_quadraticMiddlePrimeClasses_le_card_mul
      (N := N) (h := roughPart h y) (u := u) (v := v)
      hN (Nat.pos_of_ne_zero (roughPart_ne_zero h y))
  have hcard :
      ((quadraticAssignmentResidues u v (roughPart h y)).card : ℝ) ≤
        ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) := by
    exact_mod_cast quadraticAssignments_roughPart_card_le_two_pow hm hh
  have hfactor :
      0 ≤ (((1 : ℝ) / roughPart h y +
          (1 : ℝ) / (N ^ 4 : ℕ)) * (harmonic N : ℝ)) := by
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_right hcard hfactor)

/-- The middle prime of a supported corrected-B4 cofactor lies in the
honest rough quadratic class union. -/
theorem middlePrime_mem_quadraticClasses_of_rough_commonDivisor
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
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂)
    (hr₁mem : r₁ ∈ middlePrimes N) :
    r₁ ∈ quadraticMiddlePrimeClasses N (roughPart h y)
      (r₂ * q₂) (r₂ + q₂) := by
  have hroot :=
    (supported_pair_mod_mem_quadraticAssignments_of_roughPart
      hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge'
      hne₁ hne₂ hh₁ hh₂ hmul₁ hmul₂
      hr₁ hq₁ hr₂ hq₂ hr₁k hq₁kr₁ hr₂k hq₂kr₂).1
  exact mem_quadraticMiddlePrimeClasses_of_mod_mem hr₁mem hroot

/-- The reciprocal mass of the Cartesian product of the two rough
quadratic class unions has two independent inverse-modulus savings. -/
theorem sum_inv_quadraticPairClasses_roughPart_le_two_pow_sq
    {N y h m m' u v : ℕ}
    (hN : 2 ≤ N)
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    ∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
      ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
        (1 : ℝ) / (r * q) ≤
      ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) ^ 2 *
        ((((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
            (harmonic N : ℝ)) *
          (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ))) := by
  let R : ℝ :=
    ((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
      (harmonic N : ℝ)
  let Q : ℝ :=
    ((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
      (harmonic N : ℝ)
  let W : ℝ := ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ)
  have hR :
      ∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
          (1 : ℝ) / r ≤ W * R := by
    simpa [W, R] using
      sum_inv_quadraticMiddlePrimeClasses_roughPart_le_two_pow
        (N := N) (y := y) (h := h) (m := m) (m' := m')
        (u := u) (v := v) hN hm hh
  have hQ :
      ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
          (1 : ℝ) / q ≤ W * Q := by
    simpa [W, Q] using
      sum_inv_quadraticLargePrimeClasses_roughPart_le_two_pow
        (N := N) (y := y) (h := h) (m := m) (m' := m')
        (u := u) (v := v) hN hm hh
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity
  have hW0 : 0 ≤ W := by
    dsimp [W]
    positivity
  calc
    (∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
        ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
          (1 : ℝ) / (r * q)) =
        (∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
            (1 : ℝ) / r) *
          (∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
            (1 : ℝ) / q) := by
      calc
        (∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
            ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
              (1 : ℝ) / (r * q)) =
            ∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
              ((1 : ℝ) / r) *
                ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
                  (1 : ℝ) / q := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          push_cast
          ring
        _ = (∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y) u v,
              (1 : ℝ) / r) *
            (∑ q ∈ quadraticLargePrimeClasses N (roughPart h y) u v y,
              (1 : ℝ) / q) := by
          rw [Finset.sum_mul]
    _ ≤ (W * R) * (W * Q) := by
      exact mul_le_mul hR hQ
        (Finset.sum_nonneg fun q hq => by positivity)
        (mul_nonneg hW0 hR0)
    _ = W ^ 2 * (R * Q) := by ring
    _ = ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) ^ 2 *
        ((((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
            (harmonic N : ℝ)) *
          (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ))) := by rfl

end Erdos822
