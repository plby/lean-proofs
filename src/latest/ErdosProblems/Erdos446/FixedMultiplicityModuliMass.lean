/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisorMass

/-!
# Erdős Problem 446: reciprocal mass of fixed-multiplicity moduli

The prescribed-multiplicity construction starts with a small squarefree
factor `a` and adjoins a finite set `P` of separated large primes.  This file
packages the exact reindexing of the reciprocal mass of the resulting moduli
`a * ∏ p ∈ P, p`.  The only non-formal input needed for equality is the
uniqueness of this factorization on the chosen finite family.

This is the algebraic bridge between the `r`th isolated-divisor moment and
the exact-valuation CRT cells.  In particular, no multiplicity or constant is
lost when passing from weighted prime choices to distinct moduli.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The finite dependent family of a small factor together with one of its
admissible outer-prime sets. -/
def smallOuterPairs (A : Finset ℕ) (F : ℕ → Finset (Finset ℕ)) :
    Finset ((a : ℕ) × Finset ℕ) :=
  A.sigma F

/-- The modulus determined by a small factor and its outer-prime set. -/
def smallOuterModulus (x : (a : ℕ) × Finset ℕ) : ℕ :=
  x.1 * ∏ p ∈ x.2, p

/-- The finite family of moduli produced by the small/outer factorization. -/
def smallOuterModuli (A : Finset ℕ) (F : ℕ → Finset (Finset ℕ)) :
    Finset ℕ :=
  (smallOuterPairs A F).image smallOuterModulus

theorem mem_smallOuterPairs {A : Finset ℕ} {F : ℕ → Finset (Finset ℕ)}
    {x : (a : ℕ) × Finset ℕ} :
    x ∈ smallOuterPairs A F ↔ x.1 ∈ A ∧ x.2 ∈ F x.1 := by
  simp [smallOuterPairs]

theorem mem_smallOuterModuli {A : Finset ℕ} {F : ℕ → Finset (Finset ℕ)}
    {c : ℕ} :
    c ∈ smallOuterModuli A F ↔
      ∃ a ∈ A, ∃ P ∈ F a, a * ∏ p ∈ P, p = c := by
  simp only [smallOuterModuli, Finset.mem_image, mem_smallOuterPairs]
  constructor
  · rintro ⟨x, ⟨hxa, hxF⟩, rfl⟩
    exact ⟨x.1, hxa, x.2, hxF, rfl⟩
  · rintro ⟨a, ha, P, hP, rfl⟩
    exact ⟨⟨a, P⟩, ⟨ha, hP⟩, rfl⟩

/-- Reciprocal of one constructed modulus, factored into the reciprocal of
the small part and the product of reciprocal outer primes. -/
theorem reciprocal_smallOuterModulus
    (x : (a : ℕ) × Finset ℕ) :
    1 / (smallOuterModulus x : ℝ) =
      (1 / (x.1 : ℝ)) * ∏ p ∈ x.2, 1 / (p : ℝ) := by
  rw [smallOuterModulus, Nat.cast_mul, Nat.cast_prod]
  simp only [one_div]
  rw [Finset.prod_inv_distrib]
  ring

/-- Uniqueness of the small/outer factorization when a cutoff separates all
prime factors of the small part from all outer primes.  This discharges the
injectivity hypothesis in the reciprocal-mass reindexing for Ford's actual
families. -/
theorem smallOuterModulus_injOn_of_prime_separation
    (L : ℕ) (A : Finset ℕ) (F : ℕ → Finset (Finset ℕ))
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (hPprime : ∀ a ∈ A, ∀ P ∈ F a, ∀ p ∈ P, p.Prime)
    (hPlarge : ∀ a ∈ A, ∀ P ∈ F a, ∀ p ∈ P, L < p) :
    Set.InjOn smallOuterModulus (smallOuterPairs A F) := by
  intro x hx x' hx' hmod
  obtain ⟨hxa, hxF⟩ := mem_smallOuterPairs.mp hx
  obtain ⟨hxa', hxF'⟩ := mem_smallOuterPairs.mp hx'
  have hprodX : 0 < ∏ p ∈ x.2, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hPprime x.1 hxa x.2 hxF p hp).pos
  have hprodX' : 0 < ∏ p ∈ x'.2, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hPprime x'.1 hxa' x'.2 hxF' p hp).pos
  have hpfX : (smallOuterModulus x).primeFactors =
      x.1.primeFactors ∪ x.2 := by
    rw [smallOuterModulus,
      Nat.primeFactors_mul (hApos x.1 hxa).ne' hprodX.ne',
      Nat.primeFactors_prod (hPprime x.1 hxa x.2 hxF)]
  have hpfX' : (smallOuterModulus x').primeFactors =
      x'.1.primeFactors ∪ x'.2 := by
    rw [smallOuterModulus,
      Nat.primeFactors_mul (hApos x'.1 hxa').ne' hprodX'.ne',
      Nat.primeFactors_prod (hPprime x'.1 hxa' x'.2 hxF')]
  have hunion : x.1.primeFactors ∪ x.2 =
      x'.1.primeFactors ∪ x'.2 := by
    rw [← hpfX, ← hpfX', hmod]
  have houter : x.2 = x'.2 := by
    ext p
    constructor
    · intro hp
      have hpRight : p ∈ x'.1.primeFactors ∪ x'.2 := by
        rw [← hunion]
        exact Finset.mem_union_right _ hp
      rcases Finset.mem_union.mp hpRight with hpSmall | hpOuter
      · have hpLe := hAcut x'.1 hxa' p hpSmall
        have hpGt := hPlarge x.1 hxa x.2 hxF p hp
        omega
      · exact hpOuter
    · intro hp
      have hpLeft : p ∈ x.1.primeFactors ∪ x.2 := by
        rw [hunion]
        exact Finset.mem_union_right _ hp
      rcases Finset.mem_union.mp hpLeft with hpSmall | hpOuter
      · have hpLe := hAcut x.1 hxa p hpSmall
        have hpGt := hPlarge x'.1 hxa' x'.2 hxF' p hp
        omega
      · exact hpOuter
  have hsmall : x.1.primeFactors = x'.1.primeFactors := by
    ext p
    constructor
    · intro hp
      have hpRight : p ∈ x'.1.primeFactors ∪ x'.2 := by
        rw [← hunion]
        exact Finset.mem_union_left _ hp
      rcases Finset.mem_union.mp hpRight with hpSmall | hpOuter
      · exact hpSmall
      · have hpLe := hAcut x.1 hxa p hp
        have hpGt := hPlarge x'.1 hxa' x'.2 hxF' p hpOuter
        omega
    · intro hp
      have hpLeft : p ∈ x.1.primeFactors ∪ x.2 := by
        rw [hunion]
        exact Finset.mem_union_left _ hp
      rcases Finset.mem_union.mp hpLeft with hpSmall | hpOuter
      · exact hpSmall
      · have hpLe := hAcut x'.1 hxa' p hp
        have hpGt := hPlarge x.1 hxa x.2 hxF p hpOuter
        omega
  have hsmallFactor : x.1 = x'.1 := by
    calc
      x.1 = ∏ p ∈ x.1.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree (hAsq x.1 hxa)).symm
      _ = ∏ p ∈ x'.1.primeFactors, p := by rw [hsmall]
      _ = x'.1 := Nat.prod_primeFactors_of_squarefree (hAsq x'.1 hxa')
  cases x with
  | mk a P =>
    cases x' with
    | mk a' P' =>
      dsimp at hsmallFactor houter ⊢
      subst a'
      subst P'
      rfl

/-- Exact reciprocal-mass reindexing.  Injectivity is required only on the
chosen family, not on all pairs of natural numbers and prime sets. -/
theorem sum_reciprocal_smallOuterModuli_eq
    (A : Finset ℕ) (F : ℕ → Finset (Finset ℕ))
    (hinj : Set.InjOn smallOuterModulus (smallOuterPairs A F)) :
    (∑ c ∈ smallOuterModuli A F, 1 / (c : ℝ)) =
      ∑ a ∈ A, (1 / (a : ℝ)) *
        ∑ P ∈ F a, ∏ p ∈ P, 1 / (p : ℝ) := by
  rw [smallOuterModuli, Finset.sum_image hinj]
  calc
    (∑ x ∈ smallOuterPairs A F, 1 / (smallOuterModulus x : ℝ)) =
        ∑ x ∈ smallOuterPairs A F,
          (1 / (x.1 : ℝ)) * ∏ p ∈ x.2, 1 / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact reciprocal_smallOuterModulus x
    _ = ∑ a ∈ A, ∑ P ∈ F a,
          (1 / (a : ℝ)) * ∏ p ∈ P, 1 / (p : ℝ) := by
      exact Finset.sum_sigma A F
        (fun x ↦ (1 / (x.1 : ℝ)) * ∏ p ∈ x.2, 1 / (p : ℝ))
    _ = ∑ a ∈ A, (1 / (a : ℝ)) *
          ∑ P ∈ F a, ∏ p ∈ P, 1 / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

/-- Pointwise lower bounds for the outer-prime selection mass sum without
loss after the moduli are deduplicated. -/
theorem sum_smallFactorMass_le_sum_reciprocal_smallOuterModuli
    (A : Finset ℕ) (F : ℕ → Finset (Finset ℕ)) (B : ℕ → ℝ)
    (hinj : Set.InjOn smallOuterModulus (smallOuterPairs A F))
    (hA : ∀ a ∈ A, 0 < a)
    (hB : ∀ a ∈ A,
      B a ≤ ∑ P ∈ F a, ∏ p ∈ P, 1 / (p : ℝ)) :
    (∑ a ∈ A, B a / (a : ℝ)) ≤
      ∑ c ∈ smallOuterModuli A F, 1 / (c : ℝ) := by
  rw [sum_reciprocal_smallOuterModuli_eq A F hinj]
  apply Finset.sum_le_sum
  intro a ha
  have haR : (0 : ℝ) < a := by exact_mod_cast hA a ha
  calc
    B a / (a : ℝ) = (1 / (a : ℝ)) * B a := by ring
    _ ≤ (1 / (a : ℝ)) *
        ∑ P ∈ F a, ∏ p ∈ P, 1 / (p : ℝ) :=
      mul_le_mul_of_nonneg_left (hB a ha) (by positivity)

/-- The form used after the isolated-divisor moment estimate: an outer-prime
selection mass bounded below by a constant times `I(a)^r` becomes the same
lower bound for the reciprocal mass of the exact-multiplicity moduli. -/
theorem isolatedPowerMass_le_sum_reciprocal_smallOuterModuli
    (A : Finset ℕ) (F : ℕ → Finset (Finset ℕ)) (r : ℕ) (c : ℝ)
    (hinj : Set.InjOn smallOuterModulus (smallOuterPairs A F))
    (hA : ∀ a ∈ A, 0 < a)
    (hselect : ∀ a ∈ A,
      c * (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r ≤
        ∑ P ∈ F a, ∏ p ∈ P, 1 / (p : ℝ)) :
    c * (∑ a ∈ A,
        (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r / (a : ℝ)) ≤
      ∑ m ∈ smallOuterModuli A F, 1 / (m : ℝ) := by
  calc
    c * (∑ a ∈ A,
        (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r / (a : ℝ)) =
      ∑ a ∈ A,
        (c * (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ ∑ m ∈ smallOuterModuli A F, 1 / (m : ℝ) :=
      sum_smallFactorMass_le_sum_reciprocal_smallOuterModuli
        A F (fun a ↦ c * (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r)
        hinj hA hselect

/-- Any pointwise arithmetic property of the constructed pairs descends to
the deduplicated modulus family. -/
theorem property_of_mem_smallOuterModuli
    {A : Finset ℕ} {F : ℕ → Finset (Finset ℕ)} {Q : ℕ → Prop}
    (hQ : ∀ a ∈ A, ∀ P ∈ F a, Q (a * ∏ p ∈ P, p)) :
    ∀ c ∈ smallOuterModuli A F, Q c := by
  intro c hc
  obtain ⟨a, ha, P, hP, rfl⟩ := mem_smallOuterModuli.mp hc
  exact hQ a ha P hP

end Erdos446
