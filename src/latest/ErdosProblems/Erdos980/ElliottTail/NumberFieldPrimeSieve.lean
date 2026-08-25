/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos387.FiniteBetaSieveBridge
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# A finite upper sieve for principal ideals in a number field

Mathlib's `BoundingSieve` is formulated for natural numbers.  This file gives
an exact, lossless adapter for a finite family of chosen number-field
generators.  Each sieving prime ideal is assigned a distinct ordinary prime
label.  A generator is represented by the squarefree product of precisely
the labels of the prime ideals dividing its principal ideal.  Equal codes are
allowed: their weights are added in the corresponding fibre.

Consequently divisibility of a code by a squarefree divisor `d` is literally
simultaneous divisibility of the principal ideal by the prime ideals indexed
by `d.primeFactors`.  The Rosser upper-bound theorem can therefore be applied
with an explicit remainder estimate for those ideal-divisibility fibres; no
prime-ideal distribution assertion is built into this file.
-/

open scoped BigOperators NumberField

noncomputable section

namespace Erdos980.ElliottTail.NumberFieldPrimeSieve

open NumberField

/-- Finite chosen generators and the labelled prime ideals used to sieve
their principal ideals.  `principalNorm_le` records the bounded-norm range
from which the chosen (for example ray-primary) generators came. -/
structure Data (K A : Type*) [Field K] [NumberField K] where
  candidates : Finset A
  generator : A → NumberField.RingOfIntegers K
  normBound : ℕ
  principalNorm_le : ∀ a ∈ candidates,
    Ideal.absNorm (Ideal.span
      ({generator a} : Set (NumberField.RingOfIntegers K))) ≤ normBound
  weight : A → ℝ
  weight_nonneg : ∀ a ∈ candidates, 0 ≤ weight a
  primeLabels : Finset ℕ
  label_prime : ∀ p ∈ primeLabels, p.Prime
  primeIdeal : ℕ → Ideal (NumberField.RingOfIntegers K)
  primeIdeal_isPrime : ∀ p ∈ primeLabels, (primeIdeal p).IsPrime
  primeIdeal_injOn : Set.InjOn primeIdeal (primeLabels : Set ℕ)
  totalMass : ℝ
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_label : ∀ p, p.Prime → p ∣ primeLabels.prod id → 0 < nu p
  nu_lt_one_of_label : ∀ p, p.Prime → p ∣ primeLabels.prod id → nu p < 1

variable {K A : Type*} [Field K] [NumberField K]

/-- A selected prime ideal divides the principal ideal of a chosen
generator.  In a Dedekind domain this is equivalently membership of the
generator in the prime ideal, by `Ideal.dvd_span_singleton`. -/
def IdealDividesGenerator (D : Data K A) (p : ℕ) (a : A) : Prop :=
  D.primeIdeal p ∣ Ideal.span
    ({D.generator a} : Set (NumberField.RingOfIntegers K))

theorem idealDividesGenerator_iff_mem (D : Data K A) (p : ℕ) (a : A) :
    IdealDividesGenerator D p a ↔ D.generator a ∈ D.primeIdeal p := by
  exact Ideal.dvd_span_singleton

/-- Squarefree natural code of the prime ideals dividing a chosen principal
ideal. -/
def generatorCode (D : Data K A) (a : A) : ℕ := by
  classical
  exact ∏ p ∈ D.primeLabels.filter fun p ↦ IdealDividesGenerator D p a, p

/-- All natural codes occurring in the finite generator family. -/
def codeSupport [DecidableEq A] (D : Data K A) : Finset ℕ :=
  D.candidates.image (generatorCode D)

/-- The aggregate weight of all chosen generators with a prescribed code.
This retains multiplicity when several generators have the same local
prime-ideal divisibility pattern. -/
def codeWeight [DecidableEq A] (D : Data K A) (n : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ D.candidates.filter fun a ↦ generatorCode D a = n, D.weight a

/-- Literal weighted mass of the generators whose principal ideal is
divisible by every prime ideal selected by `d.primeFactors`. -/
def idealDivisorMass [DecidableEq A] (D : Data K A) (d : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ D.candidates,
    if ∀ p ∈ d.primeFactors, IdealDividesGenerator D p a
    then D.weight a else 0

/-- Literal weighted mass after removing every generator divisible by one
of the selected prime ideals. -/
def idealSiftedMass [DecidableEq A] (D : Data K A) : ℝ := by
  classical
  exact ∑ a ∈ D.candidates,
    if ∀ p ∈ D.primeLabels, ¬ IdealDividesGenerator D p a
    then D.weight a else 0

theorem primeLabels_product_squarefree (D : Data K A) :
    Squarefree (D.primeLabels.prod id) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (D.label_prime p hp) (D.label_prime q hq)).mpr hpq
  · intro p hp
    exact (D.label_prime p hp).squarefree

/-- A prime label divides the code of a generator exactly when the
corresponding prime ideal divides its principal ideal. -/
theorem label_dvd_generatorCode_iff [DecidableEq A]
    (D : Data K A) {p : ℕ} (hp : p ∈ D.primeLabels) (a : A) :
    p ∣ generatorCode D a ↔ IdealDividesGenerator D p a := by
  classical
  have hpPrime := D.label_prime p hp
  rw [generatorCode, Erdos387.prime_dvd_finset_prod_iff hpPrime]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hq' := Finset.mem_filter.mp hq
    have hpqeq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrime (D.label_prime q hq'.1)).mp hpq
    simpa [hpqeq] using hq'.2
  · intro h
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, dvd_rfl⟩

/-- Every prime factor of a divisor of the label product is itself one of
the selected labels. -/
theorem mem_primeLabels_of_mem_primeFactors_of_dvd
    (D : Data K A) {d p : ℕ} (hd : d ∣ D.primeLabels.prod id)
    (hp : p ∈ d.primeFactors) : p ∈ D.primeLabels := by
  classical
  have hprod0 : D.primeLabels.prod id ≠ 0 :=
    (primeLabels_product_squarefree D).ne_zero
  have hsub := Nat.primeFactors_mono hd hprod0 hp
  have heq : (D.primeLabels.prod id).primeFactors = D.primeLabels :=
    Nat.primeFactors_prod D.label_prime
  rw [heq] at hsub
  exact hsub

/-- Divisibility by a squarefree divisor of the label product is exactly
simultaneous divisibility by the corresponding prime ideals. -/
theorem divisor_dvd_generatorCode_iff [DecidableEq A]
    (D : Data K A) {d : ℕ} (hd : d ∣ D.primeLabels.prod id) (a : A) :
    d ∣ generatorCode D a ↔
      ∀ p ∈ d.primeFactors, IdealDividesGenerator D p a := by
  classical
  have hdsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (primeLabels_product_squarefree D)
  rw [Erdos387.squarefree_dvd_iff_primeFactors_dvd hdsq]
  constructor
  · intro h p hp
    exact (label_dvd_generatorCode_iff D
      (mem_primeLabels_of_mem_primeFactors_of_dvd D hd hp) a).mp (h p hp)
  · intro h p hp
    exact (label_dvd_generatorCode_iff D
      (mem_primeLabels_of_mem_primeFactors_of_dvd D hd hp) a).mpr (h p hp)

/-- Coprimality of a code to the full label product means that none of the
selected prime ideals divides the principal ideal. -/
theorem coprime_generatorCode_iff [DecidableEq A]
    (D : Data K A) (a : A) :
    Nat.Coprime (D.primeLabels.prod id) (generatorCode D a) ↔
      ∀ p ∈ D.primeLabels, ¬ IdealDividesGenerator D p a := by
  classical
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    have hnot : ¬ p ∣ generatorCode D a :=
      (D.label_prime p hp).coprime_iff_not_dvd.mp (h p hp)
    exact fun hideal ↦
      hnot ((label_dvd_generatorCode_iff D hp a).mpr hideal)
  · intro h p hp
    exact (D.label_prime p hp).coprime_iff_not_dvd.mpr
      ((label_dvd_generatorCode_iff D hp a).not.mpr (h p hp))

/-! ## The natural-number `BoundingSieve` adapter -/

/-- Reindexing a weighted finite generator family by its code, while
aggregating equal-code fibres, preserves every indicator-weighted sum. -/
theorem sum_codeWeight_indicator [DecidableEq A]
    (D : Data K A) (pred : ℕ → Prop) [DecidablePred pred] :
    (∑ n ∈ codeSupport D, if pred n then codeWeight D n else 0) =
      ∑ a ∈ D.candidates,
        if pred (generatorCode D a) then D.weight a else 0 := by
  classical
  let f : A → ℕ := generatorCode D
  let G : A → ℝ := fun a ↦ if pred (f a) then D.weight a else 0
  have hmaps : ∀ a ∈ D.candidates, f a ∈ D.candidates.image f := by
    intro a ha
    exact Finset.mem_image_of_mem f ha
  calc
    (∑ n ∈ codeSupport D, if pred n then codeWeight D n else 0) =
        ∑ n ∈ D.candidates.image f,
          ∑ a ∈ D.candidates.filter (fun a ↦ f a = n), G a := by
      apply Finset.sum_congr
      · rfl
      · intro n hn
        by_cases hpred : pred n
        · rw [if_pos hpred]
          unfold codeWeight
          apply Finset.sum_congr rfl
          intro a ha
          have hfa : f a = n := (Finset.mem_filter.mp ha).2
          simp only [G, hfa, if_pos hpred]
        · rw [if_neg hpred]
          symm
          apply Finset.sum_eq_zero
          intro a ha
          have hfa : f a = n := (Finset.mem_filter.mp ha).2
          simp only [G, hfa, if_neg hpred]
    _ = ∑ a ∈ D.candidates, G a :=
      Finset.sum_fiberwise_of_maps_to hmaps G
    _ = ∑ a ∈ D.candidates,
        if pred (generatorCode D a) then D.weight a else 0 := by
      rfl

/-- The ordinary `BoundingSieve` obtained by squarefree natural coding of
prime-ideal divisibility. -/
def boundingSieve [DecidableEq A] (D : Data K A) : BoundingSieve := by
  classical
  exact
    { support := codeSupport D
      prodPrimes := D.primeLabels.prod id
      prodPrimes_squarefree := primeLabels_product_squarefree D
      weights := codeWeight D
      weights_nonneg := by
        intro n
        unfold codeWeight
        exact Finset.sum_nonneg fun a ha ↦
          D.weight_nonneg a (Finset.mem_filter.mp ha).1
      totalMass := D.totalMass
      nu := D.nu
      nu_mult := D.nu_mult
      nu_pos_of_prime := D.nu_pos_of_label
      nu_lt_one_of_prime := D.nu_lt_one_of_label }

@[simp] theorem boundingSieve_prodPrimes [DecidableEq A] (D : Data K A) :
    (boundingSieve D).prodPrimes = D.primeLabels.prod id := rfl

@[simp] theorem boundingSieve_totalMass [DecidableEq A] (D : Data K A) :
    (boundingSieve D).totalMass = D.totalMass := rfl

@[simp] theorem boundingSieve_nu [DecidableEq A] (D : Data K A) :
    (boundingSieve D).nu = D.nu := rfl

/-- The abstract multiple sum is the literal simultaneous prime-ideal
divisibility mass. -/
theorem boundingSieve_multSum [DecidableEq A]
    (D : Data K A) {d : ℕ} (hd : d ∣ D.primeLabels.prod id) :
    (boundingSieve D).multSum d = idealDivisorMass D d := by
  classical
  rw [BoundingSieve.multSum]
  change (∑ n ∈ codeSupport D,
      if d ∣ n then codeWeight D n else 0) = idealDivisorMass D d
  rw [sum_codeWeight_indicator]
  unfold idealDivisorMass
  apply Finset.sum_congr rfl
  intro a ha
  have hiff := divisor_dvd_generatorCode_iff D hd a
  by_cases hdiv : d ∣ generatorCode D a
  · rw [if_pos hdiv, if_pos (hiff.mp hdiv)]
  · rw [if_neg hdiv, if_neg (fun h ↦ hdiv (hiff.mpr h))]

/-- The abstract sifted sum is the literal mass of principal ideals avoiding
all selected prime-ideal divisors. -/
theorem boundingSieve_siftedSum [DecidableEq A] (D : Data K A) :
    (boundingSieve D).siftedSum = idealSiftedMass D := by
  classical
  rw [BoundingSieve.siftedSum]
  change (∑ n ∈ codeSupport D,
      if Nat.Coprime (D.primeLabels.prod id) n
      then codeWeight D n else 0) = idealSiftedMass D
  rw [sum_codeWeight_indicator]
  unfold idealSiftedMass
  apply Finset.sum_congr rfl
  intro a ha
  have hiff := coprime_generatorCode_iff D a
  by_cases hcop : Nat.Coprime (D.primeLabels.prod id) (generatorCode D a)
  · rw [if_pos hcop, if_pos (hiff.mp hcop)]
  · rw [if_neg hcop, if_neg (fun h ↦ hcop (hiff.mpr h))]

/-- Exact identity for the remainder consumed by the finite beta sieve. -/
theorem boundingSieve_rem_eq [DecidableEq A]
    (D : Data K A) {d : ℕ} (hd : d ∣ D.primeLabels.prod id) :
    (boundingSieve D).rem d =
      idealDivisorMass D d - D.nu d * D.totalMass := by
  rw [BoundingSieve.rem, boundingSieve_multSum D hd]
  rfl

/-- The explicit arithmetic input required by the Rosser specialization.
It is deliberately stated solely in terms of genuine prime ideals dividing
the chosen principal ideals. -/
def HasIdealRemainderBound [DecidableEq A]
    (D : Data K A) (C : ℝ) (k : ℕ) : Prop :=
  ∀ d : ℕ, d ∣ D.primeLabels.prod id →
    |idealDivisorMass D d - D.nu d * D.totalMass| ≤
      C * (k : ℝ) ^ d.primeFactors.card

/-- The selected natural-prime labels in the increasing order required by
the finite Rosser-chain implementation. -/
def ascendingPrimeLabels (D : Data K A) : List ℕ :=
  D.primeLabels.sort (· ≤ ·)

theorem ascendingPrimeLabels_prod (D : Data K A) :
    (ascendingPrimeLabels D).prod = D.primeLabels.prod id := by
  classical
  unfold ascendingPrimeLabels
  symm
  simpa using List.prod_toFinset id
    (Finset.sort_nodup D.primeLabels (· ≤ ·))

theorem ascendingPrimeLabels_pairwise (D : Data K A) :
    (ascendingPrimeLabels D).Pairwise (· ≤ ·) := by
  exact Finset.pairwise_sort D.primeLabels (· ≤ ·)

theorem ascendingPrimeLabels_nodup (D : Data K A) :
    (ascendingPrimeLabels D).Nodup := by
  exact Finset.sort_nodup D.primeLabels (· ≤ ·)

theorem ascendingPrimeLabels_prime (D : Data K A) :
    ∀ p ∈ ascendingPrimeLabels D, p.Prime := by
  intro p hp
  exact D.label_prime p ((Finset.mem_sort (· ≤ ·)).mp hp)

open Erdos851.FiniteCombinatorialSieve
open Erdos387.FiniteBetaSieveBridge

/-- A completely unconditional Rosser upper bound for a finite bounded family
of canonical number-field generators.  Its sole arithmetic hypothesis is
`HasIdealRemainderBound`, the displayed simultaneous prime-ideal
divisibility estimate. -/
theorem idealSiftedMass_le_rosserUpperMain_add_levelEuler
    [DecidableEq A] (D : Data K A) (P : List ℕ)
    (C : ℝ) (k β level : ℕ)
    (hprod : P.prod = D.primeLabels.prod id)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hβ : 1 ≤ β) (hlevel : 1 ≤ level)
    (hrem : HasIdealRemainderBound D C k) (hC : 0 ≤ C) :
    idealSiftedMass D ≤
      D.totalMass *
          upperMainTerm (rosserStoppingPredicate β level) (fun p ↦ D.nu p) P +
        C * level * (P.map fun p ↦ 1 + (k : ℝ) / p).prod := by
  have hrem' : ∀ d : ℕ, d ∣ (boundingSieve D).prodPrimes →
      |(boundingSieve D).rem d| ≤
        C * (k : ℝ) ^ d.primeFactors.card := by
    intro d hd
    rw [boundingSieve_rem_eq D hd]
    exact hrem d hd
  have hsieve :=
    boundingSieve_siftedSum_le_rosserUpperMain_add_levelEuler
      (boundingSieve D) P C k β level hprod hsort hnodup hprime
        hβ hlevel hrem' hC
  rw [boundingSieve_siftedSum] at hsieve
  exact hsieve

/-- The self-contained sorted-label form of the number-field Rosser
specialization.  The hypothesis shown here is the exact remaining geometric
or prime-ideal fibre estimate: there are no list-ordering or natural-code
obligations left for a caller. -/
theorem idealSiftedMass_le_sortedRosserUpperMain_add_levelEuler
    [DecidableEq A] (D : Data K A) (C : ℝ) (k β level : ℕ)
    (hβ : 1 ≤ β) (hlevel : 1 ≤ level)
    (hrem : ∀ d : ℕ, d ∣ D.primeLabels.prod id →
      |idealDivisorMass D d - D.nu d * D.totalMass| ≤
        C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    idealSiftedMass D ≤
      D.totalMass *
          upperMainTerm (rosserStoppingPredicate β level)
            (fun p ↦ D.nu p) (ascendingPrimeLabels D) +
        C * level *
          ((ascendingPrimeLabels D).map fun p ↦ 1 + (k : ℝ) / p).prod := by
  apply idealSiftedMass_le_rosserUpperMain_add_levelEuler
    D (ascendingPrimeLabels D) C k β level
  · exact ascendingPrimeLabels_prod D
  · exact ascendingPrimeLabels_pairwise D
  · exact ascendingPrimeLabels_nodup D
  · exact ascendingPrimeLabels_prime D
  · exact hβ
  · exact hlevel
  · exact hrem
  · exact hC

end Erdos980.ElliottTail.NumberFieldPrimeSieve
