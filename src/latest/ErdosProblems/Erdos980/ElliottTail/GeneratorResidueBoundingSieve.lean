/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.IdealGeneratorCongruenceCount
import ErdosProblems.Erdos387.FiniteBetaSieveBridge

/-!
# The bounding sieve attached to finitely many prime ideals

This file is the lossless adapter between a finite family of prime ideals
and Mathlib's natural-number `BoundingSieve`.  The prime ideals are assigned
distinct auxiliary ordinary-prime labels.  A generator is encoded by the
squarefree product of precisely the labels of the prime ideals containing
it.  The local density at a label `p` is exactly
`1 / Ideal.absNorm (primeIdeal p)`.

The construction is deliberately independent of the numerical sizes of the
auxiliary labels.  Their only purpose is to let the generic finite Rosser
sieve express simultaneous ideal divisibility by ordinary divisibility.
The analytic input supplied by the canonical-generator lattice count is a
bound for the resulting `BoundingSieve.rem`; no density is hidden in the
encoding.
-/

open scoped BigOperators NumberField NNReal nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.GeneratorResidueBoundingSieve

open NumberField Set Submodule Ideal
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone

/-- Finite generator data for the ideal-norm bounding sieve.  We record that
each selected prime ideal is nonzero because the zero prime of a number ring
has norm zero and is not a legitimate sieving prime. -/
structure Data (K A : Type*) [Field K] [NumberField K] where
  candidates : Finset A
  generator : A → NumberField.RingOfIntegers K
  weight : A → ℝ
  weight_nonneg : ∀ a ∈ candidates, 0 ≤ weight a
  primeLabels : Finset ℕ
  label_prime : ∀ p ∈ primeLabels, p.Prime
  primeIdeal : ℕ → Ideal (NumberField.RingOfIntegers K)
  primeIdeal_isPrime : ∀ p ∈ primeLabels, (primeIdeal p).IsPrime
  primeIdeal_ne_bot : ∀ p ∈ primeLabels, primeIdeal p ≠ ⊥
  primeIdeal_injOn : Set.InjOn primeIdeal (primeLabels : Set ℕ)
  /-- The main mass before any of the selected prime ideals are imposed. -/
  totalMass : ℝ

variable {K A : Type*} [Field K] [NumberField K]

/-- Local ideal density, extended multiplicatively from auxiliary primes. -/
def idealNormNu (D : Data K A) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p ↦
    (Ideal.absNorm (D.primeIdeal p) : ℝ)⁻¹

theorem idealNormNu_mult (D : Data K A) :
    (idealNormNu D).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem idealNormNu_apply {D : Data K A} {d : ℕ} (hd : d ≠ 0) :
    idealNormNu D d =
      ∏ p ∈ d.primeFactors,
        (Ideal.absNorm (D.primeIdeal p) : ℝ)⁻¹ := by
  rw [idealNormNu, ArithmeticFunction.prodPrimeFactors_apply hd]

theorem idealNormNu_prime {D : Data K A} {p : ℕ} (hp : p.Prime) :
    idealNormNu D p = (Ideal.absNorm (D.primeIdeal p) : ℝ)⁻¹ := by
  rw [idealNormNu_apply hp.ne_zero, hp.primeFactors]
  simp

/-- Every selected nonzero prime ideal has norm at least two. -/
theorem one_lt_absNorm_primeIdeal (D : Data K A) {p : ℕ}
    (hp : p ∈ D.primeLabels) :
    1 < Ideal.absNorm (D.primeIdeal p) := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  refine ⟨?_, ?_⟩
  · exact Ideal.absNorm_eq_zero_iff.not.mpr (D.primeIdeal_ne_bot p hp)
  · exact Ideal.absNorm_eq_one_iff.not.mpr
      (D.primeIdeal_isPrime p hp).ne_top

/-- The natural squarefree code retaining exactly the selected ideal
divisibility pattern of a generator. -/
def generatorCode (D : Data K A) (a : A) : ℕ := by
  classical
  exact ∏ p ∈ D.primeLabels.filter fun p ↦
    D.primeIdeal p ∣
      Ideal.span ({D.generator a} : Set (NumberField.RingOfIntegers K)), p

/-- Natural support of all generator codes. -/
def codeSupport [DecidableEq A] (D : Data K A) : Finset ℕ :=
  D.candidates.image (generatorCode D)

/-- Aggregate weight on one code; this preserves multiplicity when several
generators have the same selected ideal-divisibility pattern. -/
def codeWeight [DecidableEq A] (D : Data K A) (n : ℕ) : ℝ :=
  ∑ a ∈ D.candidates.filter fun a ↦ generatorCode D a = n, D.weight a

/-- Literal mass on which all prime ideals indexed by `d.primeFactors`
divide the generated principal ideal. -/
def idealDivisorMass [DecidableEq A] (D : Data K A) (d : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ D.candidates,
      if ∀ p ∈ d.primeFactors,
          D.primeIdeal p ∣
            Ideal.span ({D.generator a} : Set (NumberField.RingOfIntegers K))
      then D.weight a else 0

/-- Literal mass after excluding every selected prime ideal. -/
def idealSiftedMass [DecidableEq A] (D : Data K A) : ℝ := by
  classical
  exact ∑ a ∈ D.candidates,
      if ∀ p ∈ D.primeLabels,
          ¬ D.primeIdeal p ∣
            Ideal.span ({D.generator a} : Set (NumberField.RingOfIntegers K))
      then D.weight a else 0

theorem primeLabels_product_squarefree (D : Data K A) :
    Squarefree (D.primeLabels.prod id) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (D.label_prime p hp)
      (D.label_prime q hq)).mpr hpq
  · intro p hp
    exact (D.label_prime p hp).squarefree

theorem label_dvd_generatorCode_iff [DecidableEq A]
    (D : Data K A) {p : ℕ} (hp : p ∈ D.primeLabels) (a : A) :
    p ∣ generatorCode D a ↔
      D.primeIdeal p ∣
        Ideal.span ({D.generator a} : Set (NumberField.RingOfIntegers K)) := by
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

theorem divisor_dvd_generatorCode_iff [DecidableEq A]
    (D : Data K A) {d : ℕ} (hd : d ∣ D.primeLabels.prod id) (a : A) :
    d ∣ generatorCode D a ↔
      ∀ p ∈ d.primeFactors,
        D.primeIdeal p ∣
          Ideal.span ({D.generator a} : Set (NumberField.RingOfIntegers K)) := by
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

theorem coprime_generatorCode_iff [DecidableEq A]
    (D : Data K A) (a : A) :
    Nat.Coprime (D.primeLabels.prod id) (generatorCode D a) ↔
      ∀ p ∈ D.primeLabels,
        ¬ D.primeIdeal p ∣
          Ideal.span ({D.generator a} : Set (NumberField.RingOfIntegers K)) := by
  classical
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    exact (label_dvd_generatorCode_iff D hp a).not.mp
      ((D.label_prime p hp).coprime_iff_not_dvd.mp (h p hp))
  · intro h p hp
    exact (D.label_prime p hp).coprime_iff_not_dvd.mpr
      ((label_dvd_generatorCode_iff D hp a).not.mpr (h p hp))

/-- Aggregating equal generator codes preserves every indicator-weighted
sum.  This is the bookkeeping fact that makes the auxiliary labels
completely lossless. -/
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
          exact (Finset.sum_eq_zero fun a ha ↦ by
            have hfa : f a = n := (Finset.mem_filter.mp ha).2
            simp only [G, hfa, if_neg hpred]).symm
    _ = ∑ a ∈ D.candidates, G a :=
      Finset.sum_fiberwise_of_maps_to hmaps G
    _ = ∑ a ∈ D.candidates,
        if pred (generatorCode D a) then D.weight a else 0 := by
      rfl

/-- The ideal bounding sieve with exact local density `1 / N(P)`. -/
def boundingSieve [DecidableEq A] (D : Data K A) : BoundingSieve where
  support := codeSupport D
  prodPrimes := D.primeLabels.prod id
  prodPrimes_squarefree := primeLabels_product_squarefree D
  weights := codeWeight D
  weights_nonneg := by
    intro n
    exact Finset.sum_nonneg fun a ha ↦
      D.weight_nonneg a (Finset.mem_filter.mp ha).1
  totalMass := D.totalMass
  nu := idealNormNu D
  nu_mult := idealNormNu_mult D
  nu_pos_of_prime := by
    intro p hp hpd
    have hpLabel : p ∈ D.primeLabels := by
      have hprod0 : D.primeLabels.prod id ≠ 0 :=
        (primeLabels_product_squarefree D).ne_zero
      have hpf : p ∈ (D.primeLabels.prod id).primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero hprod0).mpr ⟨hp, hpd⟩
      have heq : (D.primeLabels.prod id).primeFactors = D.primeLabels :=
        Nat.primeFactors_prod D.label_prime
      rw [heq] at hpf
      exact hpf
    rw [idealNormNu_prime hp]
    exact inv_pos.mpr (by
      exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm_primeIdeal D hpLabel)))
  nu_lt_one_of_prime := by
    intro p hp hpd
    have hpLabel : p ∈ D.primeLabels := by
      have hprod0 : D.primeLabels.prod id ≠ 0 :=
        (primeLabels_product_squarefree D).ne_zero
      have hpf : p ∈ (D.primeLabels.prod id).primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero hprod0).mpr ⟨hp, hpd⟩
      have heq : (D.primeLabels.prod id).primeFactors = D.primeLabels :=
        Nat.primeFactors_prod D.label_prime
      rw [heq] at hpf
      exact hpf
    rw [idealNormNu_prime hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_absNorm_primeIdeal D hpLabel)

@[simp] theorem boundingSieve_totalMass [DecidableEq A] (D : Data K A) :
    (boundingSieve D).totalMass = D.totalMass := rfl

@[simp] theorem boundingSieve_nu [DecidableEq A] (D : Data K A) :
    (boundingSieve D).nu = idealNormNu D := rfl

@[simp] theorem boundingSieve_prodPrimes [DecidableEq A] (D : Data K A) :
    (boundingSieve D).prodPrimes = D.primeLabels.prod id := rfl

/-- The abstract multiple sum is literal simultaneous prime-ideal
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

/-- The abstract sifted sum is literal avoidance of all selected prime
ideals. -/
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

/-- Exact ideal-divisibility formula for the sieve remainder. -/
theorem boundingSieve_rem_eq [DecidableEq A]
    (D : Data K A) {d : ℕ} (hd : d ∣ D.primeLabels.prod id) :
    (boundingSieve D).rem d =
      idealDivisorMass D d - idealNormNu D d * D.totalMass := by
  rw [BoundingSieve.rem, boundingSieve_multSum D hd]
  rfl

/-- Exact product formula for every squarefree subproduct remainder main
term. -/
theorem boundingSieve_rem_eq_normProduct [DecidableEq A]
    (D : Data K A) {d : ℕ} (hd : d ∣ D.primeLabels.prod id) :
    (boundingSieve D).rem d = idealDivisorMass D d -
      (∏ p ∈ d.primeFactors,
        (Ideal.absNorm (D.primeIdeal p) : ℝ)⁻¹) * D.totalMass := by
  have hdz : d ≠ 0 := by
    intro h
    subst d
    exact (primeLabels_product_squarefree D).ne_zero
      (Nat.eq_zero_of_zero_dvd hd)
  rw [boundingSieve_rem_eq D hd, idealNormNu_apply hdz]

/-! ## Fixed-ideal unions of growing-modulus generator cells

The preceding prime-ideal adapter is exact algebraically, but the available
uniform lattice estimate varies the *rational modulus* while keeping the
ideal lattice fixed.  The next definitions expose precisely that valid
analytic specialization.  A later norm-form or tensor argument supplies a
finite set `accepted` of coordinate residue vectors; the theorem below sums
the per-cell estimate with no loss other than the literal number of accepted
cells. -/

open Erdos980.ElliottTail.IdealGeneratorCongruenceCount

/-- Sum of canonical-generator counts over a finite collection of coordinate
residue cells.  Keeping it as a sum (rather than a set union) makes the
endpoint estimate independent of a separate disjointness proof; distinct
coordinate residue cells are the intended application. -/
def generatorCongruenceCellFinsetCount
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (m : ℕ) [NeZero m]
    (accepted : Finset (index K → ZMod m)) (t : ℝ) : ℕ :=
  ∑ k ∈ accepted,
    Nat.card ↑(generatorCongruenceCell J m k ∩
      t • generatorNormRegion K)

open Classical in
/-- Uniform growing-modulus estimate for a finite union of accepted
generator-coordinate cells in one fixed ideal lattice.  The same constant
works for every modulus, accepted set, translate, and scale in the natural
range `m ≤ t`. -/
theorem exists_uniform_generatorCongruenceCellFinsetCount_growing_modulus
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) [NeZero m]
      (accepted : Finset (index K → ZMod m)) (t : ℝ), (m : ℝ) ≤ t →
      |(generatorCongruenceCellFinsetCount J m accepted t : ℝ) -
        (accepted.card : ℝ) *
          (MeasureTheory.volume.real (generatorNormRegion K) /
            |LinearMap.det (idealLatticeChart J :
              (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
            (t / m) ^ Fintype.card (index K))| ≤
        (accepted.card : ℝ) * C *
          (t / m) ^ (Fintype.card (index K) - 1) := by
  classical
  obtain ⟨C₀, hC₀⟩ :=
    exists_uniform_generatorCongruenceCell_count_growing_modulus K J
  refine ⟨|C₀|, abs_nonneg C₀, ?_⟩
  intro m hm accepted t hmt
  let main : ℝ :=
    MeasureTheory.volume.real (generatorNormRegion K) /
      |LinearMap.det (idealLatticeChart J :
        (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
      (t / m) ^ Fintype.card (index K)
  let boundary : ℝ :=
    (t / m) ^ (Fintype.card (index K) - 1)
  have hratio : 0 ≤ t / (m : ℝ) := by
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    exact div_nonneg (le_trans (Nat.cast_nonneg m) hmt) hmpos.le
  have hboundary : 0 ≤ boundary := by
    exact pow_nonneg hratio _
  have hcell : ∀ k : index K → ZMod m,
      |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) - main| ≤
        |C₀| * boundary := by
    intro k
    exact (hC₀ m k t hmt).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C₀) hboundary)
  simp only [generatorCongruenceCellFinsetCount, Nat.cast_sum]
  change |(∑ k ∈ accepted,
        (Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ)) -
        (accepted.card : ℝ) * main| ≤
      (accepted.card : ℝ) * |C₀| * boundary
  have hconst : ∑ _k ∈ accepted, main = (accepted.card : ℝ) * main := by
    simp [mul_comm]
  rw [← hconst, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ accepted,
        ((Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) - main)| ≤
        ∑ k ∈ accepted,
          |(Nat.card ↑(generatorCongruenceCell J m k ∩
            t • generatorNormRegion K) : ℝ) - main| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ accepted, |C₀| * boundary := by
      exact Finset.sum_le_sum fun k hk ↦ hcell k
    _ = (accepted.card : ℝ) * |C₀| * boundary := by
      simp [mul_assoc]

end Erdos980.ElliottTail.GeneratorResidueBoundingSieve
