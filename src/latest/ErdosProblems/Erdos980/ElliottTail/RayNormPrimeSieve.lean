/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.NumberFieldPrimeSieve
import ErdosProblems.Erdos980.ElliottTail.IdealGeneratorCongruenceCount

/-!
# A fixed-lattice sieve on conductor norms

For one ray-class correction ideal `J`, a chosen generator satisfies
`(alpha) = P * J`.  Hence the natural conductor norm `N(P)` is the quotient
`N((alpha)) / N(J)`.  Unlike a code made from arbitrary prime ideals, this
is an actual natural number.  Divisibility by a squarefree rational integer
`d` is therefore determined by the coordinate residue vector of `alpha`
modulo `d` in the *same fixed lattice* `J`.

This file gives the lossless finite `BoundingSieve` adapter for those
conductor norms.  It also exposes the finite residue-vector union which is
the exact input to
`exists_uniform_generatorCongruenceCell_count_growing_modulus`.
-/

open scoped BigOperators NumberField nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.RayNormPrimeSieve

open NumberField

/-- A finite family of canonical generators in one fixed correction-ideal
lattice, together with their natural conductor norms. -/
structure Data (K A : Type*) [Field K] [NumberField K] where
  correctionIdeal : (Ideal (NumberField.RingOfIntegers K))⁰
  candidates : Finset A
  generator : A → NumberField.RingOfIntegers K
  generator_mem_correction : ∀ a ∈ candidates,
    generator a ∈ (correctionIdeal : Ideal (NumberField.RingOfIntegers K))
  conductorNorm : A → ℕ
  normBound : ℕ
  conductorNorm_le : ∀ a ∈ candidates, conductorNorm a ≤ normBound
  principalNorm_eq : ∀ a ∈ candidates,
    Ideal.absNorm (Ideal.span
        ({generator a} : Set (NumberField.RingOfIntegers K))) =
      conductorNorm a * Ideal.absNorm
        (correctionIdeal : Ideal (NumberField.RingOfIntegers K))
  weight : A → ℝ
  weight_nonneg : ∀ a ∈ candidates, 0 ≤ weight a
  sievePrimes : Finset ℕ
  sievePrimes_prime : ∀ p ∈ sievePrimes, p.Prime
  totalMass : ℝ
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p, p.Prime → p ∣ sievePrimes.prod id → 0 < nu p
  nu_lt_one_of_prime : ∀ p, p.Prime → p ∣ sievePrimes.prod id → nu p < 1

variable {K A : Type*} [Field K] [NumberField K]

/-- The natural numbers actually occurring as conductor norms. -/
def normSupport [DecidableEq A] (D : Data K A) : Finset ℕ :=
  D.candidates.image D.conductorNorm

/-- Aggregate the weights of all generators having the same conductor norm. -/
def normWeight [DecidableEq A] (D : Data K A) (n : ℕ) : ℝ :=
  ∑ a ∈ D.candidates.filter fun a ↦ D.conductorNorm a = n, D.weight a

/-- Literal weighted mass with conductor norm divisible by `d`. -/
def normDivisorMass [DecidableEq A] (D : Data K A) (d : ℕ) : ℝ :=
  ∑ a ∈ D.candidates,
    if d ∣ D.conductorNorm a then D.weight a else 0

/-- Literal weighted mass whose conductor norm avoids every sieving prime. -/
def normSiftedMass [DecidableEq A] (D : Data K A) : ℝ :=
  ∑ a ∈ D.candidates,
    if ∀ p ∈ D.sievePrimes, ¬ p ∣ D.conductorNorm a
    then D.weight a else 0

theorem sievePrimes_product_squarefree (D : Data K A) :
    Squarefree (D.sievePrimes.prod id) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (D.sievePrimes_prime p hp)
      (D.sievePrimes_prime q hq)).mpr hpq
  · intro p hp
    exact (D.sievePrimes_prime p hp).squarefree

/-- Fibre aggregation preserves every indicator-weighted norm sum. -/
theorem sum_normWeight_indicator [DecidableEq A]
    (D : Data K A) (pred : ℕ → Prop) [DecidablePred pred] :
    (∑ n ∈ normSupport D, if pred n then normWeight D n else 0) =
      ∑ a ∈ D.candidates,
        if pred (D.conductorNorm a) then D.weight a else 0 := by
  classical
  let f : A → ℕ := D.conductorNorm
  let G : A → ℝ := fun a ↦ if pred (f a) then D.weight a else 0
  have hmaps : ∀ a ∈ D.candidates, f a ∈ D.candidates.image f := by
    intro a ha
    exact Finset.mem_image_of_mem f ha
  calc
    (∑ n ∈ normSupport D, if pred n then normWeight D n else 0) =
        ∑ n ∈ D.candidates.image f,
          ∑ a ∈ D.candidates.filter (fun a ↦ f a = n), G a := by
      apply Finset.sum_congr
      · rfl
      · intro n hn
        by_cases hpred : pred n
        · rw [if_pos hpred]
          unfold normWeight
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
        if pred (D.conductorNorm a) then D.weight a else 0 := by
      rfl

/-- The natural-conductor-norm bounding sieve. -/
def boundingSieve [DecidableEq A] (D : Data K A) : BoundingSieve where
  support := normSupport D
  prodPrimes := D.sievePrimes.prod id
  prodPrimes_squarefree := sievePrimes_product_squarefree D
  weights := normWeight D
  weights_nonneg := by
    intro n
    exact Finset.sum_nonneg fun a ha ↦
      D.weight_nonneg a (Finset.mem_filter.mp ha).1
  totalMass := D.totalMass
  nu := D.nu
  nu_mult := D.nu_mult
  nu_pos_of_prime := D.nu_pos_of_prime
  nu_lt_one_of_prime := D.nu_lt_one_of_prime

@[simp] theorem boundingSieve_prodPrimes [DecidableEq A] (D : Data K A) :
    (boundingSieve D).prodPrimes = D.sievePrimes.prod id := rfl

@[simp] theorem boundingSieve_totalMass [DecidableEq A] (D : Data K A) :
    (boundingSieve D).totalMass = D.totalMass := rfl

@[simp] theorem boundingSieve_nu [DecidableEq A] (D : Data K A) :
    (boundingSieve D).nu = D.nu := rfl

/-- The abstract multiple sum is exactly natural conductor-norm divisibility. -/
theorem boundingSieve_multSum [DecidableEq A] (D : Data K A) (d : ℕ) :
    (boundingSieve D).multSum d = normDivisorMass D d := by
  classical
  rw [BoundingSieve.multSum]
  change (∑ n ∈ normSupport D,
    if d ∣ n then normWeight D n else 0) = normDivisorMass D d
  rw [sum_normWeight_indicator]
  rfl

/-- The abstract sifted sum is exactly avoidance of the selected rational
prime divisors of the conductor norm. -/
theorem coprime_conductorNorm_iff (D : Data K A) (a : A) :
    Nat.Coprime (D.sievePrimes.prod id) (D.conductorNorm a) ↔
      ∀ p ∈ D.sievePrimes, ¬ p ∣ D.conductorNorm a := by
  classical
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    exact (D.sievePrimes_prime p hp).coprime_iff_not_dvd.mp (h p hp)
  · intro h p hp
    exact (D.sievePrimes_prime p hp).coprime_iff_not_dvd.mpr (h p hp)

theorem boundingSieve_siftedSum [DecidableEq A] (D : Data K A) :
    (boundingSieve D).siftedSum = normSiftedMass D := by
  classical
  rw [BoundingSieve.siftedSum]
  change (∑ n ∈ normSupport D,
      if Nat.Coprime (D.sievePrimes.prod id) n
      then normWeight D n else 0) = normSiftedMass D
  rw [sum_normWeight_indicator]
  unfold normSiftedMass
  apply Finset.sum_congr rfl
  intro a ha
  have hiff := coprime_conductorNorm_iff D a
  by_cases hcop : Nat.Coprime (D.sievePrimes.prod id) (D.conductorNorm a)
  · rw [if_pos hcop, if_pos (hiff.mp hcop)]
  · rw [if_neg hcop, if_neg (fun h ↦ hcop (hiff.mpr h))]

/-- Exact remainder identity, valid for every modulus. -/
theorem boundingSieve_rem_eq [DecidableEq A] (D : Data K A) (d : ℕ) :
    (boundingSieve D).rem d =
      normDivisorMass D d - D.nu d * D.totalMass := by
  rw [BoundingSieve.rem, boundingSieve_multSum]
  rfl

/-! ## Finite residue-vector union in the fixed lattice -/

/-- Residue vectors on which a supplied integral conductor-norm form
vanishes modulo `d`.  This is the exact finite set of growing-modulus cells
which must be summed in the geometric remainder estimate. -/
def normDivisibleResidues (K : Type*) [Field K] [NumberField K]
    (d : ℕ) [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d) :
    Finset (NumberField.mixedEmbedding.index K → ZMod d) := by
  classical
  letI := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
  exact Finset.univ.filter fun k ↦ normMod k = 0

@[simp] theorem mem_normDivisibleResidues
    (K : Type*) [Field K] [NumberField K]
    {d : ℕ} [NeZero d]
    {normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d}
    {k : NumberField.mixedEmbedding.index K → ZMod d} :
    k ∈ normDivisibleResidues K d normMod ↔ normMod k = 0 := by
  classical
  simp [normDivisibleResidues]

theorem card_normDivisibleResidues_le
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d) :
    (normDivisibleResidues K d normMod).card ≤
      d ^ Nat.card (NumberField.mixedEmbedding.index K) := by
  classical
  letI := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
  calc
    (normDivisibleResidues K d normMod).card ≤
        (Finset.univ : Finset
          (NumberField.mixedEmbedding.index K → ZMod d)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = d ^ Nat.card (NumberField.mixedEmbedding.index K) := by
      rw [Finset.card_univ, Fintype.card_pi]
      simp

/-- Explicit compatibility interface between conductor-norm divisibility
and the residue-vector cells of the fixed correction lattice. -/
structure NormResidueModel (D : Data K A) where
  normMod : (d : ℕ) →
    (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d
  residueVector : (d : ℕ) → A →
    (NumberField.mixedEmbedding.index K → ZMod d)
  normMod_residueVector : ∀ d a, normMod d (residueVector d a) =
    (D.conductorNorm a : ZMod d)

theorem NormResidueModel.dvd_conductorNorm_iff_mem
    [DecidableEq A] {D : Data K A} (M : NormResidueModel D)
    (d : ℕ) [NeZero d] (a : A) :
    d ∣ D.conductorNorm a ↔
      M.residueVector d a ∈ normDivisibleResidues K d (M.normMod d) := by
  rw [mem_normDivisibleResidues, M.normMod_residueVector]
  exact (ZMod.natCast_eq_zero_iff (D.conductorNorm a) d).symm

/-! ## Coordinatewise Chinese remaindering -/

/-- Coordinatewise Chinese remainder equivalence.  This is the exact bridge used to impose a
fixed ray/tensor condition modulo `f` and natural-norm divisibility modulo a coprime squarefree
integer `d` in one congruence cell modulo `f * d`. -/
def coordinateChineseRemainder
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hfd : Nat.Coprime f d) :
    (NumberField.mixedEmbedding.index K → ZMod (f * d)) ≃
      (NumberField.mixedEmbedding.index K → ZMod f) ×
        (NumberField.mixedEmbedding.index K → ZMod d) where
  toFun k :=
    (⟨fun i ↦ (ZMod.chineseRemainder hfd (k i)).1,
      fun i ↦ (ZMod.chineseRemainder hfd (k i)).2⟩ :
        (NumberField.mixedEmbedding.index K → ZMod f) ×
          (NumberField.mixedEmbedding.index K → ZMod d))
  invFun k i := (ZMod.chineseRemainder hfd).symm (k.1 i, k.2 i)
  left_inv k := by
    funext i
    exact (ZMod.chineseRemainder hfd).symm_apply_apply (k i)
  right_inv k := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((ZMod.chineseRemainder hfd).apply_symm_apply (k.1 i, k.2 i))
    · exact congrArg Prod.snd ((ZMod.chineseRemainder hfd).apply_symm_apply (k.1 i, k.2 i))

/-- The combined coordinate residues obtained from a finite set of ray residues modulo `f` and a
finite set of norm residues modulo the coprime modulus `d`. -/
def crtAllowedResidues
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hfd : Nat.Coprime f d)
    (rayAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod f))
    (normAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod d)) :
    Finset (NumberField.mixedEmbedding.index K → ZMod (f * d)) := by
  classical
  exact (rayAllowed.product normAllowed).map
    (coordinateChineseRemainder K hfd).symm.toEmbedding

@[simp] theorem mem_crtAllowedResidues
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hfd : Nat.Coprime f d)
    {rayAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod f)}
    {normAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod d)}
    {k : NumberField.mixedEmbedding.index K → ZMod (f * d)} :
    k ∈ crtAllowedResidues K hfd rayAllowed normAllowed ↔
      (coordinateChineseRemainder K hfd k).1 ∈ rayAllowed ∧
        (coordinateChineseRemainder K hfd k).2 ∈ normAllowed := by
  classical
  simp [crtAllowedResidues]

/-- CRT preserves the product cardinality exactly. -/
theorem card_crtAllowedResidues
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hfd : Nat.Coprime f d)
    (rayAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod f))
    (normAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod d)) :
    (crtAllowedResidues K hfd rayAllowed normAllowed).card =
      rayAllowed.card * normAllowed.card := by
  classical
  simp [crtAllowedResidues]

/-- A family of coordinate norm forms whose zero sets respect the coordinatewise Chinese
remainder equivalence.  The signed algebraic norm in any fixed integral ideal basis is the
principal example. -/
structure CRTNormResidueSystem
    (K : Type*) [Field K] [NumberField K] where
  normMod : (d : ℕ) →
    (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d
  zero_chineseRemainder : ∀ {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hmn : Nat.Coprime m n)
    (k : NumberField.mixedEmbedding.index K → ZMod (m * n)),
    normMod (m * n) k = 0 ↔
      normMod m (coordinateChineseRemainder K hmn k).1 = 0 ∧
        normMod n (coordinateChineseRemainder K hmn k).2 = 0

/-- For a CRT-compatible norm form, the number of zero residue vectors is exactly
multiplicative on coprime nonzero moduli. -/
theorem CRTNormResidueSystem.card_normDivisibleResidues_mul
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K)
    (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)]
    (hmn : Nat.Coprime m n) :
    (normDivisibleResidues K (m * n) (M.normMod (m * n))).card =
      (normDivisibleResidues K m (M.normMod m)).card *
        (normDivisibleResidues K n (M.normMod n)).card := by
  classical
  have hset :
      normDivisibleResidues K (m * n) (M.normMod (m * n)) =
        crtAllowedResidues K hmn
          (normDivisibleResidues K m (M.normMod m))
          (normDivisibleResidues K n (M.normMod n)) := by
    ext k
    rw [mem_normDivisibleResidues, mem_crtAllowedResidues,
      mem_normDivisibleResidues, mem_normDivisibleResidues]
    exact M.zero_chineseRemainder hmn k
  rw [hset, card_crtAllowedResidues]

/-- Total version of the norm-zero residue count.  The value at modulus zero is set to zero;
all sieve moduli are nonzero, where this is definitionally the finite zero-set cardinality. -/
def CRTNormResidueSystem.rootCount
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) (d : ℕ) : ℕ :=
  if hd : d = 0 then 0 else by
    letI : NeZero d := ⟨hd⟩
    exact (normDivisibleResidues K d (M.normMod d)).card

@[simp] theorem CRTNormResidueSystem.rootCount_eq
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) (d : ℕ) [NeZero d] :
    M.rootCount K d =
      (normDivisibleResidues K d (M.normMod d)).card := by
  simp [CRTNormResidueSystem.rootCount, NeZero.ne d]

@[simp] theorem CRTNormResidueSystem.rootCount_one
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) :
    M.rootCount K 1 = 1 := by
  classical
  rw [M.rootCount_eq K 1]
  letI := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
  have hset : normDivisibleResidues K 1 (M.normMod 1) = Finset.univ := by
    ext k
    simp only [mem_normDivisibleResidues, Finset.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hset, Finset.card_univ, Fintype.card_pi]
  simp

/-- The total norm-zero root count is multiplicative on coprime nonzero moduli. -/
theorem CRTNormResidueSystem.rootCount_mul
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K)
    (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)]
    (hmn : Nat.Coprime m n) :
    M.rootCount K (m * n) = M.rootCount K m * M.rootCount K n := by
  rw [M.rootCount_eq K (m * n), M.rootCount_eq K m, M.rootCount_eq K n]
  exact M.card_normDivisibleResidues_mul K m n hmn

/-- The norm-zero root count as an arithmetic function. -/
def CRTNormResidueSystem.rootCountingFunction
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) : ArithmeticFunction ℕ where
  toFun := M.rootCount K
  map_zero' := by simp [CRTNormResidueSystem.rootCount]

/-- CRT compatibility makes the norm-zero root-counting function multiplicative. -/
theorem CRTNormResidueSystem.rootCountingFunction_mult
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) :
    (M.rootCountingFunction K).IsMultiplicative := by
  constructor
  · exact M.rootCount_one K
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      have hn : n = 1 := by simpa using hmn
      subst n
      simp [CRTNormResidueSystem.rootCountingFunction,
        CRTNormResidueSystem.rootCount]
    by_cases hn : n = 0
    · subst n
      have hm1 : m = 1 := by simpa using hmn
      subst m
      simp [CRTNormResidueSystem.rootCountingFunction,
        CRTNormResidueSystem.rootCount]
    letI : NeZero m := ⟨hm⟩
    letI : NeZero n := ⟨hn⟩
    letI : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
    exact M.rootCount_mul K m n hmn

/-- Exact prime-factor product for the zero set of a CRT-compatible norm form on a squarefree
modulus. -/
theorem CRTNormResidueSystem.rootCount_eq_prod_primeFactors
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) {d : ℕ} (hd : Squarefree d) :
    M.rootCount K d = ∏ p ∈ d.primeFactors, M.rootCount K p := by
  symm
  exact (M.rootCountingFunction_mult K).prod_primeFactors hd

/-- The exact local density of the zero set of a supplied integral norm form modulo `d`. -/
def normResidueDensity
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d) :
    ℝ := by
  classical
  exact (normDivisibleResidues K d normMod).card /
    (d : ℝ) ^ Nat.card (NumberField.mixedEmbedding.index K)

theorem normResidueDensity_nonneg
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d) :
    0 ≤ normResidueDensity K d normMod := by
  unfold normResidueDensity
  positivity

theorem normResidueDensity_le_one
    (K : Type*) [Field K] [NumberField K]
    {d : ℕ} [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d) :
    normResidueDensity K d normMod ≤ 1 := by
  rw [normResidueDensity, div_le_one]
  · exact_mod_cast card_normDivisibleResidues_le K d normMod
  · exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)) _

open Erdos980.ElliottTail.IdealGeneratorCongruenceCount

/-! ## Integral generators represented by coordinate residues -/

/-- Every coordinate residue vector has an integral representative in the fixed ideal `J` whose
mixed embedding is the chosen lattice-chart translate. -/
theorem exists_generatorOfCoordinate
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    {d : ℕ} (k : NumberField.mixedEmbedding.index K → ZMod d) :
    ∃ a : NumberField.RingOfIntegers K,
      a ∈ (J : Ideal (NumberField.RingOfIntegers K)) ∧
      (NumberField.mixedEmbedding.stdBasis K).equivFunL
          (NumberField.mixedEmbedding K (a : K)) =
        generatorCongruenceTranslate J k := by
  classical
  let z : NumberField.mixedEmbedding.index K → ℝ := fun i ↦ (k i).val
  have hz : z ∈
      (Submodule.span ℤ (Set.range
        (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K))) :
          Set (NumberField.mixedEmbedding.index K → ℝ)) := by
    letI := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
    change z ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)))
    simp only [(Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)).mem_span_iff_repr_mem
      ℤ z, Pi.basisFun_repr, Set.mem_range, eq_intCast, eq_comm]
    intro i
    exact ⟨((k i).val : ℤ), by simp [z]⟩
  have hchart : generatorCongruenceTranslate J k ∈
      idealLatticeChart J ''
        (Submodule.span ℤ (Set.range
          (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K))) :
            Set (NumberField.mixedEmbedding.index K → ℝ)) := by
    exact ⟨z, hz, rfl⟩
  rw [idealLatticeChart_image] at hchart
  obtain ⟨x, hx, hxchart⟩ := hchart
  rw [SetLike.mem_coe] at hx
  rw [NumberField.mixedEmbedding.mem_idealLattice] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  simp only [FractionalIdeal.coe_mk0] at hy
  obtain ⟨a, ha, hay⟩ := hy
  refine ⟨a, ha, ?_⟩
  have hcoe : (a : K) = y := by simpa using hay
  rw [hcoe, hyx, hxchart]

/-- A fixed integral representative of a coordinate residue vector. -/
noncomputable def generatorOfCoordinate
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    {d : ℕ} (k : NumberField.mixedEmbedding.index K → ZMod d) :
    NumberField.RingOfIntegers K :=
  (exists_generatorOfCoordinate K J k).choose

theorem generatorOfCoordinate_mem
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    {d : ℕ} (k : NumberField.mixedEmbedding.index K → ZMod d) :
    generatorOfCoordinate K J k ∈
      (J : Ideal (NumberField.RingOfIntegers K)) :=
  (exists_generatorOfCoordinate K J k).choose_spec.1

theorem embedding_generatorOfCoordinate
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    {d : ℕ} (k : NumberField.mixedEmbedding.index K → ZMod d) :
    (NumberField.mixedEmbedding.stdBasis K).equivFunL
        (NumberField.mixedEmbedding K (generatorOfCoordinate K J k : K)) =
      generatorCongruenceTranslate J k :=
  (exists_generatorOfCoordinate K J k).choose_spec.2

/-- The integral algebraic norm is constant after adding a multiple of the modulus. -/
theorem algebraNorm_add_nat_mul_mod
    {K : Type*} [Field K] [NumberField K]
    (d : ℕ) (x y : NumberField.RingOfIntegers K) :
    ((Algebra.norm ℤ (x + (d : NumberField.RingOfIntegers K) * y) : ℤ) : ZMod d) =
      ((Algebra.norm ℤ x : ℤ) : ZMod d) := by
  classical
  let b := Module.Free.chooseBasis ℤ (NumberField.RingOfIntegers K)
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b,
    Int.cast_det, Int.cast_det]
  congr 1
  rw [show (d : NumberField.RingOfIntegers K) * y = d • y from
    (nsmul_eq_mul _ _).symm, map_add, map_nsmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Int.cast_add]
  rw [show (((d • (Algebra.leftMulMatrix b) y i j) : ℤ) : ZMod d) = 0 by
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul], add_zero]

/-- If the mixed embeddings of two algebraic integers differ by the `d`-multiple of the fixed
ideal lattice, their signed algebraic norms agree modulo `d`. -/
theorem algebraNorm_zmod_eq_of_embedding_sub_mem
    {K : Type*} [Field K] [NumberField K]
    (d : ℕ) (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (x y : NumberField.RingOfIntegers K)
    (hsub : NumberField.mixedEmbedding K (x : K) -
        NumberField.mixedEmbedding K (y : K) ∈
      (d : ℝ) • (NumberField.mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K J) : Set (NumberField.mixedEmbedding.mixedSpace K))) :
    ((Algebra.norm ℤ x : ℤ) : ZMod d) =
      ((Algebra.norm ℤ y : ℤ) : ZMod d) := by
  obtain ⟨v, hv, hveq⟩ := hsub
  simp only at hveq
  rw [SetLike.mem_coe, NumberField.mixedEmbedding.mem_idealLattice] at hv
  obtain ⟨yK, hyK, hyeq⟩ := hv
  simp only [FractionalIdeal.coe_mk0] at hyK
  obtain ⟨w, _, hweq⟩ := hyK
  rw [Algebra.linearMap_apply] at hweq
  have hkey : NumberField.mixedEmbedding K ((x - y :
      NumberField.RingOfIntegers K) : K) =
      NumberField.mixedEmbedding K
        (((d : NumberField.RingOfIntegers K) * w :
          NumberField.RingOfIntegers K) : K) := by
    push_cast
    rw [map_sub, ← hveq, ← hyeq, ← hweq, Nat.cast_smul_eq_nsmul, ← map_nsmul]
    congr 1
    rw [nsmul_eq_mul]
  have hxy : x - y = (d : NumberField.RingOfIntegers K) * w :=
    NumberField.RingOfIntegers.coe_injective (K := K)
      (NumberField.mixedEmbedding_injective K hkey)
  have hx : x = y + (d : NumberField.RingOfIntegers K) * w := by
    linear_combination hxy
  rw [hx]
  exact algebraNorm_add_nat_mul_mod d y w

/-- Coordinate representatives whose integer coordinate vectors agree modulo `m` differ by an
element of the `m`-multiple of the fixed ideal lattice.  The two coordinate vectors may have
different ambient moduli; only their reductions modulo `m` matter. -/
theorem embedding_generatorOfCoordinate_sub_mem_nsmul
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (m : ℕ) {d₁ d₂ : ℕ}
    (k₁ : NumberField.mixedEmbedding.index K → ZMod d₁)
    (k₂ : NumberField.mixedEmbedding.index K → ZMod d₂)
    (hcos : ∀ i,
      ((k₁ i).val : ZMod m) = ((k₂ i).val : ZMod m)) :
    NumberField.mixedEmbedding K (generatorOfCoordinate K J k₁ : K) -
        NumberField.mixedEmbedding K (generatorOfCoordinate K J k₂ : K) ∈
      (m : ℝ) • (NumberField.mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K J) : Set (NumberField.mixedEmbedding.mixedSpace K)) := by
  classical
  have hdvd : ∀ i, (m : ℤ) ∣ ((k₁ i).val : ℤ) - ((k₂ i).val : ℤ) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    exact_mod_cast hcos i
  choose p hp using hdvd
  let z : NumberField.mixedEmbedding.index K → ℝ := fun i ↦ (p i : ℝ)
  have hz : z ∈
      (Submodule.span ℤ (Set.range
        (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K))) :
          Set (NumberField.mixedEmbedding.index K → ℝ)) := by
    letI := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
    change z ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)))
    simp only [(Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)).mem_span_iff_repr_mem
      ℤ z, Pi.basisFun_repr, Set.mem_range, eq_intCast]
    exact fun i ↦ ⟨p i, rfl⟩
  have hchart : idealLatticeChart J z ∈
      (NumberField.mixedEmbedding.stdBasis K).equivFunL ''
        (NumberField.mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K J) :
            Set (NumberField.mixedEmbedding.mixedSpace K)) := by
    rw [← idealLatticeChart_image J]
    exact ⟨z, hz, rfl⟩
  obtain ⟨v, hv, hvchart⟩ := hchart
  refine ⟨v, hv, ?_⟩
  apply (NumberField.mixedEmbedding.stdBasis K).equivFunL.injective
  rw [map_sub, map_smul, embedding_generatorOfCoordinate,
    embedding_generatorOfCoordinate, hvchart]
  simp only [generatorCongruenceTranslate, ← map_sub, ← map_smul]
  congr 1
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, z]
  exact_mod_cast (hp i).symm

/-- The signed algebraic norm residue attached to the chosen representative of a coordinate
vector in the fixed ideal lattice. -/
def coordinateAlgebraNormMod
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (d : ℕ)
    (k : NumberField.mixedEmbedding.index K → ZMod d) : ZMod d :=
  ((Algebra.norm ℤ (generatorOfCoordinate K J k) : ℤ) : ZMod d)

/-- The coordinate algebraic norm residues form a CRT-compatible family. -/
noncomputable def coordinateAlgebraNormResidueSystem
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    CRTNormResidueSystem K where
  normMod := coordinateAlgebraNormMod K J
  zero_chineseRemainder := by
    intro m n _ _ _ hmn k
    let km := (coordinateChineseRemainder K hmn k).1
    let kn := (coordinateChineseRemainder K hmn k).2
    have chinese_fst (x : ZMod (m * n)) :
        (ZMod.chineseRemainder hmn x).1 = (ZMod.cast x : ZMod m) := by
      change (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff])
        (ZMod m × ZMod n) x).1 = _
      rw [ZMod.castHom_apply, Prod.fst_zmod_cast]
    have chinese_snd (x : ZMod (m * n)) :
        (ZMod.chineseRemainder hmn x).2 = (ZMod.cast x : ZMod n) := by
      change (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff])
        (ZMod m × ZMod n) x).2 = _
      rw [ZMod.castHom_apply, Prod.snd_zmod_cast]
    have hcosm : ∀ i, ((km i).val : ZMod m) = ((k i).val : ZMod m) := by
      intro i
      simpa [km, coordinateChineseRemainder] using chinese_fst (k i)
    have hcosn : ∀ i, ((kn i).val : ZMod n) = ((k i).val : ZMod n) := by
      intro i
      simpa [kn, coordinateChineseRemainder] using chinese_snd (k i)
    have hnormm := algebraNorm_zmod_eq_of_embedding_sub_mem m J
      (generatorOfCoordinate K J km) (generatorOfCoordinate K J k)
      (embedding_generatorOfCoordinate_sub_mem_nsmul K J m km k hcosm)
    have hnormn := algebraNorm_zmod_eq_of_embedding_sub_mem n J
      (generatorOfCoordinate K J kn) (generatorOfCoordinate K J k)
      (embedding_generatorOfCoordinate_sub_mem_nsmul K J n kn k hcosn)
    have hpair :
        ZMod.chineseRemainder hmn (coordinateAlgebraNormMod K J (m * n) k) =
          (coordinateAlgebraNormMod K J m km,
            coordinateAlgebraNormMod K J n kn) := by
      apply Prod.ext
      · change (ZMod.chineseRemainder hmn
            (((Algebra.norm ℤ (generatorOfCoordinate K J k) : ℤ) :
              ZMod (m * n)))).1 =
          ((Algebra.norm ℤ (generatorOfCoordinate K J km) : ℤ) : ZMod m)
        rw [chinese_fst]
        rw [ZMod.cast_intCast (by simp)]
        exact hnormm.symm
      · change (ZMod.chineseRemainder hmn
            (((Algebra.norm ℤ (generatorOfCoordinate K J k) : ℤ) :
              ZMod (m * n)))).2 =
          ((Algebra.norm ℤ (generatorOfCoordinate K J kn) : ℤ) : ZMod n)
        rw [chinese_snd]
        rw [ZMod.cast_intCast (by simp)]
        exact hnormn.symm
    constructor
    · intro hk
      have hc : ZMod.chineseRemainder hmn
          (coordinateAlgebraNormMod K J (m * n) k) = 0 := by
        rw [hk, map_zero]
      rw [hpair] at hc
      exact ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
    · rintro ⟨hm, hn⟩
      apply (ZMod.chineseRemainder hmn).injective
      rw [hpair, map_zero, hm, hn]
      rfl

/-- The fixed covolume-normalized volume constant for the generator cone in the ideal lattice
`J`.  Packaging it avoids exposing auxiliary classical `Fintype` and measure instances in later
uniform statements. -/
noncomputable def generatorCellMainConstant
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) : ℝ := by
  classical
  exact MeasureTheory.volume.real (generatorNormRegion K) /
    |LinearMap.det (idealLatticeChart J :
      (NumberField.mixedEmbedding.index K → ℝ) →ₗ[ℝ]
        (NumberField.mixedEmbedding.index K → ℝ))|

/-- The single growing-modulus lattice estimate after imposing ray conditions modulo `f` and
norm-zero conditions modulo a coprime `d`.  Both the main term and error retain the exact product
of the two local residue cardinalities. -/
theorem exists_uniform_crtAllowedGeneratorResidueCellCount
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, ∀ {f d : ℕ} (hfd : Nat.Coprime f d) [NeZero (f * d)]
      (rayAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod f))
      (normAllowed : Finset (NumberField.mixedEmbedding.index K → ZMod d))
      (t : ℝ), ((f * d : ℕ) : ℝ) ≤ t →
      |(allowedGeneratorResidueCellCount J (f * d)
          (crtAllowedResidues K hfd rayAllowed normAllowed) t : ℝ) -
        (rayAllowed.card * normAllowed.card : ℕ) *
          (generatorCellMainConstant K J * (t / (f * d : ℕ)) ^
              Nat.card (NumberField.mixedEmbedding.index K))| ≤
        (rayAllowed.card * normAllowed.card : ℕ) * C *
          (t / (f * d : ℕ)) ^
            (Nat.card (NumberField.mixedEmbedding.index K) - 1) := by
  classical
  obtain ⟨C, hC⟩ := exists_uniform_allowedGeneratorResidueCellCount K J
  refine ⟨C, ?_⟩
  intro f d hfd _ rayAllowed normAllowed t ht
  simpa only [card_crtAllowedResidues, generatorCellMainConstant,
    Nat.card_eq_fintype_card] using
    hC (f * d) (crtAllowedResidues K hfd rayAllowed normAllowed) t ht

/-! ## Norm-zero cell counts and the sieve remainder -/

/-- The literal sum of fixed-lattice congruence-cell counts on which the supplied natural norm
form vanishes modulo `d`. -/
def normDivisibleGeneratorCellCount
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (d : ℕ) [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d)
    (t : ℝ) : ℕ :=
  allowedGeneratorResidueCellCount J d (normDivisibleResidues K d normMod) t

/-- Rewriting the exact norm-zero residue density as the corresponding cell main term. -/
theorem normResidueDensity_mul_main_eq_cellMain
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (d : ℕ) [NeZero d]
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d)
    (t : ℝ) :
    normResidueDensity K d normMod *
        (generatorCellMainConstant K J *
          t ^ Nat.card (NumberField.mixedEmbedding.index K)) =
      (normDivisibleResidues K d normMod).card *
        (generatorCellMainConstant K J *
          (t / d) ^ Nat.card (NumberField.mixedEmbedding.index K)) := by
  classical
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  unfold normResidueDensity
  rw [div_pow]
  field_simp

/-- Uniform fixed-lattice remainder for natural-norm divisibility.  The main term uses the
literal local density `#\{x mod d : Norm(x)=0\} / d^[K:ℚ]`; the error retains the exact number
of norm-zero residue cells. -/
theorem exists_uniform_normDivisibleGeneratorCellCount
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) [NeZero d]
      (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d)
      (t : ℝ), (d : ℝ) ≤ t →
      |(normDivisibleGeneratorCellCount K J d normMod t : ℝ) -
        normResidueDensity K d normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (NumberField.mixedEmbedding.index K))| ≤
        (normDivisibleResidues K d normMod).card * C *
          (t / d) ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_uniform_allowedGeneratorResidueCellCount K J
  refine ⟨|C₀|, abs_nonneg C₀, ?_⟩
  intro d _ normMod t hdt
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hratio : 0 ≤ t / (d : ℝ) :=
    div_nonneg (le_trans (Nat.cast_nonneg d) hdt) hdR.le
  have h := hC₀ d (normDivisibleResidues K d normMod) t hdt
  have hmain := normResidueDensity_mul_main_eq_cellMain K J d normMod t
  simp only [generatorCellMainConstant, Nat.card_eq_fintype_card] at hmain
  rw [← hmain] at h
  simpa only [normDivisibleGeneratorCellCount, generatorCellMainConstant,
    Nat.card_eq_fintype_card] using h.trans (by
    gcongr
    exact le_abs_self C₀)

/-- Multiplying a `k p^(r-1)` root bound over the prime factors of a squarefree modulus gives
the standard `k^ω(d) d^(r-1)` norm-form root bound.  This isolates the entirely finite CRT
calculation from the number-field input establishing the bound at one good rational prime. -/
theorem squarefree_rootCount_le
    {d k r rootCount : ℕ} (localRootCount : ℕ → ℕ)
    (hd : Squarefree d)
    (hfactor : rootCount = ∏ p ∈ d.primeFactors, localRootCount p)
    (hlocal : ∀ p ∈ d.primeFactors,
      localRootCount p ≤ k * p ^ (r - 1)) :
    rootCount ≤ k ^ d.primeFactors.card * d ^ (r - 1) := by
  rw [hfactor]
  calc
    ∏ p ∈ d.primeFactors, localRootCount p ≤
        ∏ p ∈ d.primeFactors, (k * p ^ (r - 1)) := by
      exact Finset.prod_le_prod' hlocal
    _ = (∏ _p ∈ d.primeFactors, k) *
          ∏ p ∈ d.primeFactors, p ^ (r - 1) := by
      rw [← Finset.prod_mul_distrib]
    _ = k ^ d.primeFactors.card *
          (∏ p ∈ d.primeFactors, p) ^ (r - 1) := by
      rw [Finset.prod_const, Finset.prod_pow]
    _ = k ^ d.primeFactors.card * d ^ (r - 1) := by
      rw [Nat.prod_primeFactors_of_squarefree hd]

/-- A prime-by-prime root bound for a CRT-compatible norm form automatically supplies the
squarefree bound required by the geometric remainder theorem. -/
theorem CRTNormResidueSystem.rootCount_le_of_primeFactors
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) {d k r : ℕ}
    (hd : Squarefree d)
    (hlocal : ∀ p ∈ d.primeFactors,
      M.rootCount K p ≤ k * p ^ (r - 1)) :
    M.rootCount K d ≤ k ^ d.primeFactors.card * d ^ (r - 1) := by
  exact squarefree_rootCount_le (fun p ↦ M.rootCount K p) hd
    (M.rootCount_eq_prod_primeFactors K hd) hlocal

/-- Cardinality form of `rootCount_le_of_primeFactors`, ready to feed directly into
`exists_uniform_normDivisibleGeneratorCellCount_of_rootBound`. -/
theorem CRTNormResidueSystem.card_normDivisibleResidues_le_of_primeFactors
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K) {d k r : ℕ} [NeZero d]
    (hd : Squarefree d)
    (hlocal : ∀ p ∈ d.primeFactors,
      M.rootCount K p ≤ k * p ^ (r - 1)) :
    (normDivisibleResidues K d (M.normMod d)).card ≤
      k ^ d.primeFactors.card * d ^ (r - 1) := by
  simpa only [M.rootCount_eq K d] using
    M.rootCount_le_of_primeFactors K hd hlocal

/-- The usual norm-form root bound turns the geometric boundary term into
`C * k^ω(d) * t^([K:ℚ]-1)`, uniformly in the squarefree sieve modulus.  This is the
remainder growth consumed by the Rosser upper-bound sieve. -/
theorem exists_uniform_normDivisibleGeneratorCellCount_of_rootBound
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d k : ℕ) [NeZero d]
      (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d)
      (t : ℝ), (d : ℝ) ≤ t →
      (normDivisibleResidues K d normMod).card ≤
        k ^ d.primeFactors.card *
          d ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) →
      |(normDivisibleGeneratorCellCount K J d normMod t : ℝ) -
        normResidueDensity K d normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (NumberField.mixedEmbedding.index K))| ≤
        C * (k : ℝ) ^ d.primeFactors.card *
          t ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) := by
  classical
  obtain ⟨C, hC, hgeom⟩ := exists_uniform_normDivisibleGeneratorCellCount K J
  refine ⟨C, hC, ?_⟩
  intro d k _ normMod t hdt hroot
  refine (hgeom d normMod t hdt).trans ?_
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have ht : 0 ≤ t := le_trans (Nat.cast_nonneg d) hdt
  have hratio : 0 ≤ t / (d : ℝ) := div_nonneg ht (le_of_lt (by positivity))
  calc
    ((normDivisibleResidues K d normMod).card : ℝ) * C *
          (t / d) ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) ≤
        ((k ^ d.primeFactors.card *
          d ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) : ℕ) : ℝ) * C *
          (t / d) ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) := by
      gcongr
    _ = C * (k : ℝ) ^ d.primeFactors.card *
          t ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) := by
      push_cast
      rw [div_pow]
      field_simp

/-- Fully assembled fixed-lattice remainder for a CRT-compatible norm form.  A local root bound
at the rational primes dividing the squarefree sieve modulus is the only arithmetic input; CRT,
the `k^ω(d) d^(r-1)` root count, and the growing-modulus lattice estimate are all discharged
here. -/
theorem CRTNormResidueSystem.exists_uniform_normDivisibleGeneratorCellCount_of_primeBounds
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (M : CRTNormResidueSystem K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d k : ℕ) [NeZero d] (hd : Squarefree d)
      (t : ℝ), (d : ℝ) ≤ t →
      (∀ p ∈ d.primeFactors,
        M.rootCount K p ≤
          k * p ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1)) →
      |(normDivisibleGeneratorCellCount K J d (M.normMod d) t : ℝ) -
        normResidueDensity K d (M.normMod d) *
          (generatorCellMainConstant K J *
            t ^ Nat.card (NumberField.mixedEmbedding.index K))| ≤
        C * (k : ℝ) ^ d.primeFactors.card *
          t ^ (Nat.card (NumberField.mixedEmbedding.index K) - 1) := by
  obtain ⟨C, hC, hgeom⟩ :=
    exists_uniform_normDivisibleGeneratorCellCount_of_rootBound K J
  refine ⟨C, hC, ?_⟩
  intro d k _ hd t hdt hlocal
  exact hgeom d k (M.normMod d) t hdt
    (M.card_normDivisibleResidues_le_of_primeFactors K hd hlocal)

/-! ## Rosser endpoint -/

def ascendingSievePrimes (D : Data K A) : List ℕ :=
  D.sievePrimes.sort (· ≤ ·)

theorem ascendingSievePrimes_prod (D : Data K A) :
    (ascendingSievePrimes D).prod = D.sievePrimes.prod id := by
  classical
  unfold ascendingSievePrimes
  symm
  simpa using List.prod_toFinset id
    (Finset.sort_nodup D.sievePrimes (· ≤ ·))

theorem ascendingSievePrimes_pairwise (D : Data K A) :
    (ascendingSievePrimes D).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort D.sievePrimes (· ≤ ·)

theorem ascendingSievePrimes_nodup (D : Data K A) :
    (ascendingSievePrimes D).Nodup :=
  Finset.sort_nodup D.sievePrimes (· ≤ ·)

theorem ascendingSievePrimes_prime (D : Data K A) :
    ∀ p ∈ ascendingSievePrimes D, p.Prime := by
  intro p hp
  exact D.sievePrimes_prime p ((Finset.mem_sort (· ≤ ·)).mp hp)

open Erdos851.FiniteCombinatorialSieve
open Erdos387.FiniteBetaSieveBridge

/-- Rosser upper bound for a fixed ray-correction lattice, with the exact
natural-norm remainder left visible. -/
theorem normSiftedMass_le_sortedRosserUpperMain_add_levelEuler
    [DecidableEq A] (D : Data K A) (C : ℝ) (k β level : ℕ)
    (hβ : 1 ≤ β) (hlevel : 1 ≤ level)
    (hrem : ∀ d : ℕ, d ∣ D.sievePrimes.prod id →
      |normDivisorMass D d - D.nu d * D.totalMass| ≤
        C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    normSiftedMass D ≤
      D.totalMass *
          upperMainTerm (rosserStoppingPredicate β level)
            (fun p ↦ D.nu p) (ascendingSievePrimes D) +
        C * level *
          ((ascendingSievePrimes D).map fun p ↦ 1 + (k : ℝ) / p).prod := by
  have hrem' : ∀ d : ℕ, d ∣ (boundingSieve D).prodPrimes →
      |(boundingSieve D).rem d| ≤
        C * (k : ℝ) ^ d.primeFactors.card := by
    intro d hd
    rw [boundingSieve_rem_eq]
    exact hrem d hd
  have hsieve :=
    boundingSieve_siftedSum_le_rosserUpperMain_add_levelEuler
      (boundingSieve D) (ascendingSievePrimes D) C k β level
      (ascendingSievePrimes_prod D) (ascendingSievePrimes_pairwise D)
      (ascendingSievePrimes_nodup D) (ascendingSievePrimes_prime D)
      hβ hlevel hrem' hC
  rw [boundingSieve_siftedSum] at hsieve
  exact hsieve

end Erdos980.ElliottTail.RayNormPrimeSieve
