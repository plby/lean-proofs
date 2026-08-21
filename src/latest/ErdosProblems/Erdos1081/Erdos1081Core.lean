/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.Order.Field
import ErdosProblems.Erdos448.HalberstamComplete448
import ErdosProblems.Erdos469
import ErdosProblems.Erdos387.AnalyticInputs
import Mathlib.NumberTheory.Harmonic.Bounds
import BoundedGaps.BombieriVinogradov.Analytic.BelowCutoffLogSaving
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimePowerRemoval
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import BoundedGaps.Maynard.PrimeMertens
import ErdosProblems.Erdos1081.Erdos1081Split

/-!
# Erdős Problem 1081

This core module formalizes the exact counting function in Erdős Problem 1081,
the analytic and combinatorial estimates used in its resolution, and the final
deductions from those estimates.  The arithmetic closure of the argument is in
the companion `Erdos1081*` modules imported by `Erdos1081.lean`; the detailed
mathematical reconstruction is in `tex/1081.tex`.
-/

namespace Erdos1081

noncomputable section

open Filter Finset Set
open scoped nonZeroDivisors

/-- A natural number is squarefull when every prime divisor occurs at least
twice.  The counting predicates below separately require positive summands,
so the vacuous squarefullness of `0` does not affect the problem. -/
def IsSquarefull (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A representation as a sum of two *positive* squarefull numbers. -/
def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ IsSquarefull a ∧ IsSquarefull b ∧ n = a + b

/-- The counting function in Problem 1081. -/
noncomputable def A (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter IsSumOfTwoSquarefull).card

local instance isSumOfTwoSquarefullDecidable :
    DecidablePred IsSumOfTwoSquarefull := Classical.decPred _

/-- The scale conjectured by Erdős, without the proposed positive constant. -/
noncomputable def landauScale (N : ℕ) : ℝ :=
  (N : ℝ) / Real.sqrt (Real.log (N : ℝ))

/-- The quotient whose convergence to a positive finite constant is precisely
the conjectured asymptotic statement. -/
noncomputable def normalizedCount (N : ℕ) : ℝ :=
  (A N : ℝ) / landauScale N

/-- Erdős's proposed asymptotic, in its ratio-limit formulation. -/
def ErdosConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto normalizedCount atTop (nhds c)

/-- An abstract lower bound strong enough to refute the proposed asymptotic:
the counting function dominates the conjectured scale by a factor tending to
infinity.  Blomer's later `x / (log x)^(α + ε)` lower bound, with `α < 1/2`,
has this consequence. -/
def DivergentLowerBound : Prop :=
  ∃ g : ℕ → ℝ,
    Tendsto g atTop atTop ∧
      ∀ᶠ N : ℕ in atTop, g N * landauScale N ≤ (A N : ℝ)

/-- The precise exponent in the strongest published order-of-magnitude
estimate. -/
noncomputable def blomerGranvilleAlpha : ℝ :=
  1 - (2 : ℝ) ^ (-(1 : ℝ) / 3)

/-- The transition parameter in Blomer's optimizing family of forms. -/
noncomputable def blomerKappa : ℝ :=
  (2 : ℝ) ^ (-(1 : ℝ) / 3)

/-- The logarithmic exponent governing the number of forms in Blomer's
optimizing family. -/
noncomputable def blomerBeta : ℝ :=
  (2 / 3 : ℝ) * blomerKappa * Real.log 2

/-- The middle branch of the simultaneous-representation exponent from
Blomer's uniform quadratic-form theorem. -/
noncomputable def middleRepresentationExponent (m : ℕ) (kappa : ℝ) : ℝ :=
  1 + kappa * (Real.log ((2 : ℝ) ^ m * kappa) - 1)

/-- A proposition recording the lower half of the Blomer estimate.  It is a
definition, not an assumed theorem.  A foundational proof of this proposition
requires the uniform quadratic-form theorem itemized in `tex/1081.tex`. -/
def BlomerLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        C * (N : ℝ) /
            (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + ε) ≤ (A N : ℝ)

theorem blomerKappa_pos : 0 < blomerKappa := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem blomerKappa_ne_zero : blomerKappa ≠ 0 :=
  blomerKappa_pos.ne'

theorem blomerBeta_pos : 0 < blomerBeta := by
  dsimp [blomerBeta]
  exact mul_pos (mul_pos (by norm_num) blomerKappa_pos)
    (Real.log_pos (by norm_num))

theorem blomerGranvilleAlpha_eq_one_sub_kappa :
    blomerGranvilleAlpha = 1 - blomerKappa := by
  rfl

/-- The one-form exponent identity used in the lower main term. -/
theorem middleRepresentationExponent_one_blomerKappa :
    middleRepresentationExponent 1 blomerKappa =
      blomerGranvilleAlpha + blomerBeta := by
  have hlog :
      Real.log (2 * blomerKappa) = (2 / 3 : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) blomerKappa_ne_zero]
    rw [show blomerKappa = (2 : ℝ) ^ (-(1 : ℝ) / 3) by rfl,
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [middleRepresentationExponent, pow_one, hlog,
    blomerGranvilleAlpha_eq_one_sub_kappa]
  dsimp [blomerBeta]
  ring

/-- The two-form exponent identity used in the Bonferroni error term. -/
theorem middleRepresentationExponent_two_blomerKappa :
    middleRepresentationExponent 2 blomerKappa =
      blomerGranvilleAlpha +
        (5 / 3 : ℝ) * blomerKappa * Real.log 2 := by
  have hlog :
      Real.log (4 * blomerKappa) = (5 / 3 : ℝ) * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_mul (by positivity : (2 : ℝ) ^ 2 ≠ 0) blomerKappa_ne_zero,
      Real.log_pow]
    rw [show blomerKappa = (2 : ℝ) ^ (-(1 : ℝ) / 3) by rfl,
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [middleRepresentationExponent,
    show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, hlog,
    blomerGranvilleAlpha_eq_one_sub_kappa]
  ring

/-- After summing over the optimizing family, the ordered-pair exponent is
strictly larger than the one-form main exponent. -/
theorem pairExponent_after_family_lt_singleExponent :
    middleRepresentationExponent 1 blomerKappa - blomerBeta <
      middleRepresentationExponent 2 blomerKappa - 2 * blomerBeta := by
  rw [middleRepresentationExponent_one_blomerKappa,
    middleRepresentationExponent_two_blomerKappa]
  dsimp [blomerBeta]
  have hk : 0 < blomerKappa := blomerKappa_pos
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

/-! ## Finite class-group signed products

The following elementary construction is the first algebraic ingredient in
Blomer's Lemma 4.5.  A choice of a prime ideal above each split rational
prime contributes either a class or its inverse.  Thus the relevant class of
a tuple is exactly a signed product. -/

section SignedProducts

variable {G : Type*} [CommGroup G]

/-- The product of a tuple in a commutative group, with the coordinates
selected by `sigma` inverted. -/
def signedProduct {k : ℕ} (sigma : Fin k → Bool) (x : Fin k → G) : G :=
  ∏ i, if sigma i then (x i)⁻¹ else x i

/-- A fixed choice of signs gives a multiplicative homomorphism from the
group of tuples to the class group. -/
def signedProductHom {k : ℕ} (sigma : Fin k → Bool) :
    (Fin k → G) →* G where
  toFun := signedProduct sigma
  map_one' := by simp [signedProduct]
  map_mul' x y := by
    classical
    simp only [signedProduct, Pi.mul_apply]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : sigma i <;> simp [h, mul_comm]

@[simp] theorem signedProductHom_apply {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) :
    signedProductHom sigma x = signedProduct sigma x := rfl

/-- Every target class is obtained for every fixed sign pattern, as soon as
the tuple has at least one coordinate.  This is the surjectivity used to
compute the size of each sign fiber in the finite-group counting argument. -/
theorem signedProductHom_surjective {k : ℕ} (hk : 0 < k)
    (sigma : Fin k → Bool) :
    Function.Surjective (signedProductHom sigma : (Fin k → G) → G) := by
  classical
  intro c
  let i0 : Fin k := ⟨0, hk⟩
  let x : Fin k → G := fun i ↦
    if i = i0 then if sigma i0 then c⁻¹ else c else 1
  refine ⟨x, ?_⟩
  rw [signedProductHom_apply, signedProduct]
  rw [Finset.prod_eq_single i0]
  · by_cases h : sigma i0 <;> simp [x, h]
  · intro j hj hji
    simp [x, hji]
  · simp

/-- Every fixed-sign fiber has the expected size.  The multiplicative form
avoids division in `ℕ` and is the useful statement for later cardinality
estimates. -/
theorem signedProduct_fiber_card_mul {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] {k : ℕ} (hk : 0 < k)
    (sigma : Fin k → Bool) (c : G) :
    Fintype.card {x : Fin k → G // signedProductHom sigma x = c} *
        Fintype.card G = (Fintype.card G) ^ k := by
  let f : (Fin k → G) →* G := signedProductHom sigma
  have hf : Function.Surjective f := signedProductHom_surjective hk sigma
  have heq : ∀ d : G,
      (Finset.univ.filter fun x : Fin k → G ↦ f x = d).card =
        (Finset.univ.filter fun x : Fin k → G ↦ f x = c).card := by
    intro d
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf d) (hf c)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin k → G)))
    (t := (Finset.univ : Finset G)) (f := f) (by simp)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsum
  simp_rw [heq] at hsum
  simp only [Finset.sum_const_nat, Finset.card_univ] at hsum
  rw [Nat.mul_comm] at hsum
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun x : Fin k → G ↦ f x = c).card *
    Fintype.card G = Fintype.card G ^ k
  exact hsum.symm

/-- The tuples of classes for which some independent inversion of the
coordinates has signed product `c`.  This is Blomer's finite set `M_k(c)`
for a single class-group factor. -/
noncomputable def signedProductFiber {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] {k : ℕ}
    (sigma : Fin k → Bool) (c : G) : Finset (Fin k → G) :=
  Finset.univ.filter fun x ↦ signedProductHom sigma x = c

noncomputable def signedClassTuples {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] (k : ℕ) (c : G) : Finset (Fin k → G) :=
  (Finset.univ : Finset (Fin k → Bool)).biUnion
    (fun sigma ↦ signedProductFiber sigma c)

theorem signedClassTuples_eq_biUnion {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] (k : ℕ) (c : G) :
    signedClassTuples k c =
      (Finset.univ : Finset (Fin k → Bool)).biUnion
        (fun sigma ↦ signedProductFiber sigma c) := rfl

/-- The elementary union bound gives the `2^k / |G|` half of the upper
bound in Blomer's finite class-group lemma, here stated without natural-number
division. -/
theorem signedClassTuples_card_mul_le {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] (k : ℕ) (hk : 0 < k) (c : G) :
    (signedClassTuples k c).card * Fintype.card G ≤
      2 ^ k * (Fintype.card G) ^ k := by
  classical
  rw [signedClassTuples_eq_biUnion]
  calc
    ((Finset.univ : Finset (Fin k → Bool)).biUnion
          (fun sigma ↦ signedProductFiber sigma c)).card * Fintype.card G ≤
        (∑ sigma : Fin k → Bool, (signedProductFiber sigma c).card) *
          Fintype.card G := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ sigma : Fin k → Bool,
          ((signedProductFiber sigma c).card * Fintype.card G) := by
      rw [Finset.sum_mul]
    _ = ∑ _sigma : Fin k → Bool, (Fintype.card G) ^ k := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      change (Finset.univ.filter fun x : Fin k → G ↦
        signedProductHom sigma x = c).card * Fintype.card G = _
      rw [← Fintype.card_subtype,
        signedProduct_fiber_card_mul hk sigma c]
    _ = 2 ^ k * (Fintype.card G) ^ k := by simp

/-- Cardinality of a fiber of a surjective homomorphism between finite
groups, again in division-free form. -/
theorem surjectiveMonoidHom_fiber_card_mul
    {H K : Type*} [Group H] [Fintype H] [Group K] [Fintype K]
    [DecidableEq K] (f : H →* K) (hf : Function.Surjective f) (c : K) :
    Fintype.card {x : H // f x = c} * Fintype.card K = Fintype.card H := by
  have heq : ∀ d : K,
      (Finset.univ.filter fun x : H ↦ f x = d).card =
        (Finset.univ.filter fun x : H ↦ f x = c).card := by
    intro d
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf d) (hf c)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset H))
    (t := (Finset.univ : Finset K)) (f := f) (by simp)
  rw [Finset.card_univ] at hsum
  simp_rw [heq] at hsum
  simp only [Finset.sum_const_nat, Finset.card_univ] at hsum
  rw [Nat.mul_comm] at hsum
  rw [Fintype.card_subtype]
  exact hsum.symm

/-- A fiber of an arbitrary homomorphism has size `|domain| / |range|`,
provided the specified target lies in the range. -/
theorem monoidHom_fiber_card_mul_range
    {H K : Type*} [Group H] [Fintype H] [Group K] [Fintype K]
    [DecidableEq K] (f : H →* K) {y : K} (hy : y ∈ f.range) :
    Fintype.card {x : H // f x = y} * Nat.card f.range = Fintype.card H := by
  classical
  letI : Fintype f.range := Fintype.ofFinite _
  let y' : f.range := ⟨y, hy⟩
  have h := surjectiveMonoidHom_fiber_card_mul f.rangeRestrict
    f.rangeRestrict_surjective y'
  let e : {x : H // f.rangeRestrict x = y'} ≃ {x : H // f x = y} :=
    Equiv.subtypeEquivProp (by
      funext x
      apply propext
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        apply Subtype.ext
        exact hx)
  rw [Fintype.card_congr e] at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- The square subgroup `G²`. -/
def classSquareSubgroup {G : Type*} [CommGroup G] : Subgroup G :=
  (powMonoidHom 2 : G →* G).range

theorem classSquare_mem {G : Type*} [CommGroup G] (x : G) :
    x ^ 2 ∈ (classSquareSubgroup : Subgroup G) := ⟨x, rfl⟩

/-- In the quotient by squares, inverse and identity sign choices agree. -/
theorem quotient_classSquare_inv_eq {G : Type*} [CommGroup G] (x : G) :
    (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) x⁻¹ =
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) x := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem]
  change x⁻¹ / x ∈ (powMonoidHom 2 : G →* G).range
  refine ⟨x⁻¹, ?_⟩
  simp [div_eq_mul_inv, pow_two]

theorem quotient_signedProduct_eq_product {G : Type*} [CommGroup G]
    {k : ℕ} (sigma : Fin k → Bool) (x : Fin k → G) :
    (QuotientGroup.mk' (classSquareSubgroup : Subgroup G))
        (signedProduct sigma x) =
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) := by
  rw [signedProduct, map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : sigma i
  · simp only [h, ite_true]
    exact quotient_classSquare_inv_eq (x i)
  · simp [h]

/-- Product of all tuple coordinates, viewed modulo squares. -/
def tupleSquareClassHom {G : Type*} [CommGroup G] {k : ℕ} :
    (Fin k → G) →* G ⧸ (classSquareSubgroup : Subgroup G) :=
  (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)).comp
    (signedProductHom fun _ ↦ false)

@[simp] theorem tupleSquareClassHom_apply {G : Type*} [CommGroup G]
    {k : ℕ} (x : Fin k → G) :
    tupleSquareClassHom x =
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) := by
  simp [tupleSquareClassHom, signedProduct]

theorem tupleSquareClassHom_surjective {G : Type*} [CommGroup G]
    {k : ℕ} (hk : 0 < k) :
    Function.Surjective (tupleSquareClassHom :
      (Fin k → G) → G ⧸ (classSquareSubgroup : Subgroup G)) := by
  exact (QuotientGroup.mk'_surjective _).comp
    (signedProductHom_surjective hk (fun _ ↦ false))

/-- The necessary square-class constraint on a signed-product tuple. -/
noncomputable def squareClassConstraintTuples {G : Type*} [CommGroup G]
    [Fintype G] (k : ℕ) (c : G) : Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter fun x ↦ tupleSquareClassHom x =
    (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c

theorem signedClassTuples_subset_squareClassConstraint
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) (c : G) :
    signedClassTuples k c ⊆ squareClassConstraintTuples k c := by
  classical
  intro x hx
  rw [signedClassTuples, Finset.mem_biUnion] at hx
  rcases hx with ⟨sigma, _hsigma, hx⟩
  rw [signedProductFiber, Finset.mem_filter] at hx
  rw [squareClassConstraintTuples, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [tupleSquareClassHom_apply,
    ← quotient_signedProduct_eq_product sigma x,
    ← signedProductHom_apply]
  exact congrArg (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) hx.2

theorem squareClassConstraint_card_mul
    {G : Type*} [CommGroup G] [Fintype G]
    (k : ℕ) (hk : 0 < k) (c : G) :
    (squareClassConstraintTuples k c).card *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) =
      (Fintype.card G) ^ k := by
  classical
  letI : Fintype (G ⧸ (classSquareSubgroup : Subgroup G)) := Fintype.ofFinite _
  change (Finset.univ.filter fun x : Fin k → G ↦ tupleSquareClassHom x =
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c).card * _ = _
  rw [Nat.card_eq_fintype_card]
  rw [← Fintype.card_subtype,
    surjectiveMonoidHom_fiber_card_mul tupleSquareClassHom
      (tupleSquareClassHom_surjective hk)
      ((QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c),
    Fintype.card_fun, Fintype.card_fin]

/-- The square-class obstruction gives the other half of Blomer's elementary
upper bound, `|M_k(c)| ≤ |G|^k / |G/G²|`. -/
theorem signedClassTuples_card_squareClasses_le
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) (hk : 0 < k) (c : G) :
    (signedClassTuples k c).card *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) ≤
      (Fintype.card G) ^ k := by
  rw [← squareClassConstraint_card_mul k hk c]
  exact Nat.mul_le_mul_right _
    (Finset.card_le_card
      (signedClassTuples_subset_squareClassConstraint k c))

/-! ### Two sign fibers

Two distinct non-complementary sign patterns agree in one coordinate and
differ in another.  Their joint homomorphism has as image exactly the pairs
whose ratio is a square class.  This supplies the precise intersection size
needed for the lower half of the finite class-group lemma. -/

def signedProductPairHom {G : Type*} [CommGroup G] {k : ℕ}
    (sigma tau : Fin k → Bool) : (Fin k → G) →* G × G :=
  (signedProductHom sigma).prod (signedProductHom tau)

@[simp] theorem signedProductPairHom_apply {G : Type*} [CommGroup G]
    {k : ℕ} (sigma tau : Fin k → Bool) (x : Fin k → G) :
    signedProductPairHom sigma tau x =
      (signedProduct sigma x, signedProduct tau x) := rfl

def quotientRatioHom {G : Type*} [CommGroup G] :
    G × G →* G ⧸ (classSquareSubgroup : Subgroup G) where
  toFun z := (QuotientGroup.mk' (classSquareSubgroup : Subgroup G))
    (z.1 / z.2)
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, div_eq_mul_inv,
      mul_inv_rev]
    ac_rfl

@[simp] theorem quotientRatioHom_apply {G : Type*} [CommGroup G]
    (a b : G) :
    quotientRatioHom (a, b) =
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (a / b) := rfl

theorem signedPair_range_le_ratio_ker {G : Type*} [CommGroup G]
    {k : ℕ} (sigma tau : Fin k → Bool) :
    (signedProductPairHom sigma tau : (Fin k → G) →* G × G).range ≤
      (quotientRatioHom : G × G →* G ⧸
        (classSquareSubgroup : Subgroup G)).ker := by
  intro z hz
  rcases hz with ⟨x, rfl⟩
  rw [MonoidHom.mem_ker, signedProductPairHom_apply,
    quotientRatioHom_apply, map_div,
    quotient_signedProduct_eq_product,
    quotient_signedProduct_eq_product]
  simp

theorem signedPair_range_eq_ratio_ker {G : Type*} [CommGroup G]
    {k : ℕ} (sigma tau : Fin k → Bool)
    {i j : Fin k} (hsame : sigma i = tau i)
    (hdiff : sigma j ≠ tau j) :
    (signedProductPairHom sigma tau : (Fin k → G) →* G × G).range =
      (quotientRatioHom : G × G →* G ⧸
        (classSquareSubgroup : Subgroup G)).ker := by
  apply le_antisymm (signedPair_range_le_ratio_ker sigma tau)
  intro z hz
  rcases z with ⟨a, b⟩
  rw [MonoidHom.mem_ker, quotientRatioHom_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
  rcases hz with ⟨v, hv⟩
  have hij : i ≠ j := by
    intro h
    subst j
    exact hdiff hsame
  let w : G := a / v
  let xi : G := if sigma i then w⁻¹ else w
  let xj : G := if sigma j then v⁻¹ else v
  let x : Fin k → G := fun l ↦
    if l = i then xi else if l = j then xj else 1
  have hraw (s : Bool) (y : G) :
      (if s then (if s then y⁻¹ else y)⁻¹ else
        (if s then y⁻¹ else y)) = y := by
    cases s <;> simp
  have hrawOther (s t : Bool) (hst : s ≠ t) (y : G) :
      (if t then (if s then y⁻¹ else y)⁻¹ else
        (if s then y⁻¹ else y)) = y⁻¹ := by
    cases s <;> cases t <;> simp_all
  refine ⟨x, ?_⟩
  rw [signedProductPairHom_apply]
  apply Prod.ext
  · change signedProduct sigma x = a
    rw [signedProduct]
    have hterm : (fun l : Fin k ↦ if sigma l then (x l)⁻¹ else x l) =
        fun l ↦ if l = i then w else if l = j then v else 1 := by
      funext l
      by_cases hli : l = i
      · subst l
        simp [x, xi, hraw]
      · by_cases hlj : l = j
        · subst l
          simp [x, hli, xj, hraw]
        · simp [x, hli, hlj]
    rw [hterm]
    have hsplit :
        (fun l : Fin k ↦ if l = i then w else if l = j then v else 1) =
          fun l ↦ (if l = i then w else 1) *
            (if l = j then v else 1) := by
      funext l
      by_cases hli : l = i
      · subst l
        simp [hij]
      · by_cases hlj : l = j
        · subst l
          simp [hij.symm]
        · simp [hli, hlj]
    rw [hsplit, Finset.prod_mul_distrib]
    simp [w]
  · change signedProduct tau x = b
    rw [signedProduct]
    have hterm : (fun l : Fin k ↦ if tau l then (x l)⁻¹ else x l) =
        fun l ↦ if l = i then w else if l = j then v⁻¹ else 1 := by
      funext l
      by_cases hli : l = i
      · subst l
        simp [x, xi, hsame, hraw]
      · by_cases hlj : l = j
        · subst l
          simp [x, hli, xj, hrawOther (sigma j) (tau j) hdiff]
        · simp [x, hli, hlj]
    rw [hterm]
    have hsplit :
        (fun l : Fin k ↦ if l = i then w else if l = j then v⁻¹ else 1) =
          fun l ↦ (if l = i then w else 1) *
            (if l = j then v⁻¹ else 1) := by
      funext l
      by_cases hli : l = i
      · subst l
        simp [hij]
      · by_cases hlj : l = j
        · subst l
          simp [hij.symm]
        · simp [hli, hlj]
    rw [hsplit, Finset.prod_mul_distrib]
    simp only [Fintype.prod_ite_eq']
    have hv' : v ^ 2 = a / b := hv
    calc
      w * v⁻¹ = a * (v ^ 2)⁻¹ := by
        simp [w, div_eq_mul_inv, pow_two]
        group
      _ = a * (a / b)⁻¹ := by rw [hv']
      _ = b := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        rw [show a * (b * a⁻¹) = b * (a * a⁻¹) by ac_rfl]
        simp

theorem quotientRatioHom_surjective {G : Type*} [CommGroup G] :
    Function.Surjective (quotientRatioHom :
      G × G → G ⧸ (classSquareSubgroup : Subgroup G)) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      (classSquareSubgroup : Subgroup G) q with ⟨a, rfl⟩
  refine ⟨(a, 1), ?_⟩
  simp [quotientRatioHom]

theorem quotientRatio_ker_card_mul_squareClasses
    {G : Type*} [CommGroup G] [Fintype G] :
    Nat.card (quotientRatioHom :
        G × G →* G ⧸ (classSquareSubgroup : Subgroup G)).ker *
      Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) =
        (Fintype.card G) ^ 2 := by
  have h := (quotientRatioHom :
    G × G →* G ⧸ (classSquareSubgroup : Subgroup G)).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr quotientRatioHom_surjective] at h
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, pow_two] using h

noncomputable def signedProductPairFiber {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] {k : ℕ}
    (sigma tau : Fin k → Bool) (c : G) : Finset (Fin k → G) :=
  Finset.univ.filter fun x ↦ signedProductPairHom sigma tau x = (c, c)

theorem signedProductPairFiber_card_mul_range
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] {k : ℕ}
    (sigma tau : Fin k → Bool) (c : G)
    {i j : Fin k} (hsame : sigma i = tau i)
    (hdiff : sigma j ≠ tau j) :
    (signedProductPairFiber sigma tau c).card *
        Nat.card (signedProductPairHom sigma tau :
          (Fin k → G) →* G × G).range =
      (Fintype.card G) ^ k := by
  classical
  have hrange :=
    signedPair_range_eq_ratio_ker (G := G) sigma tau hsame hdiff
  have hy : (c, c) ∈ (signedProductPairHom sigma tau :
      (Fin k → G) →* G × G).range := by
    rw [hrange, MonoidHom.mem_ker, quotientRatioHom_apply]
    simp
  have h := monoidHom_fiber_card_mul_range
    (H := Fin k → G) (K := G × G)
    (signedProductPairHom sigma tau) (y := (c, c)) hy
  change (Finset.univ.filter fun x : Fin k → G ↦
      signedProductPairHom sigma tau x = (c, c)).card * _ = _
  rw [← Fintype.card_subtype, h, Fintype.card_fun, Fintype.card_fin]

theorem signedProductPairFiber_card_mul_groupSq
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] {k : ℕ}
    (sigma tau : Fin k → Bool) (c : G)
    {i j : Fin k} (hsame : sigma i = tau i)
    (hdiff : sigma j ≠ tau j) :
    (signedProductPairFiber sigma tau c).card * (Fintype.card G) ^ 2 =
      (Fintype.card G) ^ k *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) := by
  let r := Nat.card (signedProductPairHom sigma tau :
    (Fin k → G) →* G × G).range
  let t := Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))
  have hfiber :=
    signedProductPairFiber_card_mul_range sigma tau c hsame hdiff
  have hrange : r * t = (Fintype.card G) ^ 2 := by
    dsimp [r, t]
    rw [signedPair_range_eq_ratio_ker (G := G) sigma tau hsame hdiff]
    exact quotientRatio_ker_card_mul_squareClasses
  calc
    (signedProductPairFiber sigma tau c).card * (Fintype.card G) ^ 2 =
        (signedProductPairFiber sigma tau c).card * (r * t) := by
          rw [hrange]
    _ = ((signedProductPairFiber sigma tau c).card * r) * t := by ring
    _ = (Fintype.card G) ^ k * t := by rw [hfiber]

end SignedProducts

theorem isSquarefull_mul {m n : ℕ}
    (hm : IsSquarefull m) (hn : IsSquarefull n) :
    IsSquarefull (m * n) := by
  intro p hp hpmn
  rcases hp.dvd_mul.mp hpmn with hpm | hpn
  · exact dvd_mul_of_dvd_left (hm p hp hpm) n
  · exact dvd_mul_of_dvd_right (hn p hp hpn) m

theorem square_isSquarefull (n : ℕ) : IsSquarefull (n ^ 2) := by
  intro p hp hpn
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hpn) 2

theorem prime_cube_isSquarefull {p : ℕ} (hp : p.Prime) :
    IsSquarefull (p ^ 3) := by
  intro q hq hqp
  have hq_dvd_p : q ∣ p := hq.dvd_of_dvd_pow hqp
  have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hq_dvd_p
  subst q
  exact pow_dvd_pow p (by decide : 2 ≤ 3)

/-- Every natural cube is squarefull.  This slightly more general form is
useful after completing the square in a non-diagonal quadratic form. -/
theorem cube_isSquarefull (d : ℕ) : IsSquarefull (d ^ 3) := by
  intro p hp hpd
  have hp_d : p ∣ d := hp.dvd_of_dvd_pow hpd
  exact (pow_dvd_pow_of_dvd hp_d 2).trans
    (pow_dvd_pow d (by decide : 2 ≤ 3))

theorem primeCube_mul_square_isSquarefull {p v : ℕ} (hp : p.Prime) :
    IsSquarefull (p ^ 3 * v ^ 2) :=
  isSquarefull_mul (prime_cube_isSquarefull hp) (square_isSquarefull v)

theorem cube_mul_square_isSquarefull (d v : ℕ) :
    IsSquarefull (d ^ 3 * v ^ 2) :=
  isSquarefull_mul (cube_isSquarefull d) (square_isSquarefull v)

/-- Completing the square converts a value of an arbitrary positive binary
quadratic form of discriminant `-D` into a sum of two squarefull numbers,
provided `D` itself is squarefull.  The identity used is
`4a(au²+buv+cv²) = (2au+bv)² + (4ac-b²)v²`.

This is the algebraic bridge from all form classes of one discriminant to
the original additive problem; no choice of a principal form is required. -/
theorem completedForm_isSumOfTwoSquarefull
    {a b c D u v n : ℕ}
    (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (hdisc : D + b ^ 2 = 4 * a * c)
    (hD : IsSquarefull D) (hDpos : 0 < D)
    (hn : n = a * u ^ 2 + b * u * v + c * v ^ 2) :
    IsSumOfTwoSquarefull (4 * a * n) := by
  have hfirst : 0 < 2 * a * u + b * v := by positivity
  have hsecond : 0 < D * v ^ 2 := mul_pos hDpos (pow_pos hv 2)
  refine ⟨(2 * a * u + b * v) ^ 2, D * v ^ 2,
    pow_pos hfirst 2, hsecond, square_isSquarefull _,
    isSquarefull_mul hD (square_isSquarefull v), ?_⟩
  rw [hn]
  nlinarith

/-- Cube-discriminant specialization of `completedForm_isSumOfTwoSquarefull`. -/
theorem completedCubeDiscriminantForm_isSumOfTwoSquarefull
    {a b c d u v n : ℕ}
    (ha : 0 < a) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (hdisc : d ^ 3 + b ^ 2 = 4 * a * c)
    (hn : n = a * u ^ 2 + b * u * v + c * v ^ 2) :
    IsSumOfTwoSquarefull (4 * a * n) :=
  completedForm_isSumOfTwoSquarefull ha hu hv hdisc
    (cube_isSquarefull d) (pow_pos hd 3) hn

/-! ## Completion-of-square bridge for a whole form class -/

/-- Positive values at most `N` of the natural-coefficient form
`aX² + bXY + cY²`, using positive variables. -/
noncomputable def natFormValues (a b c N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n ↦
    ∃ u ∈ Finset.Icc 1 N, ∃ v ∈ Finset.Icc 1 N,
      n = a * u ^ 2 + b * u * v + c * v ^ 2

/-- The completed-square image of one finite represented-value set. -/
noncomputable def completedNatFormValues (a b c N : ℕ) : Finset ℕ := by
  classical
  exact (natFormValues a b c N).image fun n ↦ 4 * a * n

@[simp] theorem mem_natFormValues {a b c N n : ℕ} :
    n ∈ natFormValues a b c N ↔
      n ∈ Finset.Icc 1 N ∧
        ∃ u ∈ Finset.Icc 1 N, ∃ v ∈ Finset.Icc 1 N,
          n = a * u ^ 2 + b * u * v + c * v ^ 2 := by
  classical
  simp [natFormValues]

theorem completedNatFormValues_subset_A
    {a b c D N : ℕ} (ha : 0 < a)
    (hdisc : D + b ^ 2 = 4 * a * c)
    (hD : IsSquarefull D) (hDpos : 0 < D) :
    completedNatFormValues a b c N ⊆
      (Finset.Icc 1 (4 * a * N)).filter IsSumOfTwoSquarefull := by
  classical
  intro m hm
  rw [completedNatFormValues, Finset.mem_image] at hm
  rcases hm with ⟨n, hn, rfl⟩
  rw [mem_natFormValues] at hn
  rcases hn with ⟨hnIcc, u, huIcc, v, hvIcc, hnform⟩
  rw [Finset.mem_filter]
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
  have hnle : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
  have hu : 0 < u :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp huIcc).1
  have hv : 0 < v :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hvIcc).1
  constructor
  · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.mul_ne_zero (by decide) ha.ne') hnpos.ne'),
      Nat.mul_le_mul_left (4 * a) hnle⟩
  · exact completedForm_isSumOfTwoSquarefull ha hu hv hdisc hD hDpos hnform

/-- Completing the square does not lose cardinality when the leading
coefficient is positive. -/
theorem card_completedNatFormValues
    {a b c N : ℕ} (ha : 0 < a) :
    (completedNatFormValues a b c N).card =
      (natFormValues a b c N).card := by
  classical
  rw [completedNatFormValues, Finset.card_image_of_injective]
  intro m n hmn
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 4 * a) hmn

/-- Every form of a fixed squarefull negative discriminant contributes all
of its represented values to `A`, after the explicit harmless dilation
`n ↦ 4an`. -/
theorem natFormValues_card_le_A
    {a b c D N : ℕ} (ha : 0 < a)
    (hdisc : D + b ^ 2 = 4 * a * c)
    (hD : IsSquarefull D) (hDpos : 0 < D) :
    (natFormValues a b c N).card ≤ A (4 * a * N) := by
  rw [← card_completedNatFormValues ha]
  exact Finset.card_le_card
    (completedNatFormValues_subset_A ha hdisc hD hDpos)

/-- Every positive value of `u² + p³v²` from the quadratic-form family in
Blomer's proof is counted by `A`. -/
theorem specialForm_isSumOfTwoSquarefull {p u v : ℕ}
    (hp : p.Prime) (hu : 0 < u) (hv : 0 < v) :
    IsSumOfTwoSquarefull (u ^ 2 + p ^ 3 * v ^ 2) := by
  refine ⟨u ^ 2, p ^ 3 * v ^ 2, pow_pos hu _,
    mul_pos (pow_pos hp.pos _) (pow_pos hv _), square_isSquarefull u,
    primeCube_mul_square_isSquarefull hp, rfl⟩

/-! ## Finite quadratic-form families -/

/-- Values at most `N` of the special form `u² + p³v²`, with both variables
positive.  Bounding `u` and `v` by `N` loses no value in `Icc 1 N`, and makes
the finite set convenient for exact cardinality arguments. -/
noncomputable def specialFormValues (p N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    ∃ u ∈ Finset.Icc 1 N, ∃ v ∈ Finset.Icc 1 N,
      n = u ^ 2 + p ^ 3 * v ^ 2

/-- The union of the special-form value sets over a finite set of kernels. -/
noncomputable def specialFamilyValues (P : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact P.biUnion fun p => specialFormValues p N

/-- The represented-value count for one special form. -/
noncomputable def specialFormCount (p N : ℕ) : ℕ :=
  (specialFormValues p N).card

/-- The simultaneous represented-value count for two special forms. -/
noncomputable def specialPairCount (p q N : ℕ) : ℕ :=
  (specialFormValues p N ∩ specialFormValues q N).card

@[simp]
theorem mem_specialFormValues {p N n : ℕ} :
    n ∈ specialFormValues p N ↔
      n ∈ Finset.Icc 1 N ∧
        ∃ u ∈ Finset.Icc 1 N, ∃ v ∈ Finset.Icc 1 N,
          n = u ^ 2 + p ^ 3 * v ^ 2 := by
  classical
  simp [specialFormValues]

theorem specialFormValues_subset_A {p N : ℕ} (hp : p.Prime) :
    specialFormValues p N ⊆
      (Finset.Icc 1 N).filter IsSumOfTwoSquarefull := by
  classical
  intro n hn
  rw [mem_specialFormValues] at hn
  rcases hn with ⟨hnIcc, u, huIcc, v, hvIcc, rfl⟩
  rw [Finset.mem_filter]
  have huPos : 0 < u :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp huIcc).1
  have hvPos : 0 < v :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hvIcc).1
  exact ⟨hnIcc, specialForm_isSumOfTwoSquarefull hp huPos hvPos⟩

/-! ### Finite lattice boxes and their exact collision loss -/

/-- Ordered off-diagonal collisions of a finite map. -/
noncomputable def collisionPairs {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α)
    (f : α → β) : Finset (α × α) := by
  classical
  exact (s ×ˢ s).filter fun z ↦ z.1 ≠ z.2 ∧ f z.1 = f z.2

@[simp] theorem mem_collisionPairs {α β : Type*}
    [DecidableEq α] [DecidableEq β] {s : Finset α} {f : α → β}
    {a b : α} :
    (a, b) ∈ collisionPairs s f ↔
      a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ f a = f b := by
  classical
  simp [collisionPairs, and_assoc]

/-- The fiber of a finite map above one value. -/
noncomputable def representationFiber {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α)
    (f : α → β) (y : β) : Finset α :=
  s.filter fun x => f x = y

/-- The second moment of the fiber sizes is exactly the diagonal contribution
plus the ordered off-diagonal collision count. -/
theorem sum_representationFiber_card_sq_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (∑ y ∈ s.image f, (representationFiber s f y).card ^ 2) =
      s.card + (collisionPairs s f).card := by
  classical
  let E := (s ×ˢ s).filter fun z => f z.1 = f z.2
  have hmap : Set.MapsTo (fun z : α × α => f z.1) (E : Set (α × α))
      (s.image f : Set β) := by
    intro z hz
    change z ∈ E at hz
    rw [Finset.mem_filter, Finset.mem_product] at hz
    exact Finset.mem_image.mpr ⟨z.1, hz.1.1, rfl⟩
  have hfiber (y : β) :
      (E.filter fun z => f z.1 = y).card =
        (representationFiber s f y).card ^ 2 := by
    have heq : E.filter (fun z => f z.1 = y) =
        representationFiber s f y ×ˢ representationFiber s f y := by
      ext z
      simp only [E, representationFiber, Finset.mem_filter,
        Finset.mem_product]
      aesop
    rw [heq, Finset.card_product]
    simp [pow_two]
  have hsum : E.card =
      ∑ y ∈ s.image f, (representationFiber s f y).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    exact Finset.sum_congr rfl fun y _ => hfiber y
  have hdiag :
      (E.filter fun z => ¬z.1 ≠ z.2).card = s.card := by
    let diag : α → α × α := fun x => (x, x)
    have heq : E.filter (fun z => ¬z.1 ≠ z.2) = s.image diag := by
      ext z
      simp only [E, Finset.mem_filter, Finset.mem_product,
        Finset.mem_image]
      constructor
      · intro hzmem
        have hz1 : z.1 ∈ s := hzmem.1.1.1
        have hzz : ¬ z.1 ≠ z.2 := hzmem.2
        have hz : z.1 = z.2 := by simpa using hzz
        refine ⟨z.1, hz1, ?_⟩
        rcases z with ⟨a, b⟩
        simp only at hz ⊢
        simp [diag, hz]
      · rintro ⟨x, hx, rfl⟩
        dsimp [diag]
        simp [hx]
    rw [heq, Finset.card_image_iff.mpr]
    intro a _ b _ hab
    exact congrArg Prod.fst hab
  have hsplit := E.card_filter_add_card_filter_not
    (fun z => z.1 ≠ z.2)
  have hcoll : E.filter (fun z => z.1 ≠ z.2) = collisionPairs s f := by
    ext z
    simp only [E, collisionPairs, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [hcoll, hdiag] at hsplit
  omega

/-- Sharp finite second-moment image bound.  Unlike the linear collision
bound below, it retains the square of the number of source points. -/
theorem card_sq_le_image_card_mul_card_add_collisionPairs
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (s.card : ℝ) ^ 2 ≤ ((s.image f).card : ℝ) *
      ((s.card : ℝ) + ((collisionPairs s f).card : ℝ)) := by
  classical
  have hmap : Set.MapsTo f (s : Set α) (s.image f : Set β) := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfirstNat :
      s.card = ∑ y ∈ s.image f, (representationFiber s f y).card := by
    simpa [representationFiber] using
      Finset.card_eq_sum_card_fiberwise hmap
  have hfirst :
      (∑ y ∈ s.image f, ((representationFiber s f y).card : ℝ)) =
        (s.card : ℝ) := by
    exact_mod_cast hfirstNat.symm
  have hsecondNat := sum_representationFiber_card_sq_eq s f
  have hsecond :
      (∑ y ∈ s.image f,
        ((representationFiber s f y).card : ℝ) ^ 2) =
          (s.card : ℝ) + ((collisionPairs s f).card : ℝ) := by
    exact_mod_cast hsecondNat
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := s.image f)
    (f := fun y => ((representationFiber s f y).card : ℝ))
  simpa [hfirst, hsecond] using hcs

/-- A finite map loses at most one image point for each ordered
off-diagonal collision. -/
theorem card_le_card_image_add_card_collisionPairs {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (f : α → β) :
    s.card ≤ (s.image f).card + (collisionPairs s f).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [collisionPairs]
  | @insert a s ha ih =>
      have hcollsub :
          collisionPairs s f ⊆ collisionPairs (insert a s) f := by
        intro z hz
        rcases z with ⟨x, y⟩
        rw [mem_collisionPairs] at hz ⊢
        exact ⟨Finset.mem_insert_of_mem hz.1,
          Finset.mem_insert_of_mem hz.2.1, hz.2.2⟩
      by_cases hfa : f a ∈ s.image f
      · obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hfa
        have hpair : (a, b) ∈ collisionPairs (insert a s) f := by
          rw [mem_collisionPairs]
          exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hb,
            fun heq ↦ ha (heq ▸ hb), hab.symm⟩
        have hpairnot : (a, b) ∉ collisionPairs s f := by
          simp [ha]
        have hstrict :
            collisionPairs s f ⊂ collisionPairs (insert a s) f := by
          rw [Finset.ssubset_iff_subset_ne]
          exact ⟨hcollsub, fun heq ↦ hpairnot (heq ▸ hpair)⟩
        have hcard : (collisionPairs s f).card + 1 ≤
            (collisionPairs (insert a s) f).card := by
          simpa [Nat.add_comm] using Finset.card_lt_card hstrict
        rw [Finset.card_insert_of_notMem ha, Finset.image_insert,
          Finset.card_insert_of_mem hfa]
        omega
      · have hcard : (collisionPairs s f).card ≤
            (collisionPairs (insert a s) f).card :=
          Finset.card_le_card hcollsub
        rw [Finset.card_insert_of_notMem ha, Finset.image_insert,
          Finset.card_insert_of_notMem hfa]
        omega

/-- The rectangular box of positive pairs used to count values of one
special form. -/
def specialFormBox (U V : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 U ×ˢ Finset.Icc 1 V

/-- The values of `x² + p³y²` on a positive rectangular box. -/
noncomputable def specialFormBoxValues (p U V : ℕ) : Finset ℕ := by
  classical
  exact (specialFormBox U V).image fun z ↦
    z.1 ^ 2 + p ^ 3 * z.2 ^ 2

@[simp] theorem card_specialFormBox (U V : ℕ) :
    (specialFormBox U V).card = U * V := by
  simp [specialFormBox, Nat.card_Icc]

/-- Every value in a positive box belongs to the matching represented-value
set at the corner bound. -/
theorem specialFormBoxValues_subset
    (p U V : ℕ) (hp : 0 < p) :
    specialFormBoxValues p U V ⊆
      specialFormValues p (U ^ 2 + p ^ 3 * V ^ 2) := by
  classical
  intro n hn
  rw [specialFormBoxValues, Finset.mem_image] at hn
  rcases hn with ⟨⟨u, v⟩, huv, rfl⟩
  rw [mem_specialFormValues]
  rw [specialFormBox, Finset.mem_product] at huv
  have hu := Finset.mem_Icc.mp huv.1
  have hv := Finset.mem_Icc.mp huv.2
  change 1 ≤ u ∧ u ≤ U at hu
  change 1 ≤ v ∧ v ≤ V at hv
  have hle :
      u ^ 2 + p ^ 3 * v ^ 2 ≤ U ^ 2 + p ^ 3 * V ^ 2 := by
    exact Nat.add_le_add (Nat.pow_le_pow_left hu.2 2)
      (Nat.mul_le_mul_left (p ^ 3) (Nat.pow_le_pow_left hv.2 2))
  have huN : u ≤ U ^ 2 + p ^ 3 * V ^ 2 := by
    calc
      u ≤ u ^ 2 := by nlinarith
      _ ≤ u ^ 2 + p ^ 3 * v ^ 2 := Nat.le_add_right _ _
      _ ≤ _ := hle
  have hvN : v ≤ U ^ 2 + p ^ 3 * V ^ 2 := by
    calc
      v ≤ v ^ 2 := by nlinarith
      _ ≤ u ^ 2 + p ^ 3 * v ^ 2 := by
        have hp3 : 1 ≤ p ^ 3 := pow_pos hp 3
        nlinarith
      _ ≤ _ := hle
  have hn1 : 1 ≤ u ^ 2 + p ^ 3 * v ^ 2 := by
    calc
      1 ≤ u := hu.1
      _ ≤ u ^ 2 := by nlinarith
      _ ≤ u ^ 2 + p ^ 3 * v ^ 2 := Nat.le_add_right _ _
  refine ⟨Finset.mem_Icc.mpr ⟨hn1, hle⟩,
    u, Finset.mem_Icc.mpr ⟨hu.1, huN⟩,
    v, Finset.mem_Icc.mpr ⟨hv.1, hvN⟩, rfl⟩

/-- Raw positive lattice points give a lower bound for distinct form values,
up to the exact ordered collision set. -/
theorem specialFormBox_card_le_values_add_collisions (p U V : ℕ) :
    U * V ≤ (specialFormBoxValues p U V).card +
      (collisionPairs (specialFormBox U V)
        (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)).card := by
  simpa [specialFormBoxValues] using
    card_le_card_image_add_card_collisionPairs (specialFormBox U V)
      (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)

/-- Sharp second-moment lower bound for the number of distinct values of a
special form on a rectangular box.  The source cardinality is exactly
`U * V`; the second moment splits into the diagonal and the ordered
off-diagonal collision count. -/
theorem specialFormBox_card_sq_le_values_mul_card_add_collisions
    (p U V : ℕ) :
    ((U * V : ℕ) : ℝ) ^ 2 ≤
      ((specialFormBoxValues p U V).card : ℝ) *
        (((U * V : ℕ) : ℝ) +
          ((collisionPairs (specialFormBox U V)
            (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)).card : ℝ)) := by
  simpa [specialFormBoxValues] using
    card_sq_le_image_card_mul_card_add_collisionPairs
      (specialFormBox U V)
      (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)

/-- Difference-and-sum data for one ordered collision of a diagonal form. -/
structure FormCollisionCertificate where
  forward : Bool
  leftDiff : ℕ
  leftSum : ℕ
  rightDiff : ℕ
  rightSum : ℕ
  deriving DecidableEq

/-- Equal values of a positive diagonal form have opposite coordinate
orderings unless the pairs coincide. -/
theorem specialFormValue_right_lt_of_left_lt
    {p x y u v : ℕ} (hp : 0 < p)
    (heq : x ^ 2 + p ^ 3 * y ^ 2 = u ^ 2 + p ^ 3 * v ^ 2)
    (hxu : x < u) : v < y := by
  by_contra hnot
  have hyv : y ≤ v := by omega
  have hx2 : x ^ 2 < u ^ 2 := Nat.pow_lt_pow_left hxu (by decide)
  have hy2 : y ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hyv 2
  have hp3 : 0 < p ^ 3 := pow_pos hp 3
  nlinarith

theorem specialFormValue_left_lt_of_right_lt
    {p x y u v : ℕ} (hp : 0 < p)
    (heq : x ^ 2 + p ^ 3 * y ^ 2 = u ^ 2 + p ^ 3 * v ^ 2)
    (hyv : y < v) : u < x := by
  by_contra hnot
  have hxu : x ≤ u := by omega
  have hx2 : x ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hxu 2
  have hy2 : y ^ 2 < v ^ 2 := Nat.pow_lt_pow_left hyv (by decide)
  have hp3 : 0 < p ^ 3 := pow_pos hp 3
  nlinarith

/-- The difference-of-squares factorization, with natural subtraction kept
honest by the two order hypotheses. -/
theorem specialFormCollision_product_identity
    {p x y u v : ℕ}
    (heq : x ^ 2 + p ^ 3 * y ^ 2 = u ^ 2 + p ^ 3 * v ^ 2)
    (hxu : x ≤ u) (hvy : v ≤ y) :
    (u - x) * (u + x) = p ^ 3 * (y - v) * (y + v) := by
  have heqZ : (x : ℤ) ^ 2 + (p : ℤ) ^ 3 * (y : ℤ) ^ 2 =
      (u : ℤ) ^ 2 + (p : ℤ) ^ 3 * (v : ℤ) ^ 2 := by
    exact_mod_cast heq
  have hidZ : ((u : ℤ) - x) * ((u : ℤ) + x) =
      (p : ℤ) ^ 3 * ((y : ℤ) - v) * ((y : ℤ) + v) := by
    nlinarith [heqZ]
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hxu, Nat.cast_sub hvy]
  exact hidZ

/-- The two orientations of the factorization of an equality
`x² + p³y² = u² + p³v²`. -/
def formCollisionCertificate :
    (ℕ × ℕ) × (ℕ × ℕ) → FormCollisionCertificate
  | ((x, y), (u, v)) =>
      if x < u then
        ⟨true, u - x, u + x, y - v, y + v⟩
      else
        ⟨false, x - u, x + u, v - y, v + y⟩

/-- On genuine collisions the difference-and-sum certificate remembers the
ordered pair of lattice points. -/
theorem formCollisionCertificate_injOn
    {p U V : ℕ} (hp : 0 < p) :
    Set.InjOn formCollisionCertificate
      (collisionPairs (specialFormBox U V)
        (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)) := by
  intro z hz w hw hcert
  rcases z with ⟨⟨x, y⟩, ⟨u, v⟩⟩
  rcases w with ⟨⟨x', y'⟩, ⟨u', v'⟩⟩
  change ((x, y), (u, v)) ∈ collisionPairs (specialFormBox U V)
    (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2) at hz
  change ((x', y'), (u', v')) ∈ collisionPairs (specialFormBox U V)
    (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2) at hw
  rw [mem_collisionPairs] at hz hw
  have heq : x ^ 2 + p ^ 3 * y ^ 2 = u ^ 2 + p ^ 3 * v ^ 2 :=
    hz.2.2.2
  have heq' : x' ^ 2 + p ^ 3 * y' ^ 2 = u' ^ 2 + p ^ 3 * v' ^ 2 :=
    hw.2.2.2
  by_cases hxu : x < u
  · have hvy : v < y := specialFormValue_right_lt_of_left_lt hp heq hxu
    rw [formCollisionCertificate, if_pos hxu] at hcert
    by_cases hxu' : x' < u'
    · have hvy' : v' < y' :=
        specialFormValue_right_lt_of_left_lt hp heq' hxu'
      rw [formCollisionCertificate, if_pos hxu'] at hcert
      have h1 := congrArg FormCollisionCertificate.leftDiff hcert
      have h2 := congrArg FormCollisionCertificate.leftSum hcert
      have h3 := congrArg FormCollisionCertificate.rightDiff hcert
      have h4 := congrArg FormCollisionCertificate.rightSum hcert
      simp only at h1 h2 h3 h4
      have hxle : x ≤ u := hxu.le
      have hxle' : x' ≤ u' := hxu'.le
      have hvle : v ≤ y := hvy.le
      have hvle' : v' ≤ y' := hvy'.le
      have hx : x = x' := by omega
      have hy : y = y' := by omega
      have hu : u = u' := by omega
      have hv : v = v' := by omega
      subst x'; subst y'; subst u'; subst v'
      rfl
    · rw [formCollisionCertificate, if_neg hxu'] at hcert
      have h := congrArg FormCollisionCertificate.forward hcert
      simp at h
  · rw [formCollisionCertificate, if_neg hxu] at hcert
    by_cases hxu' : x' < u'
    · rw [formCollisionCertificate, if_pos hxu'] at hcert
      have h := congrArg FormCollisionCertificate.forward hcert
      simp at h
    · rw [formCollisionCertificate, if_neg hxu'] at hcert
      have hux : u < x := by
        have hne : x ≠ u := by
          intro he
          have hy2 : y ^ 2 = v ^ 2 := by
            have hp3 : 0 < p ^ 3 := pow_pos hp 3
            subst u
            nlinarith
          have hy : y = v :=
            Nat.pow_left_injective (by decide : 2 ≠ 0) hy2
          exact hz.2.2.1 (by simp [he, hy])
        omega
      have hux' : u' < x' := by
        have hne : x' ≠ u' := by
          intro he
          have hy2 : y' ^ 2 = v' ^ 2 := by
            have hp3 : 0 < p ^ 3 := pow_pos hp 3
            subst u'
            nlinarith
          have hy : y' = v' :=
            Nat.pow_left_injective (by decide : 2 ≠ 0) hy2
          exact hw.2.2.1 (by simp [he, hy])
        omega
      have hyv : y < v :=
        specialFormValue_right_lt_of_left_lt hp heq.symm hux
      have hyv' : y' < v' :=
        specialFormValue_right_lt_of_left_lt hp heq'.symm hux'
      have h1 := congrArg FormCollisionCertificate.leftDiff hcert
      have h2 := congrArg FormCollisionCertificate.leftSum hcert
      have h3 := congrArg FormCollisionCertificate.rightDiff hcert
      have h4 := congrArg FormCollisionCertificate.rightSum hcert
      simp only at h1 h2 h3 h4
      have hx : x = x' := by omega
      have hy : y = y' := by omega
      have hu : u = u' := by omega
      have hv : v = v' := by omega
      subst x'; subst y'; subst u'; subst v'
      rfl

/-- A collision certificate satisfies the exact product identity. -/
theorem formCollisionCertificate_product
    {p U V : ℕ} (hp : 0 < p)
    {z : (ℕ × ℕ) × (ℕ × ℕ)}
    (hz : z ∈ collisionPairs (specialFormBox U V)
      (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)) :
    (formCollisionCertificate z).leftDiff *
        (formCollisionCertificate z).leftSum =
      p ^ 3 * (formCollisionCertificate z).rightDiff *
        (formCollisionCertificate z).rightSum := by
  rcases z with ⟨⟨x, y⟩, ⟨u, v⟩⟩
  rw [mem_collisionPairs] at hz
  have heq : x ^ 2 + p ^ 3 * y ^ 2 = u ^ 2 + p ^ 3 * v ^ 2 :=
    hz.2.2.2
  by_cases hxu : x < u
  · have hvy : v < y := specialFormValue_right_lt_of_left_lt hp heq hxu
    rw [formCollisionCertificate, if_pos hxu]
    change (u - x) * (u + x) = p ^ 3 * (y - v) * (y + v)
    exact specialFormCollision_product_identity heq hxu.le hvy.le
  · have hux : u < x := by
      have hne : x ≠ u := by
        intro he
        have hy2 : y ^ 2 = v ^ 2 := by
          have hp3 : 0 < p ^ 3 := pow_pos hp 3
          subst u
          nlinarith
        have hy : y = v := Nat.pow_left_injective (by decide : 2 ≠ 0) hy2
        exact hz.2.2.1 (by simp [he, hy])
      omega
    have hyv : y < v :=
      specialFormValue_right_lt_of_left_lt hp heq.symm hux
    rw [formCollisionCertificate, if_neg hxu]
    change (x - u) * (x + u) = p ^ 3 * (v - y) * (v + y)
    exact specialFormCollision_product_identity heq.symm hux.le hyv.le

/-- Positive factor quadruples in the rectangular ranges forced by a form
collision. -/
noncomputable def formFactorQuadruples (D U V : ℕ) :
    Finset (((ℕ × ℕ) × ℕ) × ℕ) := by
  classical
  exact ((((Finset.Icc 1 U ×ˢ Finset.Icc 1 (2 * U)) ×ˢ
    Finset.Icc 1 V) ×ˢ Finset.Icc 1 (2 * V))).filter fun z ↦
      z.1.1.1 * z.1.1.2 = D * z.1.2 * z.2

@[simp] theorem mem_formFactorQuadruples {D U V a b c d : ℕ} :
    (((a, b), c), d) ∈ formFactorQuadruples D U V ↔
      a ∈ Finset.Icc 1 U ∧ b ∈ Finset.Icc 1 (2 * U) ∧
      c ∈ Finset.Icc 1 V ∧ d ∈ Finset.Icc 1 (2 * V) ∧
      a * b = D * c * d := by
  classical
  simp [formFactorQuadruples, and_assoc]

def formCollisionCertificateCode : FormCollisionCertificate →
    Bool × (((ℕ × ℕ) × ℕ) × ℕ)
  | ⟨o, a, b, c, d⟩ => (o, (((a, b), c), d))

theorem formCollisionCertificateCode_injective :
    Function.Injective formCollisionCertificateCode := by
  intro a b h
  cases a
  cases b
  simp only [formCollisionCertificateCode, Prod.mk.injEq] at h
  aesop

/-- Every genuine collision code lies in one of two orientations of the
bounded factor-quadruple set. -/
theorem formCollisionCertificateCode_mem
    {p U V : ℕ} (hp : 0 < p)
    {z : (ℕ × ℕ) × (ℕ × ℕ)}
    (hz : z ∈ collisionPairs (specialFormBox U V)
      (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)) :
    (formCollisionCertificateCode (formCollisionCertificate z)).2 ∈
      formFactorQuadruples (p ^ 3) U V := by
  rcases z with ⟨⟨x, y⟩, ⟨u, v⟩⟩
  change ((x, y), (u, v)) ∈ collisionPairs (specialFormBox U V)
    (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2) at hz
  rw [mem_collisionPairs] at hz
  have hxy := hz.1
  have huv := hz.2.1
  rw [specialFormBox, Finset.mem_product] at hxy huv
  have hx := Finset.mem_Icc.mp hxy.1
  have hy := Finset.mem_Icc.mp hxy.2
  have hu := Finset.mem_Icc.mp huv.1
  have hv := Finset.mem_Icc.mp huv.2
  change 1 ≤ x ∧ x ≤ U at hx
  change 1 ≤ y ∧ y ≤ V at hy
  change 1 ≤ u ∧ u ≤ U at hu
  change 1 ≤ v ∧ v ≤ V at hv
  have heq : x ^ 2 + p ^ 3 * y ^ 2 = u ^ 2 + p ^ 3 * v ^ 2 :=
    hz.2.2.2
  rw [mem_formFactorQuadruples]
  by_cases hxu : x < u
  · have hvy : v < y := specialFormValue_right_lt_of_left_lt hp heq hxu
    rw [formCollisionCertificate, if_pos hxu, formCollisionCertificateCode]
    change (u - x) ∈ Finset.Icc 1 U ∧
      (u + x) ∈ Finset.Icc 1 (2 * U) ∧
      (y - v) ∈ Finset.Icc 1 V ∧
      (y + v) ∈ Finset.Icc 1 (2 * V) ∧
      (u - x) * (u + x) = p ^ 3 * (y - v) * (y + v)
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt hxu,
          (Nat.sub_le u x).trans hu.2⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt hvy,
          (Nat.sub_le y v).trans hy.2⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    exact specialFormCollision_product_identity heq hxu.le hvy.le
  · have hux : u < x := by
      have hne : x ≠ u := by
        intro he
        have hy2 : y ^ 2 = v ^ 2 := by
          have hp3 : 0 < p ^ 3 := pow_pos hp 3
          subst u
          nlinarith
        have hyv : y = v :=
          Nat.pow_left_injective (by decide : 2 ≠ 0) hy2
        exact hz.2.2.1 (by simp [he, hyv])
      omega
    have hyv : y < v :=
      specialFormValue_right_lt_of_left_lt hp heq.symm hux
    rw [formCollisionCertificate, if_neg hxu, formCollisionCertificateCode]
    change (x - u) ∈ Finset.Icc 1 U ∧
      (x + u) ∈ Finset.Icc 1 (2 * U) ∧
      (v - y) ∈ Finset.Icc 1 V ∧
      (v + y) ∈ Finset.Icc 1 (2 * V) ∧
      (x - u) * (x + u) = p ^ 3 * (v - y) * (v + y)
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt hux,
          (Nat.sub_le x u).trans hx.2⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt hyv,
          (Nat.sub_le v y).trans hv.2⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    exact specialFormCollision_product_identity heq.symm hux.le hyv.le

/-- Ordered collisions inject into two copies of the finite
factor-quadruple set. -/
theorem collisionPairs_card_le_two_mul_formFactorQuadruples
    (p U V : ℕ) (hp : 0 < p) :
    (collisionPairs (specialFormBox U V)
      (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)).card ≤
      2 * (formFactorQuadruples (p ^ 3) U V).card := by
  classical
  let S := collisionPairs (specialFormBox U V)
    (fun z ↦ z.1 ^ 2 + p ^ 3 * z.2 ^ 2)
  let code := fun z ↦
    formCollisionCertificateCode (formCollisionCertificate z)
  have hinj : Set.InjOn code (S : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    intro z hz w hw h
    apply formCollisionCertificate_injOn hp hz hw
    exact formCollisionCertificateCode_injective h
  have hsub : S.image code ⊆
      (Finset.univ : Finset Bool) ×ˢ
        formFactorQuadruples (p ^ 3) U V := by
    intro c hc
    rw [Finset.mem_image] at hc
    rcases hc with ⟨z, hz, rfl⟩
    rw [Finset.mem_product]
    exact ⟨Finset.mem_univ _, formCollisionCertificateCode_mem hp hz⟩
  calc
    S.card = (S.image code).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((Finset.univ : Finset Bool) ×ˢ
          formFactorQuadruples (p ^ 3) U V).card := Finset.card_le_card hsub
    _ = 2 * (formFactorQuadruples (p ^ 3) U V).card := by simp

theorem specialFamilyValues_subset_A {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    specialFamilyValues P N ⊆
      (Finset.Icc 1 N).filter IsSumOfTwoSquarefull := by
  classical
  intro n hn
  rw [specialFamilyValues, Finset.mem_biUnion] at hn
  rcases hn with ⟨p, hpP, hnp⟩
  exact specialFormValues_subset_A (hP p hpP) hnp

theorem specialFamilyValues_card_le_A {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    (specialFamilyValues P N).card ≤ A N := by
  classical
  exact Finset.card_le_card (specialFamilyValues_subset_A hP)

/-- The depth-two Bonferroni inequality for a finite family of finite sets.
The second sum is over ordered distinct pairs; this deliberately counts each
intersection twice, a harmless weakening which avoids choosing an order on the
index type and is exactly strong enough for the analytic application. -/
theorem card_biUnion_lower_bound_orderedPairs
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (P : Finset ι) (S : ι → Finset α) :
    (∑ i ∈ P, ((S i).card : ℝ)) -
        ∑ i ∈ P, ∑ j ∈ P.filter (fun j => j ≠ i),
          (((S i ∩ S j).card : ℕ) : ℝ) ≤
      ((P.biUnion S).card : ℝ) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
      let U : Finset α := P.biUnion S
      have hUnionInter :
          (((U ∩ S a).card : ℕ) : ℝ) ≤
            ∑ i ∈ P, (((S i ∩ S a).card : ℕ) : ℝ) := by
        have hsubset : U ∩ S a ⊆ P.biUnion fun i => S i ∩ S a := by
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxU, hxa⟩
          rcases Finset.mem_biUnion.mp hxU with ⟨i, hiP, hxi⟩
          exact Finset.mem_biUnion.mpr
            ⟨i, hiP, Finset.mem_inter.mpr ⟨hxi, hxa⟩⟩
        exact_mod_cast (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
      have hnonneg :
          0 ≤ ∑ i ∈ P, (((S a ∩ S i).card : ℕ) : ℝ) := by
        exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg (S a ∩ S i).card
      have hsymm :
          (∑ i ∈ P, (((S i ∩ S a).card : ℕ) : ℝ)) =
            ∑ i ∈ P, (((S a ∩ S i).card : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.inter_comm]
      have hcardUnion :
          (((U ∪ S a).card : ℕ) : ℝ) =
            (U.card : ℝ) + (S a).card - (U ∩ S a).card := by
        have h := Finset.card_union_add_card_inter U (S a)
        have h' :
            (((U ∪ S a).card : ℕ) : ℝ) + (U ∩ S a).card =
              (U.card : ℝ) + (S a).card := by
          exact_mod_cast h
        linarith
      have hfilterSelf :
          (insert a P).filter (fun j => j ≠ a) = P := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj | hj, hne⟩
          · exact (hne hj).elim
          · exact hj
        · intro hj
          exact ⟨Or.inr hj, fun hja => ha (hja ▸ hj)⟩
      have hpairExpand :
          (∑ i ∈ insert a P,
              ∑ j ∈ (insert a P).filter (fun j => j ≠ i),
                (((S i ∩ S j).card : ℕ) : ℝ)) =
            (∑ j ∈ P, (((S a ∩ S j).card : ℕ) : ℝ)) +
              ∑ i ∈ P,
                ((((S i ∩ S a).card : ℕ) : ℝ) +
                  ∑ j ∈ P.filter (fun j => j ≠ i),
                    (((S i ∩ S j).card : ℕ) : ℝ)) := by
        rw [Finset.sum_insert ha, hfilterSelf]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hai : a ≠ i := fun h => ha (h ▸ hi)
        have hfilter :
            (insert a P).filter (fun j => j ≠ i) =
              insert a (P.filter fun j => j ≠ i) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          aesop
        rw [hfilter, Finset.sum_insert (by simp [ha])]
      have ih' :
          (∑ i ∈ P, ((S i).card : ℝ)) -
              ∑ i ∈ P, ∑ j ∈ P.filter (fun j => j ≠ i),
                (((S i ∩ S j).card : ℕ) : ℝ) ≤ (U.card : ℝ) := by
        simpa [U] using ih
      rw [Finset.sum_insert ha, hpairExpand, Finset.biUnion_insert,
        Finset.union_comm, hcardUnion]
      rw [Finset.sum_add_distrib]
      rw [hsymm]
      linarith

/-! ### The lower half of the finite class-group lemma -/

section SignedProductBonferroni

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

theorem signedProduct_fiber_card {k : ℕ} (hk : 0 < k)
    (sigma : Fin k → Bool) (c : G) :
    (signedProductFiber sigma c).card = (Fintype.card G) ^ (k - 1) := by
  have h := signedProduct_fiber_card_mul hk sigma c
  have h' : (signedProductFiber sigma c).card * Fintype.card G =
      (Fintype.card G) ^ k := by
    change (Finset.univ.filter fun x : Fin k → G ↦
      signedProductHom sigma x = c).card * Fintype.card G = _
    rw [← Fintype.card_subtype]
    exact h
  have hG : 0 < Fintype.card G := Fintype.card_pos
  apply Nat.eq_of_mul_eq_mul_right hG
  rw [h']
  rw [← pow_succ]
  congr
  omega

theorem signedProductPairFiber_card {k : ℕ} (hk : 2 ≤ k)
    (sigma tau : Fin k → Bool) (c : G)
    {i j : Fin k} (hsame : sigma i = tau i)
    (hdiff : sigma j ≠ tau j) :
    (signedProductPairFiber sigma tau c).card =
      (Fintype.card G) ^ (k - 2) *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) := by
  have h := signedProductPairFiber_card_mul_groupSq
    sigma tau c hsame hdiff
  have hG : 0 < (Fintype.card G) ^ 2 := pow_pos Fintype.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hG
  rw [h]
  calc
    (Fintype.card G) ^ k *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) =
        ((Fintype.card G) ^ (k - 2) * (Fintype.card G) ^ 2) *
          Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    _ = ((Fintype.card G) ^ (k - 2) *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) *
          (Fintype.card G) ^ 2 := by ring

theorem signedProductFiber_inter {k : ℕ}
    (sigma tau : Fin k → Bool) (c : G) :
    signedProductFiber sigma c ∩ signedProductFiber tau c =
      signedProductPairFiber sigma tau c := by
  ext x
  rw [signedProductFiber, signedProductFiber, signedProductPairFiber,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_filter,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, signedProductPairHom_apply,
    signedProductHom_apply, Prod.mk.injEq]

/-- Sign patterns with the first coordinate fixed.  This deletes complementary
pairs while retaining exactly `2^k` patterns in dimension `k+1`. -/
noncomputable def anchoredSignPatterns (k : ℕ) :
    Finset (Fin (k + 1) → Bool) :=
  Finset.univ.filter fun sigma ↦ sigma 0 = false

theorem anchoredSignPatterns_card (k : ℕ) :
    (anchoredSignPatterns k).card = 2 ^ k := by
  classical
  let e : {sigma : Fin (k + 1) → Bool // sigma 0 = false} ≃
      (Fin k → Bool) := {
    toFun := fun (sigma : {sigma : Fin (k + 1) → Bool //
        sigma 0 = false}) ↦ Fin.tail sigma.1
    invFun := fun (tail : Fin k → Bool) ↦
      ⟨Fin.cons false tail, by simp⟩
    left_inv := fun sigma ↦ by
      apply Subtype.ext
      change Fin.cons false (Fin.tail sigma.1) = sigma.1
      calc
        Fin.cons false (Fin.tail sigma.1) =
            Fin.cons (sigma.1 0) (Fin.tail sigma.1) := by
          congr
          exact sigma.2.symm
        _ = sigma.1 := Fin.cons_self_tail sigma.1
    right_inv := fun tail ↦ by
      funext i
      simp }
  change (Finset.univ.filter fun sigma : Fin (k + 1) → Bool ↦
    sigma 0 = false).card = _
  rw [← Fintype.card_subtype, Fintype.card_congr e,
    Fintype.card_fun, Fintype.card_fin]
  simp

theorem mem_anchoredSignPatterns_agree_zero {k : ℕ}
    {sigma tau : Fin (k + 1) → Bool}
    (hsigma : sigma ∈ anchoredSignPatterns k)
    (htau : tau ∈ anchoredSignPatterns k) : sigma 0 = tau 0 := by
  rw [anchoredSignPatterns, Finset.mem_filter] at hsigma htau
  rw [hsigma.2, htau.2]

theorem exists_sign_difference {k : ℕ}
    {sigma tau : Fin k → Bool} (hne : sigma ≠ tau) :
    ∃ j : Fin k, sigma j ≠ tau j := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hne (funext h)

/-- Division-free Bonferroni form of the lower half of Blomer's finite-group
lemma, using the `2^k` sign patterns anchored at the first coordinate. -/
theorem signedClassTuples_bonferroni_lower {k : ℕ} (hk : 1 ≤ k) (c : G) :
    ((2 ^ k * (Fintype.card G) ^ k : ℕ) : ℝ) -
        (((2 ^ k) * (2 ^ k - 1) *
          ((Fintype.card G) ^ (k - 1) *
            Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) ≤
      ((signedClassTuples (k + 1) c).card : ℝ) := by
  classical
  let P := anchoredSignPatterns k
  let S : (Fin (k + 1) → Bool) → Finset (Fin (k + 1) → G) :=
    fun sigma ↦ signedProductFiber sigma c
  have hsingle : ∀ sigma ∈ P, (S sigma).card = (Fintype.card G) ^ k := by
    intro sigma hsigma
    dsimp [S]
    rw [signedProduct_fiber_card (by omega : 0 < k + 1)]
    congr
  have hpair : ∀ sigma ∈ P, ∀ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
      (S sigma ∩ S tau).card =
        (Fintype.card G) ^ (k - 1) *
          Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) := by
    intro sigma hsigma tau htau
    have htauP : tau ∈ P := (Finset.mem_filter.mp htau).1
    have hne : tau ≠ sigma := (Finset.mem_filter.mp htau).2
    have hsame : sigma 0 = tau 0 :=
      mem_anchoredSignPatterns_agree_zero hsigma htauP
    obtain ⟨j, hj⟩ := exists_sign_difference hne.symm
    dsimp [S]
    rw [signedProductFiber_inter]
    rw [signedProductPairFiber_card (by omega : 2 ≤ k + 1)
      sigma tau c hsame hj]
    rw [show k + 1 - 2 = k - 1 by omega]
  have hbonf := card_biUnion_lower_bound_orderedPairs P S
  have hsub : P.biUnion S ⊆ signedClassTuples (k + 1) c := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨sigma, hsigma, hx⟩
    rw [signedClassTuples, Finset.mem_biUnion]
    exact ⟨sigma, Finset.mem_univ _, hx⟩
  have hcard : ((P.biUnion S).card : ℝ) ≤
      ((signedClassTuples (k + 1) c).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hPcard : P.card = 2 ^ k := anchoredSignPatterns_card k
  have hpairSum :
      (∑ sigma ∈ P, ∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
        (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
      (((2 ^ k) * (2 ^ k - 1) *
        ((Fintype.card G) ^ (k - 1) *
          Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) := by
    let q : ℕ := (Fintype.card G) ^ (k - 1) *
      Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))
    have hinner : ∀ sigma ∈ P,
        (∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
          (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
        (((P.card - 1) * q : ℕ) : ℝ) := by
      intro sigma hsigma
      have hfilter : P.filter (fun tau ↦ tau ≠ sigma) = P.erase sigma := by
        ext tau
        simp [and_comm]
      calc
        (∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
            (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
            ∑ _tau ∈ P.filter (fun tau ↦ tau ≠ sigma), (q : ℝ) := by
              apply Finset.sum_congr rfl
              intro tau htau
              rw [hpair sigma hsigma tau htau]
        _ = (((P.card - 1) * q : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hfilter,
            Finset.card_erase_of_mem hsigma]
          norm_cast
    calc
      (∑ sigma ∈ P, ∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
          (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
          ∑ _sigma ∈ P, ((((P.card - 1) * q : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            exact hinner sigma hsigma
      _ = (((P.card * (P.card - 1) * q : ℕ) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
        ring
      _ = (((2 ^ k) * (2 ^ k - 1) *
          ((Fintype.card G) ^ (k - 1) *
            Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) := by
        rw [hPcard]
  have hsingleSum :
      (∑ sigma ∈ P, ((S sigma).card : ℝ)) =
        ((2 ^ k * (Fintype.card G) ^ k : ℕ) : ℝ) := by
    calc
      (∑ sigma ∈ P, ((S sigma).card : ℝ)) =
          ∑ _sigma ∈ P, (((Fintype.card G) ^ k : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            rw [hsingle sigma hsigma]
      _ = ((2 ^ k * (Fintype.card G) ^ k : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hPcard]
        norm_cast
  calc
    ((2 ^ k * (Fintype.card G) ^ k : ℕ) : ℝ) -
          (((2 ^ k) * (2 ^ k - 1) *
            ((Fintype.card G) ^ (k - 1) *
              Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) =
        (∑ sigma ∈ P, ((S sigma).card : ℝ)) -
          ∑ sigma ∈ P, ∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
            (((S sigma ∩ S tau).card : ℕ) : ℝ) := by
              rw [hsingleSum, hpairSum]
    _ ≤ ((P.biUnion S).card : ℝ) := hbonf
    _ ≤ ((signedClassTuples (k + 1) c).card : ℝ) := hcard

/-- The same Bonferroni estimate for an arbitrary subset of the anchored
patterns.  This is the form used to balance the main term against pair
intersections in the saturated range. -/
theorem signedClassTuples_bonferroni_lower_of_patterns {k : ℕ}
    (hk : 1 ≤ k) (c : G) (P : Finset (Fin (k + 1) → Bool))
    (hP : P ⊆ anchoredSignPatterns k) :
    ((P.card * (Fintype.card G) ^ k : ℕ) : ℝ) -
        ((P.card * (P.card - 1) *
          ((Fintype.card G) ^ (k - 1) *
            Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) ≤
      ((signedClassTuples (k + 1) c).card : ℝ) := by
  classical
  let S : (Fin (k + 1) → Bool) → Finset (Fin (k + 1) → G) :=
    fun sigma ↦ signedProductFiber sigma c
  have hsingle : ∀ sigma ∈ P, (S sigma).card = (Fintype.card G) ^ k := by
    intro sigma hsigma
    dsimp [S]
    rw [signedProduct_fiber_card (by omega : 0 < k + 1)]
    congr
  have hpair : ∀ sigma ∈ P,
      ∀ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
      (S sigma ∩ S tau).card =
        (Fintype.card G) ^ (k - 1) *
          Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) := by
    intro sigma hsigma tau htau
    have htauP : tau ∈ P := (Finset.mem_filter.mp htau).1
    have hne : tau ≠ sigma := (Finset.mem_filter.mp htau).2
    have hsame : sigma 0 = tau 0 :=
      mem_anchoredSignPatterns_agree_zero (hP hsigma) (hP htauP)
    obtain ⟨j, hj⟩ := exists_sign_difference hne.symm
    dsimp [S]
    rw [signedProductFiber_inter]
    rw [signedProductPairFiber_card (by omega : 2 ≤ k + 1)
      sigma tau c hsame hj]
    rw [show k + 1 - 2 = k - 1 by omega]
  have hbonf := card_biUnion_lower_bound_orderedPairs P S
  have hsub : P.biUnion S ⊆ signedClassTuples (k + 1) c := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨sigma, hsigma, hx⟩
    rw [signedClassTuples, Finset.mem_biUnion]
    exact ⟨sigma, Finset.mem_univ _, hx⟩
  have hcard : ((P.biUnion S).card : ℝ) ≤
      ((signedClassTuples (k + 1) c).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  let q : ℕ := (Fintype.card G) ^ (k - 1) *
    Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))
  have hpairSum :
      (∑ sigma ∈ P, ∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
        (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
      ((P.card * (P.card - 1) * q : ℕ) : ℝ) := by
    have hinner : ∀ sigma ∈ P,
        (∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
          (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
        (((P.card - 1) * q : ℕ) : ℝ) := by
      intro sigma hsigma
      have hfilter : P.filter (fun tau ↦ tau ≠ sigma) = P.erase sigma := by
        ext tau
        simp [and_comm]
      calc
        (∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
            (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
            ∑ _tau ∈ P.filter (fun tau ↦ tau ≠ sigma), (q : ℝ) := by
              apply Finset.sum_congr rfl
              intro tau htau
              rw [hpair sigma hsigma tau htau]
        _ = (((P.card - 1) * q : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hfilter,
            Finset.card_erase_of_mem hsigma]
          norm_cast
    calc
      (∑ sigma ∈ P, ∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
          (((S sigma ∩ S tau).card : ℕ) : ℝ)) =
          ∑ _sigma ∈ P, ((((P.card - 1) * q : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            exact hinner sigma hsigma
      _ = ((P.card * (P.card - 1) * q : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
        ring
  have hsingleSum :
      (∑ sigma ∈ P, ((S sigma).card : ℝ)) =
        ((P.card * (Fintype.card G) ^ k : ℕ) : ℝ) := by
    calc
      (∑ sigma ∈ P, ((S sigma).card : ℝ)) =
          ∑ _sigma ∈ P, (((Fintype.card G) ^ k : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            rw [hsingle sigma hsigma]
      _ = ((P.card * (Fintype.card G) ^ k : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
  calc
    ((P.card * (Fintype.card G) ^ k : ℕ) : ℝ) -
          ((P.card * (P.card - 1) *
            ((Fintype.card G) ^ (k - 1) *
              Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) =
        (∑ sigma ∈ P, ((S sigma).card : ℝ)) -
          ∑ sigma ∈ P, ∑ tau ∈ P.filter (fun tau ↦ tau ≠ sigma),
            (((S sigma ∩ S tau).card : ℕ) : ℝ) := by
      dsimp [q] at hpairSum
      rw [hsingleSum, hpairSum]
    _ ≤ ((P.biUnion S).card : ℝ) := hbonf
    _ ≤ ((signedClassTuples (k + 1) c).card : ℝ) := hcard

/-- Choosing any admissible number `r` of anchored patterns leaves at least
half of their total single-fiber mass once the pair intersections are small
enough. -/
theorem signedClassTuples_lower_of_pattern_count {k r : ℕ}
    (hk : 1 ≤ k) (c : G) (hr : r ≤ 2 ^ k)
    (hsmall : 2 * (r - 1) *
        Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) ≤
      Fintype.card G) :
    (((r * (Fintype.card G) ^ k : ℕ) : ℝ) / 2) ≤
      ((signedClassTuples (k + 1) c).card : ℝ) := by
  classical
  obtain ⟨P, hP, hPcard⟩ :=
    (anchoredSignPatterns k).exists_subset_card_eq
      (by simpa [anchoredSignPatterns_card] using hr)
  have hbonf := signedClassTuples_bonferroni_lower_of_patterns
    (G := G) hk c P hP
  rw [hPcard] at hbonf
  have hpow : (Fintype.card G) ^ k =
      (Fintype.card G) ^ (k - 1) * Fintype.card G := by
    rw [← pow_succ]
    congr
    omega
  have herrorNat :
      2 * (r * (r - 1) *
        ((Fintype.card G) ^ (k - 1) *
          Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)))) ≤
        r * (Fintype.card G) ^ k := by
    have hm := Nat.mul_le_mul_left
      (r * (Fintype.card G) ^ (k - 1)) hsmall
    rw [hpow]
    nlinarith
  have herrorReal :
      2 * ((r * (r - 1) *
        ((Fintype.card G) ^ (k - 1) *
          Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) ≤
        ((r * (Fintype.card G) ^ k : ℕ) : ℝ) := by
    exact_mod_cast herrorNat
  linarith

/-- Number of sign patterns selected in the balanced Bonferroni argument. -/
noncomputable def balancedSignCount (H t k : ℕ) : ℕ :=
  min (2 ^ k) (max 1 (H / (2 * t)))

theorem balancedSignCount_properties (H t k : ℕ) (ht : 0 < t) :
    balancedSignCount H t k ≤ 2 ^ k ∧
      2 * (balancedSignCount H t k - 1) * t ≤ H ∧
      (balancedSignCount H t k = 2 ^ k ∨
        H ≤ 4 * balancedSignCount H t k * t) := by
  let d := 2 * t
  have hd : 0 < d := by dsimp [d]; omega
  let s := max 1 (H / d)
  let r := min (2 ^ k) s
  have hpow : 1 ≤ 2 ^ k := one_le_pow₀ (by decide)
  have hs : 1 ≤ s := le_max_left _ _
  have hrpos : 1 ≤ r := le_min hpow hs
  have hrpow : r ≤ 2 ^ k := min_le_left _ _
  have hrs : r ≤ s := min_le_right _ _
  have hsmall : 2 * (r - 1) * t ≤ H := by
    by_cases hHd : H < d
    · have hdiv : H / d = 0 := Nat.div_eq_of_lt hHd
      have hsone : s = 1 := by simp [s, hdiv]
      have hrone : r = 1 := le_antisymm (hrs.trans_eq hsone) hrpos
      simp [hrone]
    · have hdH : d ≤ H := by omega
      have hdivpos : 1 ≤ H / d := (Nat.one_le_div_iff hd).2 hdH
      have hsdiv : s = H / d := max_eq_right hdivpos
      have hrdiv : r ≤ H / d := hrs.trans_eq hsdiv
      have hrmul : r * d ≤ H := (Nat.le_div_iff_mul_le hd).mp hrdiv
      calc
        2 * (r - 1) * t = (r - 1) * d := by dsimp [d]; ring
        _ ≤ r * d := Nat.mul_le_mul_right d (Nat.sub_le r 1)
        _ ≤ H := hrmul
  have hbalance : r = 2 ^ k ∨ H ≤ 4 * r * t := by
    by_cases hrpowEq : r = 2 ^ k
    · exact Or.inl hrpowEq
    · right
      have hrEq : r = s := min_eq_right (by
        have := min_choice (2 ^ k) s
        omega)
      by_cases hHd : H < d
      · have hdiv : H / d = 0 := Nat.div_eq_of_lt hHd
        have hsone : s = 1 := by simp [s, hdiv]
        rw [hrEq, hsone]
        dsimp [d] at hHd
        omega
      · have hdH : d ≤ H := by omega
        have hdivpos : 1 ≤ H / d := (Nat.one_le_div_iff hd).2 hdH
        have hsdiv : s = H / d := max_eq_right hdivpos
        have hlt : H < (H / d + 1) * d :=
          (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (H / d))
        rw [hrEq, hsdiv]
        have hadd : H / d + 1 ≤ 2 * (H / d) := by omega
        calc
          H ≤ (H / d + 1) * d := hlt.le
          _ ≤ (2 * (H / d)) * d := Nat.mul_le_mul_right d hadd
          _ = 4 * (H / d) * t := by dsimp [d]; ring
  simpa only [balancedSignCount, r, s, d] using
    ⟨hrpow, hsmall, hbalance⟩

/-- Blomer's finite class-group lower bound, with an explicit absolute
constant `1/8`.  Its numerator is the division-free version of
`|G|^(k+1) * min (1/|G/G²|) (2^k/|G|)`. -/
theorem signedClassTuples_blomer_lower {k : ℕ}
    (hk : 1 ≤ k) (c : G) :
    (((Fintype.card G) ^ k *
        min (Fintype.card G)
          (2 ^ k * Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))) : ℕ) : ℝ) /
        (8 * (Nat.card (G ⧸ (classSquareSubgroup : Subgroup G)) : ℝ)) ≤
      ((signedClassTuples (k + 1) c).card : ℝ) := by
  let H := Fintype.card G
  let t := Nat.card (G ⧸ (classSquareSubgroup : Subgroup G))
  let r := balancedSignCount H t k
  have ht : 0 < t := by
    dsimp [t]
    exact Nat.card_pos
  obtain ⟨hr, hsmall, hbalance⟩ := balancedSignCount_properties H t k ht
  change r ≤ 2 ^ k at hr
  change 2 * (r - 1) * t ≤ H at hsmall
  change r = 2 ^ k ∨ H ≤ 4 * r * t at hbalance
  have hmain := signedClassTuples_lower_of_pattern_count
    (G := G) hk c hr hsmall
  have hmin : min H (2 ^ k * t) ≤ 4 * r * t := by
    rcases hbalance with hrEq | hH
    · rw [hrEq]
      exact (min_le_right H (2 ^ k * t)).trans <| by
        calc
          2 ^ k * t = 1 * (2 ^ k * t) := by ring
          _ ≤ 4 * (2 ^ k * t) := Nat.mul_le_mul_right _ (by norm_num)
          _ = 4 * 2 ^ k * t := by ring
    · exact (min_le_left H (2 ^ k * t)).trans hH
  have hmul : H ^ k * min H (2 ^ k * t) ≤
      H ^ k * (4 * r * t) := Nat.mul_le_mul_left _ hmin
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  change (((H ^ k * min H (2 ^ k * t) : ℕ) : ℝ) /
      (8 * (t : ℝ))) ≤ _
  apply le_trans ?_ hmain
  calc
    (((H ^ k * min H (2 ^ k * t) : ℕ) : ℝ) /
        (8 * (t : ℝ))) ≤
      (((H ^ k * (4 * r * t) : ℕ) : ℝ) /
        (8 * (t : ℝ))) := by
          gcongr
    _ = (((r * H ^ k : ℕ) : ℝ) / 2) := by
      push_cast
      field_simp
      ring

end SignedProductBonferroni

/-- Exact finite-family lower bound which isolates the two analytic terms in
Odoni's and Blomer's arguments. -/
theorem specialFamily_bonferroni_lower_bound
    (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (specialFormCount p N : ℝ)) -
        ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
          (specialPairCount p q N : ℝ) ≤ (A N : ℝ) := by
  calc
    (∑ p ∈ P, (specialFormCount p N : ℝ)) -
          ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
            (specialPairCount p q N : ℝ) ≤
        ((specialFamilyValues P N).card : ℝ) := by
      simpa [specialFormCount, specialPairCount, specialFamilyValues] using
        card_biUnion_lower_bound_orderedPairs P (fun p => specialFormValues p N)
    _ ≤ (A N : ℝ) := by
      exact_mod_cast specialFamilyValues_card_le_A hP

/-! ## Local obstructions for the pair term -/

/-- The diagonal form `x² + d y²` is anisotropic modulo `l` when divisibility
of a value by `l` forces both variables to be divisible by `l`.  For an odd
prime not dividing `d`, this is equivalent to `-d` being a quadratic
nonresidue modulo `l`; the divisibility formulation is more convenient for
the descent argument and avoids choosing a particular character API. -/
def FormAnisotropicAt (d l : ℕ) : Prop :=
  ∀ x y : ℕ, l ∣ x ^ 2 + d * y ^ 2 → l ∣ x ∧ l ∣ y

/-- Character-theoretic version of the local obstruction: `-d` is not a
square in the prime field of modulus `l`. -/
def IsQuadraticObstruction (d l : ℕ) : Prop :=
  ¬ IsSquare (-(d : ZMod l))

/-- A chosen square root of `-p³` at every locally allowed modulus.  It is
used only through `specialSplitRoot_sq`; the arbitrary choice never enters
the resulting ideal class. -/
noncomputable def specialSplitRoot (p q : ℕ)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) : ZMod q :=
  Classical.choose (Classical.not_not.mp h)

theorem specialSplitRoot_sq (p q : ℕ)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) :
    specialSplitRoot p q h * specialSplitRoot p q h =
      ((-(p : ℤ) ^ 3 : ℤ) : ZMod q) := by
  have hs := Classical.choose_spec (Classical.not_not.mp h)
  calc
    specialSplitRoot p q h * specialSplitRoot p q h =
        -(p ^ 3 : ZMod q) := by
      simpa only [specialSplitRoot, Nat.cast_pow] using hs.symm
    _ = ((-(p : ℤ) ^ 3 : ℤ) : ZMod q) := by push_cast; ring

/-- At a distinct odd prime, a split root of `-p³` is simple. -/
theorem specialSplitRoot_coprime_two_val
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) :
    Nat.Coprime q (2 * (specialSplitRoot p q h).val) := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hq_not_dvd_two : ¬ q ∣ 2 := by
    intro hdiv
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hdiv)
  have hq_not_dvd_val : ¬ q ∣ (specialSplitRoot p q h).val := by
    intro hdiv
    have hroot0 : specialSplitRoot p q h = 0 := by
      rw [← ZMod.natCast_zmod_val (specialSplitRoot p q h),
        ZMod.natCast_eq_zero_iff]
      exact hdiv
    have hpcase : ((p : ℕ) : ZMod q) = 0 := by
      have hs := specialSplitRoot_sq p q h
      rw [hroot0, zero_mul] at hs
      have hpow : ((p : ℕ) : ZMod q) ^ 3 = 0 := by
        simpa only [Int.cast_neg, Int.cast_pow, Int.cast_natCast,
          neg_eq_zero] using hs.symm
      exact eq_zero_of_pow_eq_zero hpow
    have hdivp : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp hpcase
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdivp)
  exact hq.coprime_iff_not_dvd.mpr fun hdiv =>
    (hq.dvd_mul.mp hdiv).elim hq_not_dvd_two hq_not_dvd_val

/-! ## The split-ideal class bridge for `x² + p³y²` -/

theorem specialDiscriminant_neg (p : ℕ) (hp : p.Prime) :
    (-(p : ℤ) ^ 3 : ℤ) < 0 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rw [neg_lt_zero]
  positivity

noncomputable instance specialZsqrtdIsDomain (p : ℕ) [Fact p.Prime] :
    IsDomain (Zsqrtd (-(p : ℤ) ^ 3)) :=
  zsqrtdIsDomain (-(p : ℤ) ^ 3) (specialDiscriminant_neg p Fact.out)

noncomputable def specialSplitPrimeUnit
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) :
    (FractionalIdeal (Zsqrtd (-(p : ℤ) ^ 3))⁰
      (FractionRing (Zsqrtd (-(p : ℤ) ^ 3))))ˣ := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact splitPrimeIdealUnit (-(p : ℤ) ^ 3) q
    (specialSplitRoot p q h) (specialSplitRoot_sq p q h)
    (specialSplitRoot_coprime_two_val Fact.out hq hq2 hqp h)

noncomputable def specialSplitPrimeClass
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) :
    ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)) :=
  ClassGroup.mk (FractionRing (Zsqrtd (-(p : ℤ) ^ 3)))
    (specialSplitPrimeUnit p q hq hq2 hqp h)

noncomputable def specialOrientedSplitUnit
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    (FractionalIdeal (Zsqrtd (-(p : ℤ) ^ 3))⁰
      (FractionRing (Zsqrtd (-(p : ℤ) ^ 3))))ˣ := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact orientedSplitIdealUnit (-(p : ℤ) ^ 3) q
    (specialSplitRoot p q h) (specialSplitRoot_sq p q h)
    (specialSplitRoot_coprime_two_val Fact.out hq hq2 hqp h) b

noncomputable def specialOrientedSplitIdeal
    (p q : ℕ) (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    Ideal (Zsqrtd (-(p : ℤ) ^ 3)) :=
  orientedSplitIdeal (-(p : ℤ) ^ 3) q (specialSplitRoot p q h) b

theorem specialOrientedSplitUnit_coe
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    ((specialOrientedSplitUnit p q hq hq2 hqp h b :
        (FractionalIdeal (Zsqrtd (-(p : ℤ) ^ 3))⁰
          (FractionRing (Zsqrtd (-(p : ℤ) ^ 3))))ˣ) :
      FractionalIdeal (Zsqrtd (-(p : ℤ) ^ 3))⁰
        (FractionRing (Zsqrtd (-(p : ℤ) ^ 3)))) =
      specialOrientedSplitIdeal p q h b := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact orientedSplitIdealUnit_coe (-(p : ℤ) ^ 3) q
    (specialSplitRoot p q h) (specialSplitRoot_sq p q h)
    (specialSplitRoot_coprime_two_val Fact.out hq hq2 hqp h) b

theorem specialOrientedSplitUnit_class
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    ClassGroup.mk (FractionRing (Zsqrtd (-(p : ℤ) ^ 3)))
        (specialOrientedSplitUnit p q hq hq2 hqp h b) =
      if b then (specialSplitPrimeClass p q hq hq2 hqp h)⁻¹
      else specialSplitPrimeClass p q hq hq2 hqp h := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact orientedSplitIdeal_class (-(p : ℤ) ^ 3) q
    (specialSplitRoot p q h) (specialSplitRoot_sq p q h)
    (specialSplitRoot_coprime_two_val Fact.out hq hq2 hqp h) b

/-- A squarefree product of distinct locally split primes is represented by
`x² + p³y²` whenever some orientation of its split prime ideals has
trivial class. -/
theorem exists_specialForm_representation_of_signedClassProduct
    {p k : ℕ} [Fact p.Prime] (q : Fin k → ℕ)
    (hqprime : ∀ i, (q i).Prime)
    (hq2 : ∀ i, q i ≠ 2) (hqp : ∀ i, q i ≠ p)
    (hallowed : ∀ i, ¬ IsQuadraticObstruction (p ^ 3) (q i))
    (hinj : Function.Injective q) (sigma : Fin k → Bool)
    (hclass : signedProduct sigma (fun i =>
      specialSplitPrimeClass p (q i) (hqprime i) (hq2 i) (hqp i)
        (hallowed i)) = 1) :
    ∃ x y : ℕ, ∏ i, q i = x ^ 2 + p ^ 3 * y ^ 2 := by
  let d : ℤ := -(p : ℤ) ^ 3
  letI : Module.Free ℤ (Zsqrtd d) :=
    Module.Free.of_basis (zsqrtdBasis d)
  letI : Module.Finite ℤ (Zsqrtd d) :=
    Module.Finite.of_basis (zsqrtdBasis d)
  let J : Fin k → Ideal (Zsqrtd d) := fun i =>
    specialOrientedSplitIdeal p (q i) (hallowed i) (sigma i)
  let U : Fin k → (FractionalIdeal (Zsqrtd d)⁰
      (FractionRing (Zsqrtd d)))ˣ := fun i =>
    specialOrientedSplitUnit p (q i) (hqprime i) (hq2 i) (hqp i)
      (hallowed i) (sigma i)
  have hcoe : ∀ i,
      ((U i : (FractionalIdeal (Zsqrtd d)⁰
          (FractionRing (Zsqrtd d)))ˣ) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) = J i := by
    intro i
    exact specialOrientedSplitUnit_coe p (q i) (hqprime i)
      (hq2 i) (hqp i) (hallowed i) (sigma i)
  have hpair : ∀ i j, i ≠ j → IsCoprime (J i) (J j) := by
    intro i j hij
    apply orientedSplitIdeal_isCoprime_of_coprime
    exact (Nat.coprime_primes (hqprime i) (hqprime j)).2 (hinj.ne hij)
  have hcard : ∀ i, (J i).cardQuot = q i := by
    intro i
    letI : NeZero (q i) := ⟨(hqprime i).ne_zero⟩
    exact orientedSplitIdeal_cardQuot d (q i)
      (specialSplitRoot p (q i) (hallowed i))
      (specialSplitRoot_sq p (q i) (hallowed i)) (sigma i)
  have hclassU : ∏ i,
      ClassGroup.mk (FractionRing (Zsqrtd d)) (U i) = 1 := by
    calc
      ∏ i, ClassGroup.mk (FractionRing (Zsqrtd d)) (U i) =
          signedProduct sigma (fun i =>
            specialSplitPrimeClass p (q i) (hqprime i) (hq2 i)
              (hqp i) (hallowed i)) := by
        unfold signedProduct
        apply Finset.prod_congr rfl
        intro i hi
        exact specialOrientedSplitUnit_class p (q i) (hqprime i)
          (hq2 i) (hqp i) (hallowed i) (sigma i)
      _ = 1 := hclass
  obtain ⟨z, hnorm⟩ :=
    exists_generator_norm_eq_prod_of_class_product_eq_one q J U hcoe
      hpair hcard hclassU
  refine ⟨z.re.natAbs, z.im.natAbs, ?_⟩
  calc
    ∏ i, q i = (Algebra.norm ℤ z).natAbs := hnorm.symm
    _ = z.norm.natAbs := by rw [algebraNorm_zsqrtd]
    _ = z.re.natAbs ^ 2 + p ^ 3 * z.im.natAbs ^ 2 := by
      rw [Zsqrtd.norm_def]
      change (z.re * z.re - d * z.im * z.im).natAbs = _
      rw [show z.re * z.re - d * z.im * z.im =
          z.re ^ 2 + (p : ℤ) ^ 3 * z.im ^ 2 by
        dsimp [d]
        ring]
      rw [Int.natAbs_add_of_nonneg (sq_nonneg z.re)
        (mul_nonneg (by positivity) (sq_nonneg z.im)),
        Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow,
        Int.natAbs_pow, Int.natAbs_natCast]

local instance isQuadraticObstructionDecidable (d : ℕ) :
    DecidablePred (IsQuadraticObstruction d) := Classical.decPred _

/-- The obstruction predicate is exactly the value `-1` of the Legendre
symbol. -/
theorem isQuadraticObstruction_iff_legendreSym
    {d l : ℕ} [Fact l.Prime] :
    IsQuadraticObstruction d l ↔
      legendreSym l (-(d : ℤ)) = -1 := by
  simpa [IsQuadraticObstruction] using
    (legendreSym.eq_neg_one_iff (p := l) (a := -(d : ℤ))).symm

/-- For two distinct primes congruent to `3 mod 4`, quadratic reciprocity
cancels the minus sign and the odd cube:
`(-p³ / l) = (l / p)`. -/
theorem legendreSym_neg_primeCube_eq
    {p l : ℕ} [Fact p.Prime] [Fact l.Prime]
    (hp4 : p % 4 = 3) (hl4 : l % 4 = 3) (hpl : p ≠ l) :
    legendreSym l (-(p : ℤ) ^ 3) = legendreSym p (l : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hl2 : l ≠ 2 := by omega
  have hchi : ZMod.χ₄ l = -1 := ZMod.χ₄_nat_three_mod_four hl4
  have hrec := legendreSym.quadratic_reciprocity_three_mod_four hp4 hl4
  have hpdvd : ¬ l ∣ p := by
    intro h
    have hpprime : p.Prime := Fact.out
    have hlprime : l.Prime := Fact.out
    exact hpl ((Nat.prime_dvd_prime_iff_eq hlprime hpprime).mp h).symm
  have hsq : legendreSym l (p : ℤ) ^ 2 = 1 := by
    apply legendreSym.sq_one
    simpa [ZMod.natCast_eq_zero_iff] using hpdvd
  have hcub : legendreSym l (p : ℤ) ^ 3 = legendreSym l (p : ℤ) := by
    calc
      legendreSym l (p : ℤ) ^ 3 =
          legendreSym l (p : ℤ) * legendreSym l (p : ℤ) ^ 2 := by ring
      _ = legendreSym l (p : ℤ) := by rw [hsq, mul_one]
  calc
    legendreSym l (-(p : ℤ) ^ 3) =
        ZMod.χ₄ l * legendreSym l ((p : ℤ) ^ 3) :=
      legendreSym.at_neg hl2 _
    _ = (-1) * legendreSym l (p : ℤ) ^ 3 := by
      rw [hchi]
      congr 1
      rw [show (p : ℤ) ^ 3 = p * p * p by ring,
        legendreSym.mul, legendreSym.mul]
      ring
    _ = -legendreSym l (p : ℤ) := by rw [hcub]; ring
    _ = legendreSym p (l : ℤ) := by rw [hrec]; ring

/-- The same reciprocity identity for every odd prime `l`.  When
`l ≡ 1 (mod 4)` both the sign at `-1` and the reciprocity sign are positive;
when `l ≡ 3 (mod 4)` they are both negative and cancel. -/
theorem legendreSym_neg_primeCube_eq_of_ne_two
    {p l : ℕ} [Fact p.Prime] [Fact l.Prime]
    (hp4 : p % 4 = 3) (hl2 : l ≠ 2) (hpl : p ≠ l) :
    legendreSym l (-(p : ℤ) ^ 3) = legendreSym p (l : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hpdvd : ¬ l ∣ p := by
    intro h
    have hpprime : p.Prime := Fact.out
    have hlprime : l.Prime := Fact.out
    exact hpl ((Nat.prime_dvd_prime_iff_eq hlprime hpprime).mp h).symm
  have hsq : legendreSym l (p : ℤ) ^ 2 = 1 := by
    apply legendreSym.sq_one
    simpa [ZMod.natCast_eq_zero_iff] using hpdvd
  have hcub : legendreSym l (p : ℤ) ^ 3 = legendreSym l (p : ℤ) := by
    calc
      legendreSym l (p : ℤ) ^ 3 =
          legendreSym l (p : ℤ) * legendreSym l (p : ℤ) ^ 2 := by ring
      _ = legendreSym l (p : ℤ) := by rw [hsq, mul_one]
  have hlodd : l % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hl2
  rcases Nat.odd_mod_four_iff.mp hlodd with hl4 | hl4
  · have hchi : ZMod.χ₄ l = 1 := ZMod.χ₄_nat_one_mod_four hl4
    have hrec :=
      @legendreSym.quadratic_reciprocity_one_mod_four l p _ _ hl4 hp2
    calc
      legendreSym l (-(p : ℤ) ^ 3) =
          ZMod.χ₄ l * legendreSym l ((p : ℤ) ^ 3) :=
        legendreSym.at_neg hl2 _
      _ = legendreSym l (p : ℤ) ^ 3 := by
        rw [hchi, one_mul]
        rw [show (p : ℤ) ^ 3 = p * p * p by ring,
          legendreSym.mul, legendreSym.mul]
        ring
      _ = legendreSym l (p : ℤ) := hcub
      _ = legendreSym p (l : ℤ) := hrec.symm
  · exact legendreSym_neg_primeCube_eq hp4 hl4 hpl

/-- For a prime coefficient `p ≡ 3 (mod 4)`, every distinct odd prime
obstruction is detected by the ordinary quadratic character modulo `p`. -/
theorem isQuadraticObstruction_primeCube_iff_of_ne_two
    {p l : ℕ} [Fact p.Prime] [Fact l.Prime]
    (hp4 : p % 4 = 3) (hl2 : l ≠ 2) (hpl : p ≠ l) :
    IsQuadraticObstruction (p ^ 3) l ↔
      legendreSym p (l : ℤ) = -1 := by
  rw [isQuadraticObstruction_iff_legendreSym]
  rw [show (-(p ^ 3 : ℕ) : ℤ) = -(p : ℤ) ^ 3 by norm_num]
  rw [legendreSym_neg_primeCube_eq_of_ne_two hp4 hl2 hpl]

/-! ### Exact cardinality of the quadratic nonresidue classes -/

/-- The subgroup of square units modulo `p`. -/
noncomputable def unitSquareSubgroup (p : ℕ) : Subgroup (ZMod p)ˣ :=
  (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range

/-- The nonsquare units modulo `p`.  This is an abbreviation so that its
finite-type structure is inherited transparently from `(ZMod p)ˣ`. -/
abbrev NonSquareUnit (p : ℕ) :=
  {u : (ZMod p)ˣ // u ∉ unitSquareSubgroup p}

/-- Exactly half of the nonzero residue classes modulo an odd prime are
quadratic nonresidues. -/
theorem card_nonSquareUnit {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (NonSquareUnit p) = (p - 1) / 2 := by
  classical
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
  have heven : 2 ∣ p - 1 := by omega
  have hgcd : (p - 1).gcd 2 = 2 := Nat.gcd_eq_right heven
  have hrange : Nat.card (unitSquareSubgroup p) = (p - 1) / 2 := by
    rw [unitSquareSubgroup, IsCyclic.card_powMonoidHom_range,
      Nat.card_eq_fintype_card, ZMod.card_units, hgcd]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [Nat.card_eq_fintype_card] at hrange
  rw [hrange, ZMod.card_units]
  omega

/-- A unit is in the square subgroup exactly when its value in the prime
field is a square. -/
theorem mem_unitSquareSubgroup_iff {p : ℕ} [Fact p.Prime]
    (u : (ZMod p)ˣ) :
    u ∈ unitSquareSubgroup p ↔ IsSquare (u : ZMod p) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v : ZMod p), ?_⟩
    have hval := congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) hv
    simpa [unitSquareSubgroup, powMonoidHom_apply, pow_two] using hval.symm
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro haz
      subst a
      simp only [zero_mul] at ha
      exact u.ne_zero ha
    let v : (ZMod p)ˣ := Units.mk0 a ha0
    refine ⟨v, ?_⟩
    apply Units.ext
    simpa [v, unitSquareSubgroup, powMonoidHom_apply, pow_two] using ha.symm

/-- Nonsquare units are canonically the nonsquare elements of the prime
field; zero does not occur on either side. -/
noncomputable def nonSquareUnitEquiv {p : ℕ} [Fact p.Prime] :
    NonSquareUnit p ≃ {a : ZMod p // ¬ IsSquare a} where
  toFun u := ⟨(u.1 : ZMod p), by
    simpa [mem_unitSquareSubgroup_iff] using u.2⟩
  invFun a := by
    have ha0 : a.1 ≠ 0 := by
      intro h
      apply a.2
      exact ⟨0, by simp [h]⟩
    let u : (ZMod p)ˣ := Units.mk0 a.1 ha0
    exact ⟨u, by
      rw [mem_unitSquareSubgroup_iff]
      simpa [u] using a.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl

/-- The finite set of quadratic nonresidue classes modulo a prime. -/
noncomputable def nonresidueClasses (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun a => ¬ IsSquare a

@[simp] theorem mem_nonresidueClasses {p : ℕ} [Fact p.Prime]
    {a : ZMod p} :
    a ∈ nonresidueClasses p ↔ ¬ IsSquare a := by
  classical
  simp [nonresidueClasses]

/-- Finset form of the exact half-density theorem. -/
theorem card_nonresidueClasses {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (nonresidueClasses p).card = (p - 1) / 2 := by
  classical
  calc
    (nonresidueClasses p).card =
        Fintype.card {a : ZMod p // ¬ IsSquare a} := by
      simpa [nonresidueClasses] using
        (Fintype.card_subtype (fun a : ZMod p => ¬ IsSquare a)).symm
    _ = Nat.card (NonSquareUnit p) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_congr (nonSquareUnitEquiv (p := p))).symm
    _ = (p - 1) / 2 := card_nonSquareUnit hp2

/-- The quadratic nonresidues represented as units.  This version is useful
for taking Cartesian products before applying the Chinese remainder theorem. -/
noncomputable def nonSquareUnits (p : ℕ) [Fact p.Prime] :
    Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ.filter fun u => u ∉ unitSquareSubgroup p

/-- Unit-valued form of the exact half-density theorem. -/
theorem card_nonSquareUnits {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (nonSquareUnits p).card = (p - 1) / 2 := by
  classical
  calc
    (nonSquareUnits p).card = Fintype.card (NonSquareUnit p) := by
      simpa [nonSquareUnits] using
        (Fintype.card_subtype
          (fun u : (ZMod p)ˣ => u ∉ unitSquareSubgroup p)).symm
    _ = Nat.card (NonSquareUnit p) := by rw [Nat.card_eq_fintype_card]
    _ = (p - 1) / 2 := card_nonSquareUnit hp2

/-- The union of the two nonresidue conditions in the product of the unit
groups modulo `p` and `q`. -/
noncomputable def pairNonSquareUnits (p q : ℕ)
    [Fact p.Prime] [Fact q.Prime] : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := by
  classical
  exact ((nonSquareUnits p).product Finset.univ) ∪
    (Finset.univ.product (nonSquareUnits q))

/-- For odd primes, the union of the two quadratic-nonresidue conditions has
exact density `3/4` in the product unit group. -/
theorem card_pairNonSquareUnits {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    (pairNonSquareUnits p q).card =
      3 * ((p - 1) / 2) * ((q - 1) / 2) := by
  classical
  let P : Finset (ZMod p)ˣ := nonSquareUnits p
  let Q : Finset (ZMod q)ˣ := nonSquareUnits q
  have hP : P.card = (p - 1) / 2 := card_nonSquareUnits hp2
  have hQ : Q.card = (q - 1) / 2 := card_nonSquareUnits hq2
  have hInter :
      (P.product (Finset.univ : Finset (ZMod q)ˣ)) ∩
          ((Finset.univ : Finset (ZMod p)ˣ).product Q) = P.product Q := by
    ext z
    simp
  have hcard := Finset.card_union_add_card_inter
    (P.product (Finset.univ : Finset (ZMod q)ˣ))
    ((Finset.univ : Finset (ZMod p)ˣ).product Q)
  rw [hInter] at hcard
  have hcard' :
      ((P.product (Finset.univ : Finset (ZMod q)ˣ)) ∪
        ((Finset.univ : Finset (ZMod p)ˣ).product Q)).card +
          P.card * Q.card =
        P.card * Fintype.card (ZMod q)ˣ +
          Fintype.card (ZMod p)ˣ * Q.card := by
    simpa using hcard
  change
    ((P.product (Finset.univ : Finset (ZMod q)ˣ)) ∪
      ((Finset.univ : Finset (ZMod p)ˣ).product Q)).card = _
  have hpEven : 2 * ((p - 1) / 2) = p - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : p % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
      omega)
  have hqEven : 2 * ((q - 1) / 2) = q - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : q % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hq2
      omega)
  rw [hP, hQ, ZMod.card_units, ZMod.card_units] at hcard'
  rw [← hpEven, ← hqEven] at hcard'
  simp at hcard'
  ring_nf at hcard' ⊢
  generalize (p - 1) / 2 * ((q - 1) / 2) = t at hcard' ⊢
  clear hcard hInter hP hQ hpEven hqEven
  have hmul : t * 4 = t * 3 + t := by ring
  rw [hmul] at hcard'
  exact Nat.add_right_cancel hcard'

/-- CRT on residue rings, restricted to their unit groups. -/
noncomputable def crtUnitsEquiv {p q : ℕ} (hpq : p.Coprime q) :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hpq).toMulEquiv).trans
    MulEquiv.prodUnits

theorem crtUnitsEquiv_fst {p q : ℕ} [NeZero (p * q)]
    (hpq : p.Coprime q) (u : (ZMod (p * q))ˣ) :
    (((crtUnitsEquiv hpq u).1 : (ZMod p)ˣ) : ZMod p) =
      (((u : ZMod (p * q)).val : ℕ) : ZMod p) := by
  change ((ZMod.chineseRemainder hpq (u : ZMod (p * q))).1) = _
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod (p * q))]
  rw [map_natCast]
  rfl

theorem crtUnitsEquiv_snd {p q : ℕ} [NeZero (p * q)]
    (hpq : p.Coprime q) (u : (ZMod (p * q))ˣ) :
    (((crtUnitsEquiv hpq u).2 : (ZMod q)ˣ) : ZMod q) =
      (((u : ZMod (p * q)).val : ℕ) : ZMod q) := by
  change ((ZMod.chineseRemainder hpq (u : ZMod (p * q))).2) = _
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod (p * q))]
  rw [map_natCast]
  rfl

/-- The reduced residue classes modulo `p*q` on which at least one of the
two quadratic characters is `-1`, encoded by their canonical natural
representatives. -/
noncomputable def pairNonresidueEmbedding {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) :
    (ZMod p)ˣ × (ZMod q)ˣ ↪ ℕ := by
  let e := crtUnitsEquiv hpq
  let f : (ZMod p)ˣ × (ZMod q)ˣ → ℕ := fun z =>
    (((e.symm z : (ZMod (p * q))ˣ) : ZMod (p * q))).val
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp0 hq0
  letI : NeZero (p * q) := ⟨hpq0⟩
  refine ⟨f, ?_⟩
  intro a b hab
  apply e.symm.injective
  apply Units.ext
  exact ZMod.val_injective (p * q) hab

noncomputable def pairNonresidueResidues {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) : Finset ℕ := by
  classical
  exact (pairNonSquareUnits p q).map (pairNonresidueEmbedding hpq)

/-- The CRT encoding preserves the exact `3/4` cardinality. -/
theorem card_pairNonresidueResidues {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    (pairNonresidueResidues hpq).card =
      3 * ((p - 1) / 2) * ((q - 1) / 2) := by
  classical
  rw [pairNonresidueResidues, Finset.card_map]
  exact card_pairNonSquareUnits hp2 hq2

/-- Every encoded CRT class is reduced and is a nonresidue for at least one
of the two prime moduli. -/
theorem pairNonresidueResidues_spec {p q a : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q)
    (ha : a ∈ pairNonresidueResidues hpq) :
    a < p * q ∧ a.Coprime (p * q) ∧
      (¬ IsSquare (a : ZMod p) ∨ ¬ IsSquare (a : ZMod q)) := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp0 hq0
  letI : NeZero (p * q) := ⟨hpq0⟩
  let e := crtUnitsEquiv hpq
  let f := pairNonresidueEmbedding hpq
  rw [pairNonresidueResidues] at ha
  rcases Finset.mem_map.mp ha with ⟨z, hz, hza⟩
  subst a
  let u : (ZMod (p * q))ˣ := e.symm z
  have heu : e u = z := e.apply_symm_apply z
  have hep : (((f z : ℕ) : ZMod p)) = (z.1 : ZMod p) := by
    change ((((u : ZMod (p * q)).val : ℕ) : ZMod p)) = _
    rw [← heu]
    exact (crtUnitsEquiv_fst hpq u).symm
  have heq : (((f z : ℕ) : ZMod q)) = (z.2 : ZMod q) := by
    change ((((u : ZMod (p * q)).val : ℕ) : ZMod q)) = _
    rw [← heu]
    exact (crtUnitsEquiv_snd hpq u).symm
  refine ⟨ZMod.val_lt (u : ZMod (p * q)), ?_, ?_⟩
  · apply (ZMod.isUnit_iff_coprime (f z) (p * q)).mp
    rw [show ((f z : ℕ) : ZMod (p * q)) = (u : ZMod (p * q)) by
      exact ZMod.natCast_zmod_val (u : ZMod (p * q))]
    exact u.isUnit
  · simp only [pairNonSquareUnits, Finset.mem_union,
      Finset.mem_product, Finset.mem_univ, and_true, true_and] at hz
    rcases hz with hz | hz
    · left
      rw [hep]
      simpa [nonSquareUnits, mem_unitSquareSubgroup_iff] using hz
    · right
      rw [heq]
      simpa [nonSquareUnits, mem_unitSquareSubgroup_iff] using hz

/-- A prime in one of the CRT classes is a local obstruction for at least
one of the two special forms.  This is the exact bridge from the finite
`3/4`-density calculation to the parity sieve. -/
theorem pairNonresidueResidue_is_obstruction
    {p q l a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (ha : a ∈ pairNonresidueResidues hpq)
    (hla : l % (p * q) = a) :
    IsQuadraticObstruction (p ^ 3) l ∨
      IsQuadraticObstruction (q ^ 3) l := by
  let _ : Fact l.Prime := ⟨hl⟩
  have haspec := pairNonresidueResidues_spec hpq ha
  have hmodpq : l ≡ a [MOD p * q] := by
    unfold Nat.ModEq
    simpa [Nat.mod_eq_of_lt haspec.1] using hla
  rcases haspec.2.2 with hns | hns
  · left
    have hmodp : l ≡ a [MOD p] :=
      hmodpq.of_dvd (Nat.dvd_mul_right p q)
    have hcast : (l : ZMod p) = (a : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff l a p).2 hmodp
    have hnsl : ¬ IsSquare (l : ZMod p) := by simpa [hcast] using hns
    have hlp : p ≠ l := by
      intro hpl
      subst l
      apply hnsl
      exact ⟨0, by simp⟩
    rw [isQuadraticObstruction_primeCube_iff_of_ne_two hp4 hl2 hlp]
    exact (legendreSym.eq_neg_one_iff (p := p) (a := (l : ℤ))).2 (by
      simpa using hnsl)
  · right
    have hmodq : l ≡ a [MOD q] :=
      hmodpq.of_dvd (Nat.dvd_mul_left q p)
    have hcast : (l : ZMod q) = (a : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff l a q).2 hmodq
    have hnsl : ¬ IsSquare (l : ZMod q) := by simpa [hcast] using hns
    have hlq : q ≠ l := by
      intro hql
      subst l
      apply hnsl
      exact ⟨0, by simp⟩
    rw [isQuadraticObstruction_primeCube_iff_of_ne_two hq4 hl2 hlq]
    exact (legendreSym.eq_neg_one_iff (p := q) (a := (l : ℤ))).2 (by
      simpa using hnsl)

/-! ### Reciprocal mass in the CRT obstruction classes -/

/-- Primes in the reduced residue class `a mod q` between consecutive powers
of `4/3`.  The ratio `4/3` leaves enough room for the exact `3/4` character
density to beat the square-root logarithmic threshold. -/
noncomputable def geometricAPPrimes (q a k : ℕ) : Finset ℕ :=
  Erdos387.primeIntervalAP q a ((4 / 3 : ℝ) ^ k)
    ((4 / 3 : ℝ) ^ (k + 1))

/-- The primes in one fixed reduced residue class, collected over the
geometric shells with indices in `[k₀,K]`. -/
noncomputable def geometricAPPrimesBetween
    (q a k₀ K : ℕ) : Finset ℕ :=
  (Finset.Icc k₀ K).biUnion (geometricAPPrimes q a)

/-- Fixed-modulus PNT in arithmetic progressions, converted on each
`(4/3)`-adic interval to an explicit reciprocal-prime lower bound. -/
theorem eventually_geometricAPPrimes_reciprocal_lower
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) :
    ∀ᶠ k : ℕ in atTop,
      (6 / 25 : ℝ) /
          ((q.totient : ℝ) * (k : ℝ) * Real.log (4 / 3 : ℝ)) ≤
        ∑ l ∈ geometricAPPrimes q a k, (l : ℝ)⁻¹ := by
  obtain ⟨x₀, hx₀3, hPNT⟩ := Erdos387.primeIntervalAP_card_estimate
    hq ha haq (1 / 3 : ℝ) (1 / 25 : ℝ) (by norm_num) (by norm_num)
  have hb : (1 : ℝ) < 4 / 3 := by norm_num
  have hpow : Tendsto (fun k : ℕ ↦ (4 / 3 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  filter_upwards [hpow.eventually (eventually_ge_atTop x₀),
      eventually_ge_atTop 1] with k hkx hk1
  let x : ℝ := (4 / 3 : ℝ) ^ k
  let v : ℝ := (4 / 3 : ℝ) ^ (k + 1)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hv_eq : v = (4 / 3) * x := by
    dsimp [v, x]
    rw [pow_succ]
    ring
  have hxv : x < v := by rw [hv_eq]; nlinarith
  have hv2 : v ≤ 2 * x := by rw [hv_eq]; nlinarith
  have hlen : (1 / 3 : ℝ) * x ≤ v - x := by
    rw [hv_eq]
    ring_nf
    exact le_rfl
  have hcardAbs := hPNT x hkx x v le_rfl hxv hv2 hlen
  have hmainpos : 0 < (v - x) / (q.totient : ℝ) / Real.log x := by
    have hphi : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hq
    have hlog : 0 < Real.log x := by
      apply Real.log_pos
      dsimp [x]
      exact one_lt_pow₀ hb (Nat.ne_of_gt hk1)
    positivity
  have hcard :
      (24 / 25 : ℝ) * ((v - x) / (q.totient : ℝ) / Real.log x) ≤
        ((geometricAPPrimes q a k).card : ℝ) := by
    rw [abs_le] at hcardAbs
    dsimp [geometricAPPrimes]
    linarith
  have hterm : ∀ l ∈ geometricAPPrimes q a k,
      (1 / v : ℝ) ≤ (l : ℝ)⁻¹ := by
    intro l hl
    have hldata := Finset.mem_filter.mp hl
    have hlIoc := Finset.mem_Ioc.mp hldata.1
    have hlv : (l : ℝ) ≤ v :=
      (Nat.cast_le.mpr hlIoc.2).trans (Nat.floor_le (by positivity))
    have hlpos : (0 : ℝ) < l := by exact_mod_cast hldata.2.1.pos
    simpa only [one_div] using one_div_le_one_div_of_le hlpos hlv
  calc
    (6 / 25 : ℝ) /
          ((q.totient : ℝ) * (k : ℝ) * Real.log (4 / 3 : ℝ))
        = (24 / 25 : ℝ) *
            ((v - x) / (q.totient : ℝ) / Real.log x) / v := by
          rw [hv_eq]
          have hlogb : Real.log (4 / 3 : ℝ) ≠ 0 :=
            ne_of_gt (Real.log_pos hb)
          have hkpos : (k : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hk1)
          have hphi : (q.totient : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hq))
          have hxne : x ≠ 0 := ne_of_gt hxpos
          rw [show Real.log x = (k : ℝ) * Real.log (4 / 3 : ℝ) by
            dsimp [x]
            rw [Real.log_pow]]
          field_simp
          norm_num
    _ ≤ ((geometricAPPrimes q a k).card : ℝ) / v := by
      exact div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ _l ∈ geometricAPPrimes q a k, (1 / v : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ l ∈ geometricAPPrimes q a k, (l : ℝ)⁻¹ := by
      exact Finset.sum_le_sum hterm

/-- Distinct residue classes give disjoint geometric prime blocks. -/
theorem pairwiseDisjoint_geometricAPPrimes (q k : ℕ) (R : Finset ℕ) :
    ((R : Set ℕ)).PairwiseDisjoint (fun a ↦ geometricAPPrimes q a k) := by
  intro a ha b hb hab
  change Disjoint (geometricAPPrimes q a k) (geometricAPPrimes q b k)
  rw [Finset.disjoint_left]
  intro l hla hlb
  have hla' := (Finset.mem_filter.mp hla).2.2
  have hlb' := (Finset.mem_filter.mp hlb).2.2
  exact hab (hla'.symm.trans hlb')

/-- Shells with different indices are disjoint, independently of the
chosen modulus and residue class. -/
theorem pairwiseDisjoint_geometricAPPrimes_shells
    (q a : ℕ) (K : Finset ℕ) :
    ((K : Set ℕ)).PairwiseDisjoint (geometricAPPrimes q a) := by
  intro i hi j hj hij
  change Disjoint (geometricAPPrimes q a i) (geometricAPPrimes q a j)
  rw [Finset.disjoint_left]
  intro l hli hlj
  have hliI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hli).1
  have hljI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hlj).1
  have hliUpper : (l : ℝ) ≤ (4 / 3 : ℝ) ^ (i + 1) :=
    (Nat.cast_le.mpr hliI.2).trans (Nat.floor_le (by positivity))
  have hljUpper : (l : ℝ) ≤ (4 / 3 : ℝ) ^ (j + 1) :=
    (Nat.cast_le.mpr hljI.2).trans (Nat.floor_le (by positivity))
  have hliLower : (4 / 3 : ℝ) ^ i < (l : ℝ) :=
    Nat.lt_of_floor_lt hliI.1
  have hljLower : (4 / 3 : ℝ) ^ j < (l : ℝ) :=
    Nat.lt_of_floor_lt hljI.1
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hpows : (4 / 3 : ℝ) ^ (i + 1) ≤ (4 / 3 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  · have hpows : (4 / 3 : ℝ) ^ (j + 1) ≤ (4 / 3 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

theorem geometricAPPrimesBetween_sum_eq
    (q a k₀ K : ℕ) :
    ∑ p ∈ geometricAPPrimesBetween q a k₀ K, (p : ℝ)⁻¹ =
      ∑ k ∈ Finset.Icc k₀ K,
        ∑ p ∈ geometricAPPrimes q a k, (p : ℝ)⁻¹ := by
  exact Finset.sum_biUnion
    (pairwiseDisjoint_geometricAPPrimes_shells q a (Finset.Icc k₀ K))

/-- The union, on one geometric shell, of every CRT class which obstructs
at least one of the two forms. -/
noncomputable def geometricPairObstructionPrimes {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) (k : ℕ) : Finset ℕ :=
  (pairNonresidueResidues hpq).biUnion
    (fun a ↦ geometricAPPrimes (p * q) a k)

theorem geometricPairObstructionPrimes_sum_eq {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) (k : ℕ) :
    ∑ l ∈ geometricPairObstructionPrimes hpq k, (l : ℝ)⁻¹ =
      ∑ a ∈ pairNonresidueResidues hpq,
        ∑ l ∈ geometricAPPrimes (p * q) a k, (l : ℝ)⁻¹ := by
  exact Finset.sum_biUnion
    (pairwiseDisjoint_geometricAPPrimes (p * q) k
      (pairNonresidueResidues hpq))

/-- Summing the fixed-residue PNT over the exact `3/4` CRT family gives
more than one half of a harmonic summand on every sufficiently late shell.
The explicit coefficient `27/50` is retained for later overlap estimates. -/
theorem eventually_geometricPairObstructionPrimes_reciprocal_lower
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    ∀ᶠ k : ℕ in atTop,
      (27 / 50 : ℝ) * (k : ℝ)⁻¹ ≤
        ∑ l ∈ geometricPairObstructionPrimes hpq k, (l : ℝ)⁻¹ := by
  let R := pairNonresidueResidues hpq
  have hqpos : 1 ≤ p * q := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero
        (Fact.out : q.Prime).ne_zero)
  have hR : ∀ a ∈ R, a < p * q ∧ a.Coprime (p * q) := by
    intro a ha
    exact ⟨(pairNonresidueResidues_spec hpq ha).1,
      (pairNonresidueResidues_spec hpq ha).2.1⟩
  have hAll : ∀ᶠ k : ℕ in atTop, ∀ a ∈ R,
      (6 / 25 : ℝ) /
          (((p * q).totient : ℝ) * (k : ℝ) * Real.log (4 / 3 : ℝ)) ≤
        ∑ l ∈ geometricAPPrimes (p * q) a k, (l : ℝ)⁻¹ := by
    rw [Finset.eventually_all]
    intro a ha
    exact eventually_geometricAPPrimes_reciprocal_lower
      hqpos (hR a ha).2 (hR a ha).1
  filter_upwards [hAll, eventually_ge_atTop 1] with k hk hk1
  have hlogpos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hlogle : Real.log (4 / 3 : ℝ) ≤ 1 / 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3) using 1 <;>
      norm_num
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hphi : (0 : ℝ) < (p * q).totient := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hpEven : 2 * ((p - 1) / 2) = p - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : p % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
      omega)
  have hqEven : 2 * ((q - 1) / 2) = q - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : q % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hq2
      omega)
  have hcardNat : 4 * R.card = 3 * (p * q).totient := by
    calc
      4 * R.card = 4 *
          (3 * ((p - 1) / 2) * ((q - 1) / 2)) := by
            rw [card_pairNonresidueResidues hpq hp2 hq2]
      _ = 3 * ((2 * ((p - 1) / 2)) * (2 * ((q - 1) / 2))) := by ring
      _ = 3 * ((p - 1) * (q - 1)) := by rw [hpEven, hqEven]
      _ = 3 * (p * q).totient := by
        rw [Nat.totient_mul hpq, Nat.totient_prime (Fact.out : p.Prime),
          Nat.totient_prime (Fact.out : q.Prime)]
  have hcardR : (R.card : ℝ) =
      (3 / 4 : ℝ) * ((p * q).totient : ℝ) := by
    have hcardReal : (4 : ℝ) * (R.card : ℝ) =
        3 * ((p * q).totient : ℝ) := by exact_mod_cast hcardNat
    linarith
  have hcoefficient :
      (27 / 50 : ℝ) * (k : ℝ)⁻¹ ≤
        (R.card : ℝ) *
          ((6 / 25 : ℝ) /
            (((p * q).totient : ℝ) * (k : ℝ) *
              Real.log (4 / 3 : ℝ))) := by
    rw [hcardR]
    have hdenpos : 0 < (k : ℝ) * Real.log (4 / 3 : ℝ) :=
      mul_pos hkpos hlogpos
    rw [show
      (3 / 4 : ℝ) * ((p * q).totient : ℝ) *
          ((6 / 25 : ℝ) /
            (((p * q).totient : ℝ) * (k : ℝ) *
              Real.log (4 / 3 : ℝ))) =
        (9 / 50 : ℝ) / ((k : ℝ) * Real.log (4 / 3 : ℝ)) by
          field_simp
          ring]
    apply (le_div_iff₀ hdenpos).2
    rw [inv_eq_one_div]
    field_simp
    nlinarith
  calc
    (27 / 50 : ℝ) * (k : ℝ)⁻¹ ≤
        (R.card : ℝ) *
          ((6 / 25 : ℝ) /
            (((p * q).totient : ℝ) * (k : ℝ) *
              Real.log (4 / 3 : ℝ))) := hcoefficient
    _ = ∑ _a ∈ R,
          ((6 / 25 : ℝ) /
            (((p * q).totient : ℝ) * (k : ℝ) *
              Real.log (4 / 3 : ℝ))) := by simp
    _ ≤ ∑ a ∈ R,
        ∑ l ∈ geometricAPPrimes (p * q) a k, (l : ℝ)⁻¹ := by
      exact Finset.sum_le_sum fun a ha ↦ hk a ha
    _ = ∑ l ∈ geometricPairObstructionPrimes hpq k, (l : ℝ)⁻¹ :=
      (geometricPairObstructionPrimes_sum_eq hpq k).symm

/-- Geometric shells are pairwise disjoint. -/
theorem pairwiseDisjoint_geometricPairObstructionPrimes {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) (K : Finset ℕ) :
    ((K : Set ℕ)).PairwiseDisjoint
      (fun k ↦ geometricPairObstructionPrimes hpq k) := by
  intro i hi j hj hij
  change Disjoint (geometricPairObstructionPrimes hpq i)
    (geometricPairObstructionPrimes hpq j)
  rw [Finset.disjoint_left]
  intro l hli hlj
  rw [geometricPairObstructionPrimes, Finset.mem_biUnion] at hli hlj
  rcases hli with ⟨a, ha, hlia⟩
  rcases hlj with ⟨b, hb, hljb⟩
  have hliI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hlia).1
  have hljI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hljb).1
  have hliUpper : (l : ℝ) ≤ (4 / 3 : ℝ) ^ (i + 1) :=
    (Nat.cast_le.mpr hliI.2).trans (Nat.floor_le (by positivity))
  have hljUpper : (l : ℝ) ≤ (4 / 3 : ℝ) ^ (j + 1) :=
    (Nat.cast_le.mpr hljI.2).trans (Nat.floor_le (by positivity))
  have hliLower : (4 / 3 : ℝ) ^ i < (l : ℝ) :=
    Nat.lt_of_floor_lt hliI.1
  have hljLower : (4 / 3 : ℝ) ^ j < (l : ℝ) :=
    Nat.lt_of_floor_lt hljI.1
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hpows : (4 / 3 : ℝ) ^ (i + 1) ≤ (4 / 3 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  · have hpows : (4 / 3 : ℝ) ^ (j + 1) ≤ (4 / 3 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

/-- Union of the obstruction shells with indices in `[k₀,K]`. -/
noncomputable def geometricPairObstructionPrimesBetween {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) (k₀ K : ℕ) : Finset ℕ :=
  (Finset.Icc k₀ K).biUnion (geometricPairObstructionPrimes hpq)

theorem geometricPairObstructionPrimesBetween_sum_eq {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q) (k₀ K : ℕ) :
    ∑ l ∈ geometricPairObstructionPrimesBetween hpq k₀ K, (l : ℝ)⁻¹ =
      ∑ k ∈ Finset.Icc k₀ K,
        ∑ l ∈ geometricPairObstructionPrimes hpq k, (l : ℝ)⁻¹ := by
  exact Finset.sum_biUnion
    (pairwiseDisjoint_geometricPairObstructionPrimes hpq (Finset.Icc k₀ K))

/-- Natural endpoint of the `K`-th geometric shell. -/
noncomputable def geometricEndpoint (K : ℕ) : ℕ :=
  ⌊(4 / 3 : ℝ) ^ (K + 1)⌋₊

theorem geometricEndpoint_tendsto_atTop :
    Tendsto geometricEndpoint atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4 / 3)).comp
      (tendsto_add_atTop_nat 1))

/-- Harmonic lower bound obtained by summing all sufficiently late shells. -/
theorem exists_geometricPairObstruction_harmonic_lower
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ K : ℕ, k₀ ≤ K →
      (27 / 50 : ℝ) * (∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹) ≤
        ∑ l ∈ geometricPairObstructionPrimesBetween hpq k₀ K,
          (l : ℝ)⁻¹ := by
  obtain ⟨k₁, hk₁⟩ := (eventually_atTop.1
    (eventually_geometricPairObstructionPrimes_reciprocal_lower
      hpq hp2 hq2))
  refine ⟨max 3 k₁, le_max_left _ _, ?_⟩
  intro K hK
  rw [geometricPairObstructionPrimesBetween_sum_eq]
  calc
    (27 / 50 : ℝ) *
        (∑ k ∈ Finset.Icc (max 3 k₁) K, (k : ℝ)⁻¹) =
        ∑ k ∈ Finset.Icc (max 3 k₁) K,
          (27 / 50 : ℝ) * (k : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Icc (max 3 k₁) K,
        ∑ l ∈ geometricPairObstructionPrimes hpq k, (l : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      exact hk₁ k ((le_max_right 3 k₁).trans (Finset.mem_Icc.mp hk).1)

theorem isQuadraticObstruction_primeCube_iff
    {p l : ℕ} [Fact p.Prime] [Fact l.Prime]
    (hp4 : p % 4 = 3) (hl4 : l % 4 = 3) (hpl : p ≠ l) :
    IsQuadraticObstruction (p ^ 3) l ↔
      legendreSym p (l : ℤ) = -1 := by
  rw [isQuadraticObstruction_iff_legendreSym]
  rw [show (-(p ^ 3 : ℕ) : ℤ) = -(p : ℤ) ^ 3 by norm_num]
  rw [legendreSym_neg_primeCube_eq hp4 hl4 hpl]

/-- A quadratic nonresidue gives the divisibility form of anisotropy. -/
theorem formAnisotropicAt_of_not_isSquare_neg
    {d l : ℕ} (hl : l.Prime) (hns : IsQuadraticObstruction d l) :
    FormAnisotropicAt d l := by
  let _ : Fact l.Prime := ⟨hl⟩
  intro x y hdiv
  have heq : (x : ZMod l) ^ 2 + (d : ZMod l) * (y : ZMod l) ^ 2 = 0 := by
    have hzero : ((x ^ 2 + d * y ^ 2 : ℕ) : ZMod l) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdiv
    simpa using hzero
  have hy : l ∣ y := by
    by_contra hly
    have hyne : (y : ZMod l) ≠ 0 := by
      simpa [ZMod.natCast_eq_zero_iff] using hly
    apply hns
    rw [isSquare_iff_exists_sq]
    refine ⟨(x : ZMod l) / (y : ZMod l), ?_⟩
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hyne)).2
    have hxy : (x : ZMod l) ^ 2 =
        -(d : ZMod l) * (y : ZMod l) ^ 2 :=
      by simpa using eq_neg_of_add_eq_zero_left heq
    exact hxy.symm
  have hyzero : (y : ZMod l) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hy
  have hxzero : (x : ZMod l) = 0 := by
    rw [hyzero] at heq
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at heq
    exact sq_eq_zero_iff.mp heq
  exact And.intro ((ZMod.natCast_eq_zero_iff x l).mp hxzero) hy

/-- At an anisotropic prime, every nonzero value of `x² + d y²` has even
adic valuation.  This is the elementary local input behind every upper bound
for intersections of represented-value sets. -/
theorem even_padicValNat_of_formAnisotropicAt
    {d l x y : ℕ} (hl : l.Prime) (haniso : FormAnisotropicAt d l)
    (hpos : 0 < x ^ 2 + d * y ^ 2) :
    Even (padicValNat l (x ^ 2 + d * y ^ 2)) := by
  let _ : Fact l.Prime := ⟨hl⟩
  generalize hn : x ^ 2 + d * y ^ 2 = n at hpos ⊢
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
      by_cases hln : l ∣ n
      · have hlform : l ∣ x ^ 2 + d * y ^ 2 := hn ▸ hln
        rcases haniso x y hlform with ⟨hx, hy⟩
        rcases hx with ⟨x', rfl⟩
        rcases hy with ⟨y', rfl⟩
        have hnfac : n = l ^ 2 * (x' ^ 2 + d * y' ^ 2) := by
          rw [← hn]
          ring
        have hmpos : 0 < x' ^ 2 + d * y' ^ 2 := by
          by_contra hm
          have hmzero : x' ^ 2 + d * y' ^ 2 = 0 := Nat.eq_zero_of_not_pos hm
          rw [hnfac, hmzero, mul_zero] at hpos
          exact Nat.lt_asymm hpos hpos
        have hlsq : 2 ≤ l := hl.two_le
        have hmlt : x' ^ 2 + d * y' ^ 2 < n := by
          rw [hnfac]
          calc
            x' ^ 2 + d * y' ^ 2 = (x' ^ 2 + d * y' ^ 2) * 1 := by simp
            _ < (x' ^ 2 + d * y' ^ 2) * l ^ 2 :=
              Nat.mul_lt_mul_of_pos_left
                (Nat.one_lt_pow (by decide : 2 ≠ 0) hl.one_lt) hmpos
            _ = l ^ 2 * (x' ^ 2 + d * y' ^ 2) := by ac_rfl
        have hmeven : Even (padicValNat l (x' ^ 2 + d * y' ^ 2)) :=
          ih _ hmlt (x := x') (y := y') rfl hmpos
        rw [hnfac, padicValNat.mul (pow_ne_zero _ hl.ne_zero)
          (Nat.ne_of_gt hmpos), padicValNat.prime_pow]
        exact (even_iff_two_dvd.mpr (by norm_num : 2 ∣ 2)).add hmeven
      · rw [padicValNat.eq_zero_of_not_dvd hln]
        exact Even.zero

/-- The local parity condition inherited by every value of the special form
`u² + p³v²`. -/
theorem even_padicValNat_of_specialForm
    {p l u v : ℕ} (hl : l.Prime) (haniso : FormAnisotropicAt (p ^ 3) l)
    (hpos : 0 < u ^ 2 + p ^ 3 * v ^ 2) :
    Even (padicValNat l (u ^ 2 + p ^ 3 * v ^ 2)) :=
  even_padicValNat_of_formAnisotropicAt hl haniso hpos

/-! ### Global local-norm set for one special form -/

/-- The complete inert-prime parity condition for the form
`X² + p³Y²`.  This is the elementary local norm condition which occurs in
Bernays' theorem.  Ramified primes impose no condition here, while every
anisotropic prime must occur to even valuation. -/
def SpecialLocallyAdmissible (p n : ℕ) : Prop :=
  ∀ l : ℕ, l.Prime → IsQuadraticObstruction (p ^ 3) l →
    Even (padicValNat l n)

/-- On a prime power the local norm condition is completely explicit: an
obstruction prime may occur only to even exponent, while every other prime
power is allowed. -/
theorem specialLocallyAdmissible_prime_pow_iff
    {p l k : ℕ} (hl : l.Prime) :
    SpecialLocallyAdmissible p (l ^ k) ↔
      ¬ IsQuadraticObstruction (p ^ 3) l ∨ Even k := by
  let _ : Fact l.Prime := ⟨hl⟩
  constructor
  · intro h
    by_cases hobs : IsQuadraticObstruction (p ^ 3) l
    · right
      simpa only [padicValNat.prime_pow] using h l hl hobs
    · exact Or.inl hobs
  · intro h q hq hqobs
    rcases h with hnot | hk
    · by_cases hql : q = l
      · subst q
        exact False.elim (hnot hqobs)
      · have hqndvd : ¬ q ∣ l := by
          intro hdvd
          exact hql ((Nat.prime_dvd_prime_iff_eq hq hl).mp hdvd)
        rw [padicValNat.eq_zero_of_not_dvd
          (fun hdvd => hqndvd (hq.dvd_of_dvd_pow hdvd))]
        exact Even.zero
    · by_cases hql : q = l
      · subst q
        simpa only [padicValNat.prime_pow] using hk
      · have hqndvd : ¬ q ∣ l := by
          intro hdvd
          exact hql ((Nat.prime_dvd_prime_iff_eq hq hl).mp hdvd)
        rw [padicValNat.eq_zero_of_not_dvd
          (fun hdvd => hqndvd (hq.dvd_of_dvd_pow hdvd))]
        exact Even.zero

/-- Local admissibility is multiplicative on coprime positive integers. -/
theorem specialLocallyAdmissible_mul_iff_of_coprime
    {p m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    SpecialLocallyAdmissible p (m * n) ↔
      SpecialLocallyAdmissible p m ∧ SpecialLocallyAdmissible p n := by
  constructor
  · intro h
    constructor
    · intro l hl hobs
      let _ : Fact l.Prime := ⟨hl⟩
      have hsum := h l hl hobs
      rw [padicValNat.mul hm.ne' hn.ne'] at hsum
      by_cases hlm : l ∣ m
      · have hln : ¬ l ∣ n := by
          intro hln
          have hlgcd : l ∣ m.gcd n := Nat.dvd_gcd hlm hln
          rw [hmn.gcd_eq_one] at hlgcd
          exact hl.not_dvd_one hlgcd
        rw [padicValNat.eq_zero_of_not_dvd hln, add_zero] at hsum
        exact hsum
      · rw [padicValNat.eq_zero_of_not_dvd hlm]
        exact Even.zero
    · intro l hl hobs
      let _ : Fact l.Prime := ⟨hl⟩
      have hsum := h l hl hobs
      rw [padicValNat.mul hm.ne' hn.ne'] at hsum
      by_cases hln : l ∣ n
      · have hlm : ¬ l ∣ m := by
          intro hlm
          have hlgcd : l ∣ m.gcd n := Nat.dvd_gcd hlm hln
          rw [hmn.gcd_eq_one] at hlgcd
          exact hl.not_dvd_one hlgcd
        rw [padicValNat.eq_zero_of_not_dvd hlm, zero_add] at hsum
        exact hsum
      · rw [padicValNat.eq_zero_of_not_dvd hln]
        exact Even.zero
  · rintro ⟨hmadm, hnadm⟩ l hl hobs
    let _ : Fact l.Prime := ⟨hl⟩
    rw [padicValNat.mul hm.ne' hn.ne']
    exact (hmadm l hl hobs).add (hnadm l hl hobs)

/-- The `0/1` multiplicative function of the complete local norm set.  Its
prime-power values are `1,0,1,0,...` at obstruction primes and identically
`1` at every other prime. -/
noncomputable def specialLocalIndicator (p n : ℕ) : ℝ := by
  classical
  exact if 0 < n ∧ SpecialLocallyAdmissible p n then 1 else 0

@[simp] theorem specialLocalIndicator_zero (p : ℕ) :
    specialLocalIndicator p 0 = 0 := by
  simp [specialLocalIndicator]

@[simp] theorem specialLocalIndicator_one (p : ℕ) :
    specialLocalIndicator p 1 = 1 := by
  classical
  simp [specialLocalIndicator, SpecialLocallyAdmissible]

theorem specialLocalIndicator_nonneg (p n : ℕ) :
    0 ≤ specialLocalIndicator p n := by
  classical
  unfold specialLocalIndicator
  split_ifs <;> norm_num

theorem specialLocalIndicator_mul_of_coprime
    {p m n : ℕ} (hmn : m.Coprime n) :
    specialLocalIndicator p (m * n) =
      specialLocalIndicator p m * specialLocalIndicator p n := by
  classical
  by_cases hm : 0 < m
  · by_cases hn : 0 < n
    · simp [specialLocalIndicator, hm, hn, Nat.mul_pos hm hn,
        specialLocallyAdmissible_mul_iff_of_coprime hm hn hmn]
      by_cases hma : SpecialLocallyAdmissible p m <;>
        by_cases hna : SpecialLocallyAdmissible p n <;>
        simp [hma, hna]
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp

theorem specialLocalIndicator_prime_pow
    {p l k : ℕ} (hl : l.Prime) :
    specialLocalIndicator p (l ^ k) =
      if IsQuadraticObstruction (p ^ 3) l ∧ Odd k then 0 else 1 := by
  classical
  have hlpow : 0 < l ^ k := pow_pos hl.pos k
  simp only [specialLocalIndicator, hlpow, true_and,
    specialLocallyAdmissible_prime_pow_iff hl]
  by_cases hobs : IsQuadraticObstruction (p ^ 3) l
  · by_cases hk : Even k
    · have hkodd : ¬ Odd k := Nat.not_odd_iff_even.mpr hk
      simp [hobs, hk, hkodd]
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hk
      simp [hobs, hk, hkodd]
  · simp [hobs]

/-- Logarithmic-derivative coefficient of the local Euler factor.  It is
`log l` at every positive exponent of an allowed prime, while at an
obstruction prime it is `2 log l` at positive even exponents and zero at odd
exponents. -/
noncomputable def specialLocalLogCoeff (p l k : ℕ) : ℝ :=
  if k = 0 then 0
  else if IsQuadraticObstruction (p ^ 3) l then
    if Even k then 2 * Real.log l else 0
  else Real.log l

theorem specialLocalLogCoeff_nonneg
    (p k : ℕ) {l : ℕ} (hl : l.Prime) :
    0 ≤ specialLocalLogCoeff p l k := by
  classical
  unfold specialLocalLogCoeff
  split_ifs <;> positivity

/-- Among `1,...,2r`, exactly the even indices contribute to the doubled
logarithmic coefficient.  The formulation as a real-valued sum is the one
used directly in the local convolution identity. -/
theorem sum_Icc_even_two (r : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * r),
        if Even k then (2 : ℝ) else 0) = 2 * r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 2 by omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * r + 2),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * r + 1)]
      simp only [ih]
      have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
      have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
      simp [hodd, heven]
      ring

/-- Exact one-prime logarithmic convolution.  This is the coefficient-level
identity behind the Wirsing recurrence for the local norm indicator. -/
theorem specialLocalIndicator_prime_pow_log_convolution
    {p l e : ℕ} (hl : l.Prime) :
    specialLocalIndicator p (l ^ e) * Real.log ((l ^ e : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc 1 e,
        specialLocalIndicator p (l ^ (e - k)) *
          specialLocalLogCoeff p l k := by
  classical
  by_cases hobs : IsQuadraticObstruction (p ^ 3) l
  · by_cases he : Even e
    · obtain ⟨r, rfl⟩ := he
      simp only [show r + r = 2 * r by omega]
      have heven : Even (2 * r) := ⟨r, by omega⟩
      have hind : specialLocalIndicator p (l ^ (2 * r)) = 1 := by
        rw [specialLocalIndicator_prime_pow hl]
        simp [hobs, heven, Nat.not_odd_iff_even.mpr heven]
      have hsumPoint (k : ℕ) (hk : k ∈ Finset.Icc 1 (2 * r)) :
          specialLocalIndicator p (l ^ (2 * r - k)) *
              specialLocalLogCoeff p l k =
            (if Even k then (2 : ℝ) else 0) * Real.log l := by
        have hkI := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        rw [specialLocalLogCoeff, if_neg hk0, if_pos hobs]
        by_cases hke : Even k
        · rcases hke with ⟨s, hs⟩
          have hdiff : Even (2 * r - k) := ⟨r - s, by omega⟩
          have hke' : Even k := ⟨s, hs⟩
          have hdiffNotOdd : ¬ Odd (2 * r - k) :=
            Nat.not_odd_iff_even.mpr hdiff
          simp [hke', hdiffNotOdd, specialLocalIndicator_prime_pow hl, hobs]
        · simp [hke]
      calc
        specialLocalIndicator p (l ^ (2 * r)) *
            Real.log ((l ^ (2 * r) : ℕ) : ℝ) =
            (2 * r : ℝ) * Real.log l := by
              rw [hind, one_mul, Nat.cast_pow, Real.log_pow]
              push_cast
              ring
        _ = (∑ k ∈ Finset.Icc 1 (2 * r),
              if Even k then (2 : ℝ) else 0) * Real.log l := by
              rw [sum_Icc_even_two]
        _ = ∑ k ∈ Finset.Icc 1 (2 * r),
              specialLocalIndicator p (l ^ (2 * r - k)) *
                specialLocalLogCoeff p l k := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k hk
              exact (hsumPoint k hk).symm
    · have heodd : Odd e := Nat.not_even_iff_odd.mp he
      rw [specialLocalIndicator_prime_pow hl]
      simp only [hobs, true_and, heodd, if_pos, zero_mul]
      apply (Finset.sum_eq_zero ?_).symm
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      have hk0 : k ≠ 0 := by omega
      rw [specialLocalLogCoeff, if_neg hk0, if_pos hobs]
      by_cases hke : Even k
      · rcases heodd with ⟨r, hr⟩
        rcases hke with ⟨s, hs⟩
        have hdiff : Odd (e - k) := ⟨r - s, by omega⟩
        have hke' : Even k := ⟨s, hs⟩
        rw [specialLocalIndicator_prime_pow hl]
        simp [hobs, hke', hdiff]
      · simp [hke]
  · rw [specialLocalIndicator_prime_pow hl]
    simp only [hobs, false_and, if_false]
    rw [Nat.cast_pow, Real.log_pow]
    calc
      (1 : ℝ) * ((e : ℝ) * Real.log l) =
          ∑ k ∈ Finset.Icc 1 e, Real.log l := by simp
      _ = ∑ k ∈ Finset.Icc 1 e,
          specialLocalIndicator p (l ^ (e - k)) *
            specialLocalLogCoeff p l k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkI := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        rw [specialLocalLogCoeff, if_neg hk0, if_neg hobs,
          specialLocalIndicator_prime_pow hl]
        simp [hobs]

/-- Cumulative logarithmic-derivative mass through `Q`. -/
noncomputable def specialLocalLogMass (p Q : ℕ) : ℝ :=
  ∑ l ∈ (Q + 1).primesBelow,
    ∑ k ∈ Finset.Icc 1 (Nat.log l Q), specialLocalLogCoeff p l k

/-- The first-prime-power part of the logarithmic derivative: exactly the
logarithmic mass of primes which are not quadratic obstructions. -/
noncomputable def specialAllowedPrimeLog (p Q : ℕ) : ℝ :=
  ∑ l ∈ (Q + 1).primesBelow,
    if IsQuadraticObstruction (p ^ 3) l then 0 else Real.log l

theorem specialAllowedPrimeLog_le_specialLocalLogMass (p Q : ℕ) :
    specialAllowedPrimeLog p Q ≤ specialLocalLogMass p Q := by
  classical
  unfold specialAllowedPrimeLog specialLocalLogMass
  apply Finset.sum_le_sum
  intro l hlmem
  have hl : l.Prime := Nat.prime_of_mem_primesBelow hlmem
  have hlQ : l ≤ Q := by
    have := (Nat.mem_primesBelow.mp hlmem).1
    omega
  have hlog : 1 ≤ Nat.log l Q :=
    Nat.le_log_of_pow_le hl.one_lt (by simpa using hlQ)
  have hmem : 1 ∈ Finset.Icc 1 (Nat.log l Q) :=
    Finset.mem_Icc.mpr ⟨le_rfl, hlog⟩
  have hcoeff :
      (if IsQuadraticObstruction (p ^ 3) l then 0 else Real.log l) =
        specialLocalLogCoeff p l 1 := by
    unfold specialLocalLogCoeff
    by_cases hobs : IsQuadraticObstruction (p ^ 3) l <;> simp [hobs]
  rw [hcoeff]
  exact Finset.single_le_sum
    (fun k _ => specialLocalLogCoeff_nonneg p k hl) hmem

/-- The square unit residue classes modulo an odd prime. -/
noncomputable def squareUnitClasses (p : ℕ) [Fact p.Prime] :
    Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ.filter fun u => u ∈ unitSquareSubgroup p

theorem card_squareUnitClasses {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (squareUnitClasses p).card = (p - 1) / 2 := by
  classical
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
  have heven : 2 ∣ p - 1 := by omega
  have hgcd : (p - 1).gcd 2 = 2 := Nat.gcd_eq_right heven
  have hrange : Nat.card (unitSquareSubgroup p) = (p - 1) / 2 := by
    rw [unitSquareSubgroup, IsCyclic.card_powMonoidHom_range,
      Nat.card_eq_fintype_card, ZMod.card_units, hgcd]
  calc
    (squareUnitClasses p).card =
        Fintype.card {u : (ZMod p)ˣ // u ∈ unitSquareSubgroup p} := by
      simpa [squareUnitClasses] using
        (Fintype.card_subtype
          (fun u : (ZMod p)ˣ => u ∈ unitSquareSubgroup p)).symm
    _ = Nat.card (unitSquareSubgroup p) := by
      rw [Nat.card_eq_fintype_card]
    _ = (p - 1) / 2 := hrange

/-- Sum of the fixed-modulus Chebyshev functions over all square unit
classes. -/
noncomputable def squareUnitThetaSum (p : ℕ) [Fact p.Prime] (x : ℝ) : ℝ :=
  ∑ u ∈ squareUnitClasses p,
    Erdos387.thetaAP p (u.1 : ZMod p).val x

/-- The PNT in arithmetic progressions, summed over the half of the reduced
classes which are squares.  A deliberately slack coefficient is convenient
when the finitely many primes `2` and `p` are removed below. -/
theorem eventually_squareUnitThetaSum_lower
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) * (N : ℝ) ≤ squareUnitThetaSum p N := by
  let R := squareUnitClasses p
  have hp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hp.one_le
  have hAll : ∀ᶠ N : ℕ in atTop, ∀ u ∈ R,
      (1 / 2 : ℝ) * ((N : ℝ) / (p.totient : ℝ)) ≤
        Erdos387.thetaAP p (u.1 : ZMod p).val N := by
    rw [Finset.eventually_all]
    intro u hu
    have huCop : (u.1 : ZMod p).val.Coprime p :=
      (ZMod.isUnit_iff_coprime _ _).mp (by
        simpa only [ZMod.natCast_zmod_val] using u.isUnit)
    have huLt : (u.1 : ZMod p).val < p := ZMod.val_lt _
    have hreal := Erdos387.eventually_thetaAP_abs_sub_le
      hp1 huCop huLt (η := (1 / 2 : ℝ)) (by norm_num)
    have hnat :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
    filter_upwards [hnat, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    have hmain : 0 < (N : ℝ) / (p.totient : ℝ) := by
      have hphi : 0 < p.totient := Nat.totient_pos.mpr hp1
      positivity
    linarith
  filter_upwards [hAll] with N hN
  have hpEven : 2 * ((p - 1) / 2) = p - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : p % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).2 hp2
      omega)
  have hphiNat : p.totient = p - 1 := Nat.totient_prime hp
  have hcardNat : 2 * R.card = p.totient := by
    dsimp [R]
    rw [card_squareUnitClasses hp2, hphiNat]
    exact hpEven
  have hcardReal : 2 * (R.card : ℝ) = (p.totient : ℝ) := by
    exact_mod_cast hcardNat
  have hphiPos : (0 : ℝ) < p.totient := by
    exact_mod_cast Nat.totient_pos.mpr hp1
  calc
    (1 / 4 : ℝ) * (N : ℝ) =
        (R.card : ℝ) * ((1 / 2 : ℝ) *
          ((N : ℝ) / (p.totient : ℝ))) := by
            field_simp
            nlinarith
    _ = ∑ _u ∈ R,
          (1 / 2 : ℝ) * ((N : ℝ) / (p.totient : ℝ)) := by simp
    _ ≤ ∑ u ∈ R, Erdos387.thetaAP p (u.1 : ZMod p).val N :=
      Finset.sum_le_sum hN
    _ = squareUnitThetaSum p N := rfl

/-- Odd primes in square unit classes, collected without duplication. -/
noncomputable def squareUnitPrimeTail (p N : ℕ) [Fact p.Prime] : Finset ℕ :=
  (squareUnitClasses p).biUnion fun u =>
    Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N

private theorem pairwiseDisjoint_squareUnitPrimeTail
    (p N : ℕ) [Fact p.Prime] :
    (((squareUnitClasses p : Finset (ZMod p)ˣ) : Set (ZMod p)ˣ)).PairwiseDisjoint
      (fun u => Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N) := by
  intro u hu v hv huv
  change Disjoint
    (Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N)
    (Erdos387.primeIntervalAP p (v.1 : ZMod p).val 2 N)
  rw [Finset.disjoint_left]
  intro l hlu hlv
  have hluMod := (Finset.mem_filter.mp hlu).2.2
  have hlvMod := (Finset.mem_filter.mp hlv).2.2
  apply huv
  apply Units.ext
  apply ZMod.val_injective p
  exact hluMod.symm.trans hlvMod

theorem squareUnitThetaSum_sub_eq_tail_sum
    {p N : ℕ} [Fact p.Prime] (hN : 2 ≤ N) :
    squareUnitThetaSum p N - squareUnitThetaSum p 2 =
      ∑ l ∈ squareUnitPrimeTail p N, Real.log l := by
  classical
  unfold squareUnitThetaSum squareUnitPrimeTail
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ u ∈ squareUnitClasses p,
        (Erdos387.thetaAP p (u.1 : ZMod p).val N -
          Erdos387.thetaAP p (u.1 : ZMod p).val 2)) =
        ∑ u ∈ squareUnitClasses p,
          ∑ l ∈ Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N,
            Real.log l := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Erdos387.thetaAP_sub_eq_sum_interval _ _ (by exact_mod_cast hN)
    _ = ∑ l ∈ (squareUnitClasses p).biUnion
          (fun u => Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N),
          Real.log l := by
      exact (Finset.sum_biUnion (pairwiseDisjoint_squareUnitPrimeTail p N)).symm

private theorem not_obstruction_of_mem_squareUnitAP
    {p l N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    {u : (ZMod p)ˣ} (hu : u ∈ squareUnitClasses p)
    (hlmem : l ∈ Erdos387.primeIntervalAP p (u.1 : ZMod p).val 2 N) :
    ¬ IsQuadraticObstruction (p ^ 3) l := by
  have hp : p.Prime := Fact.out
  have hldata := Finset.mem_filter.mp hlmem
  have hlI := Finset.mem_Ioc.mp hldata.1
  have hl : l.Prime := hldata.2.1
  have hlmod : l % p = (u.1 : ZMod p).val := hldata.2.2
  have hlgt2 : 2 < l := by simpa using hlI.1
  have hl2 : l ≠ 2 := by omega
  have huSub : u ∈ unitSquareSubgroup p := by
    simpa [squareUnitClasses] using hu
  have huSq : IsSquare (u.1 : ZMod p) :=
    (mem_unitSquareSubgroup_iff u).mp huSub
  have hcast : (l : ZMod p) = (u.1 : ZMod p) := by
    calc
      (l : ZMod p) = ((u.1 : ZMod p).val : ZMod p) := by
        apply (ZMod.natCast_eq_natCast_iff' l (u.1 : ZMod p).val p).2
        simpa [Nat.mod_eq_of_lt (ZMod.val_lt (u.1 : ZMod p))] using hlmod
      _ = (u.1 : ZMod p) := ZMod.natCast_zmod_val _
  have hlsq : IsSquare (l : ZMod p) := by simpa [hcast] using huSq
  have hlcast0 : (l : ZMod p) ≠ 0 := by
    rw [hcast]
    exact u.ne_zero
  have hleg : legendreSym p (l : ℤ) = 1 :=
    (legendreSym.eq_one_iff (p := p) (a := (l : ℤ))
      (by simpa using hlcast0)).2 (by simpa using hlsq)
  have hpl : p ≠ l := by
    intro h
    subst l
    have huval0 : (u.1 : ZMod p).val = 0 := by simpa using hlmod.symm
    exact u.ne_zero ((ZMod.val_eq_zero _).mp huval0)
  let _ : Fact l.Prime := ⟨hl⟩
  intro hobs
  have hneg := (isQuadraticObstruction_primeCube_iff_of_ne_two
    hp4 hl2 hpl).mp hobs
  omega

theorem squareUnitPrimeTail_subset_allowed
    {p N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    squareUnitPrimeTail p N ⊆
      ((N + 1).primesBelow.filter
        (fun l => ¬ IsQuadraticObstruction (p ^ 3) l)) := by
  intro l hlmem
  rw [squareUnitPrimeTail, Finset.mem_biUnion] at hlmem
  rcases hlmem with ⟨u, hu, hlu⟩
  have hldata := Finset.mem_filter.mp hlu
  have hlI := Finset.mem_Ioc.mp hldata.1
  have hl : l.Prime := hldata.2.1
  have hlN : l ≤ N := by simpa using hlI.2
  rw [Finset.mem_filter]
  exact ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hlN, hl⟩,
    not_obstruction_of_mem_squareUnitAP hp4 hu hlu⟩

theorem squareUnitPrimeTail_log_le_specialAllowedPrimeLog
    {p N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    (∑ l ∈ squareUnitPrimeTail p N, Real.log l) ≤
      specialAllowedPrimeLog p N := by
  classical
  have hsubset := squareUnitPrimeTail_subset_allowed (p := p) (N := N) hp4
  have hsum :
      (∑ l ∈ squareUnitPrimeTail p N, Real.log l) ≤
        ∑ l ∈ (N + 1).primesBelow.filter
          (fun l => ¬ IsQuadraticObstruction (p ^ 3) l), Real.log l := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro l hl _
    have hlprime : l.Prime :=
      Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hl).1
    exact Real.log_nonneg (by exact_mod_cast hlprime.one_le)
  refine hsum.trans_eq ?_
  unfold specialAllowedPrimeLog
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hobs : IsQuadraticObstruction (p ^ 3) l <;> simp [hobs]

/-- The logarithmic derivative has a uniform positive linear main term for
every fixed prime coefficient.  Only the threshold depends on `p`; the
coefficient `1/8` is absolute. -/
theorem eventually_specialLocalLogMass_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      (1 / 8 : ℝ) * (Q : ℝ) ≤ specialLocalLogMass p Q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let C : ℝ := squareUnitThetaSum p 2
  have hC : ∀ᶠ Q : ℕ in atTop, 8 * C ≤ (Q : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (8 * C))
  filter_upwards [eventually_squareUnitThetaSum_lower hp2, hC,
      eventually_ge_atTop 2] with Q htheta hCQ hQ2
  have htail := squareUnitThetaSum_sub_eq_tail_sum (p := p) hQ2
  calc
    (1 / 8 : ℝ) * (Q : ℝ) ≤ squareUnitThetaSum p Q - C := by
      dsimp [C] at hCQ ⊢
      linarith
    _ = ∑ l ∈ squareUnitPrimeTail p Q, Real.log l := htail
    _ ≤ specialAllowedPrimeLog p Q :=
      squareUnitPrimeTail_log_le_specialAllowedPrimeLog hp4
    _ ≤ specialLocalLogMass p Q :=
      specialAllowedPrimeLog_le_specialLocalLogMass p Q

/-- A fixed-modulus logarithmic-saving estimate extracted from the proved
Siegel--Walfisz/Bombieri--Vinogradov endpoint theorem. -/
theorem exists_eventually_fixed_modulus_centered_discrepancy
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q ≤
        K * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
  obtain ⟨C, c, hC, hc, X0, hX0, hmain⟩ :=
    BoundedGaps.Maynard.exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_logSaving_allCutoffs
      3 (by norm_num)
  let K : ℝ := C + 40 *
    BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneTwoConstant
      (Real.log 4 + 4)
  have hlogTendsto : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcutoffTendsto : Tendsto
      (fun x : ℕ =>
        BoundedGaps.Maynard.siegelWalfiszConductorCutoff (3 + 5) x)
      atTop atTop := by
    exact tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 + 5)).comp hlogTendsto)
  obtain ⟨Xrange, hXrange4, hXrange⟩ :=
    BoundedGaps.Maynard.exists_siegelWalfiszConductorCutoff_le_logReducedSqrt 3
  have hqcut : ∀ᶠ x : ℕ in atTop,
      q ≤ BoundedGaps.Maynard.siegelWalfiszConductorCutoff (3 + 5) x :=
    hcutoffTendsto.eventually (eventually_ge_atTop q)
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop X0, eventually_ge_atTop Xrange, hqcut]
      with x hx0 hxrange hqcutx
  have hcutRange := hXrange x hxrange
  have hqRange : (q : ℝ) ≤ Real.sqrt (x : ℝ) /
      Real.rpow (Real.log (x : ℝ)) (3 + 5) := by
    exact (Nat.cast_le.mpr hqcutx).trans (by simpa using hcutRange)
  have hsum := hmain x hx0 q hqRange
  have hsingle :
      BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q ≤
        ∑ r ∈ Finset.Icc 1 q,
          BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x r := by
    exact Finset.single_le_sum
      (fun r _ =>
        BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo_nonneg x r)
      (Finset.mem_Icc.mpr ⟨hq, le_rfl⟩)
  exact hsingle.trans (by
    simpa [K, Real.rpow_natCast] using hsum)

/-- The strong PNT estimate, weakened to an integrable third logarithmic
power for use in the Volterra recurrence. -/
theorem exists_eventually_chebyshevPsi_log_saving :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      |Chebyshev.psi (x : ℝ) - (x : ℝ)| ≤
        K * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
  obtain ⟨C, c, hC, hc, X0, hX0, hpsi⟩ :=
    BoundedGaps.PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  have huTop : Tendsto
      (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpolyRaw :=
    ((isLittleO_rpow_exp_pos_mul_atTop 6 hc).comp_tendsto huTop).eventuallyLE
  have hpoly : ∀ᶠ x : ℕ in atTop,
      Real.rpow (Real.sqrt (Real.log (x : ℝ))) (6 : ℝ) ≤
        Real.exp (c * Real.sqrt (Real.log (x : ℝ))) := by
    filter_upwards [hpolyRaw] with x hx
    simp only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hx
    exact (le_abs_self _).trans hx
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop X0, hpoly, eventually_ge_atTop 4]
      with x hx0 hpolyx hx4
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hsqrt : Real.sqrt (Real.log (x : ℝ)) ^ 2 =
      Real.log (x : ℝ) := Real.sq_sqrt hlogpos.le
  have hpowId :
      Real.rpow (Real.sqrt (Real.log (x : ℝ))) (6 : ℝ) =
        Real.log (x : ℝ) ^ 3 := by
    calc
      Real.rpow (Real.sqrt (Real.log (x : ℝ))) (6 : ℝ) =
          Real.sqrt (Real.log (x : ℝ)) ^ (6 : ℕ) :=
        Real.rpow_natCast _ 6
      _ =
          (Real.sqrt (Real.log (x : ℝ)) ^ 2) ^ 3 := by ring
      _ = Real.log (x : ℝ) ^ 3 := by rw [hsqrt]
  have hdecay :
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) ≤
        1 / Real.log (x : ℝ) ^ 3 := by
    rw [show -c * Real.sqrt (Real.log (x : ℝ)) =
      -(c * Real.sqrt (Real.log (x : ℝ))) by ring, Real.exp_neg]
    have hdenpos : 0 < Real.log (x : ℝ) ^ 3 := pow_pos hlogpos 3
    have hpoly2 : Real.log (x : ℝ) ^ 3 ≤
        Real.exp (c * Real.sqrt (Real.log (x : ℝ))) := by
      rw [← hpowId]
      exact hpolyx
    have := one_div_le_one_div_of_le hdenpos hpoly2
    simpa [one_div] using this
  exact (hpsi x hx0).trans (by
    calc
      C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) =
          (C * (x : ℝ)) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) := by ring
      _ ≤ (C * (x : ℝ)) * (1 / Real.log (x : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hdecay
          (mul_nonneg hC.le (Nat.cast_nonneg x))
      _ = C * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by ring)

private theorem centeredProgressionDiscrepancy_le_max
    {x q a : ℕ} (hx : 2 ≤ x) (hq : 0 < q)
    (haLt : a < q) (haCop : a.Coprime q) :
    |BoundedGaps.Maynard.chebyshevProgressionSum x q a -
        Chebyshev.psi (x : ℝ) / (q.totient : ℝ)| ≤
      BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q := by
  rw [BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    hx hq]
  apply Finset.le_sup'_of_le
    (fun y => (BoundedGaps.Maynard.coprimeResidues q).sup'
      (BoundedGaps.Maynard.coprimeResidues_nonempty hq)
      (fun b => |BoundedGaps.Maynard.chebyshevProgressionSum y q b -
        Chebyshev.psi (y : ℝ) / (q.totient : ℝ)|))
    (Finset.mem_Icc.mpr ⟨hx, le_rfl⟩)
  apply Finset.le_sup'_of_le
    (fun b => |BoundedGaps.Maynard.chebyshevProgressionSum x q b -
      Chebyshev.psi (x : ℝ) / (q.totient : ℝ)|)
  · show a ∈ BoundedGaps.Maynard.coprimeResidues q
    rw [BoundedGaps.Maynard.coprimeResidues, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨haLt, haCop⟩
  · exact le_rfl

/-- The von Mangoldt mass in the square reduced residue classes modulo `p`. -/
noncomputable def squareUnitChebyshevSum (p Q : ℕ) [Fact p.Prime] : ℝ :=
  ∑ u ∈ squareUnitClasses p,
    BoundedGaps.Maynard.chebyshevProgressionSum Q p
      (u.1 : ZMod p).val

/-- Summing the strong fixed-modulus PNT over the square classes gives the
sharp coefficient `1/2`, with an integrable logarithmic error. -/
theorem exists_eventually_squareUnitChebyshevSum_lower
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ K : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        squareUnitChebyshevSum p Q := by
  have hp : p.Prime := Fact.out
  obtain ⟨Kd, hdisc⟩ :=
    exists_eventually_fixed_modulus_centered_discrepancy p hp.one_le
  obtain ⟨Kpsi, hpsi⟩ := exists_eventually_chebyshevPsi_log_saving
  let R := squareUnitClasses p
  let E : ℝ := Kd + Kpsi / (p.totient : ℝ)
  let K : ℝ := (R.card : ℝ) * E
  refine ⟨K, ?_⟩
  filter_upwards [hdisc, hpsi, eventually_ge_atTop 4]
      with Q hdiscQ hpsiQ hQ4
  have hlogpos : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hphiPos : (0 : ℝ) < p.totient := by
    exact_mod_cast Nat.totient_pos.mpr hp.one_le
  have hpoint : ∀ u ∈ R,
      (Q : ℝ) / (p.totient : ℝ) -
          E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        BoundedGaps.Maynard.chebyshevProgressionSum Q p
          (u.1 : ZMod p).val := by
    intro u hu
    have huLt : (u.1 : ZMod p).val < p := ZMod.val_lt _
    have huCop : (u.1 : ZMod p).val.Coprime p :=
      (ZMod.isUnit_iff_coprime _ _).mp (by
        simpa only [ZMod.natCast_zmod_val] using u.isUnit)
    have huDisc := centeredProgressionDiscrepancy_le_max
      (x := Q) (q := p) (a := (u.1 : ZMod p).val)
      (by omega) hp.pos huLt huCop
    have huLower :
        Chebyshev.psi (Q : ℝ) / (p.totient : ℝ) -
            Kd * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
          BoundedGaps.Maynard.chebyshevProgressionSum Q p
            (u.1 : ZMod p).val := by
      rw [abs_le] at huDisc
      linarith
    have hpsiLower :
        (Q : ℝ) - Kpsi * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
          Chebyshev.psi (Q : ℝ) := by
      rw [abs_le] at hpsiQ
      linarith
    calc
      (Q : ℝ) / (p.totient : ℝ) -
          E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
          ((Q : ℝ) - Kpsi * (Q : ℝ) /
              Real.log (Q : ℝ) ^ 3) / (p.totient : ℝ) -
            Kd * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
        dsimp [E]
        field_simp
        ring
      _ ≤ Chebyshev.psi (Q : ℝ) / (p.totient : ℝ) -
            Kd * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
        exact sub_le_sub_right
          (div_le_div_of_nonneg_right hpsiLower hphiPos.le) _
      _ ≤ BoundedGaps.Maynard.chebyshevProgressionSum Q p
            (u.1 : ZMod p).val := huLower
  have hpEven : 2 * ((p - 1) / 2) = p - 1 := by
    exact Nat.mul_div_cancel' (by
      have hodd : p % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp2
      omega)
  have hcardNat : 2 * R.card = p.totient := by
    dsimp [R]
    rw [card_squareUnitClasses hp2, Nat.totient_prime hp]
    exact hpEven
  have hcardReal : 2 * (R.card : ℝ) = (p.totient : ℝ) := by
    exact_mod_cast hcardNat
  have hmainEq :
      (R.card : ℝ) * ((Q : ℝ) / (p.totient : ℝ)) =
        (1 / 2 : ℝ) * (Q : ℝ) := by
    field_simp
    simpa [mul_comm] using hcardReal
  calc
    (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
        (R.card : ℝ) * ((Q : ℝ) / (p.totient : ℝ)) -
          (R.card : ℝ) * E * (Q : ℝ) /
            Real.log (Q : ℝ) ^ 3 := by
      rw [hmainEq]
    _ =
        (R.card : ℝ) *
          ((Q : ℝ) / (p.totient : ℝ) -
            E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
      ring
    _ = ∑ _u ∈ R,
          ((Q : ℝ) / (p.totient : ℝ) -
            E * (Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_sub]
    _ ≤ ∑ u ∈ R,
        BoundedGaps.Maynard.chebyshevProgressionSum Q p
          (u.1 : ZMod p).val := Finset.sum_le_sum hpoint
    _ = squareUnitChebyshevSum p Q := rfl

private theorem thetaAP_nat_eq_thetaProgressionSum
    {q a Q : ℕ} (ha : a < q) :
    Erdos387.thetaAP q a Q =
      BoundedGaps.Maynard.thetaProgressionSum Q q a := by
  rw [Erdos387.thetaAP_eq_sum_filter]
  unfold BoundedGaps.Maynard.thetaProgressionSum
  rw [Nat.primesLE_eq_filter_Icc_one]
  apply Finset.sum_congr
  · ext l
    simp [Nat.mod_eq_of_lt ha, and_left_comm, and_comm]
    exact fun _ _ hl => hl.one_le
  · intro l hl
    rfl

/-- Higher prime powers contribute only an integrable logarithmic error to
the Chebyshev mass. -/
private theorem exists_eventually_psi_sub_theta_log_saving :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
        K * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlogTendsto : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpolyRaw :=
    ((isLittleO_rpow_exp_pos_mul_atTop 3
      (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hlogTendsto).eventuallyLE
  have hpoly : ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ^ 3 ≤ Real.sqrt (x : ℝ) := by
    filter_upwards [hpolyRaw, eventually_ge_atTop 2] with x hx hx2
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hxpos : (0 : ℝ) < x := by positivity
    have hx' : Real.rpow (Real.log (x : ℝ)) (3 : ℝ) ≤
        Real.exp ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by
      have hrpowpos : 0 < Real.rpow (Real.log (x : ℝ)) (3 : ℝ) :=
        Real.rpow_pos_of_pos hlogpos _
      change ‖Real.rpow (Real.log (x : ℝ)) (3 : ℝ)‖ ≤
        ‖Real.exp ((1 / 2 : ℝ) * Real.log (x : ℝ))‖ at hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpowpos,
        abs_of_pos (Real.exp_pos _)] at hx
      exact hx
    calc
      Real.log (x : ℝ) ^ 3 =
          Real.rpow (Real.log (x : ℝ)) (3 : ℝ) := by
        exact (Real.rpow_natCast _ 3).symm
      _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (x : ℝ)) := hx'
      _ = Real.sqrt (x : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxpos]
        congr 1
        ring
  refine ⟨|C|, ?_⟩
  filter_upwards [hpoly, eventually_ge_atTop 2] with x hpolyx hx2
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hsqrt : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtBound : Real.sqrt (x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 3 := by
    rw [le_div_iff₀ (pow_pos hlogpos 3)]
    calc
      Real.sqrt (x : ℝ) * Real.log (x : ℝ) ^ 3 ≤
          Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_left hpolyx (Real.sqrt_nonneg _)
      _ = (x : ℝ) := by nlinarith
  calc
    Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
        C * Real.sqrt (x : ℝ) := hC _
    _ ≤ |C| * Real.sqrt (x : ℝ) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * ((x : ℝ) / Real.log (x : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hsqrtBound (abs_nonneg C)
    _ = |C| * (x : ℝ) / Real.log (x : ℝ) ^ 3 := by ring

/-- The square-class theta mass has its exact density-one-half main term,
with an integrable third-logarithmic-power error. -/
theorem exists_eventually_squareUnitThetaSum_sharp_lower
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ K : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        squareUnitThetaSum p Q := by
  obtain ⟨Kψ, hψ⟩ := exists_eventually_psi_sub_theta_log_saving
  obtain ⟨Kχ, hχ⟩ := exists_eventually_squareUnitChebyshevSum_lower
    (p := p) hp2
  let R := squareUnitClasses p
  let K : ℝ := Kχ + (R.card : ℝ) * Kψ
  refine ⟨K, ?_⟩
  filter_upwards [hψ, hχ] with Q hψQ hχQ
  let Δ : ℝ := Chebyshev.psi (Q : ℝ) - Chebyshev.theta (Q : ℝ)
  have hpoint : ∀ u ∈ R,
      BoundedGaps.Maynard.chebyshevProgressionSum Q p
          (u.1 : ZMod p).val - Δ ≤
        Erdos387.thetaAP p (u.1 : ZMod p).val Q := by
    intro u hu
    have hsplit :=
      BoundedGaps.Maynard.chebyshevProgressionSum_eq_thetaProgressionSum_add_remainder
        Q p (u.1 : ZMod p).val
    have hrem :=
      BoundedGaps.Maynard.progressionPrimePowerRemainder_le_psi_sub_theta
        Q p (u.1 : ZMod p).val
    rw [thetaAP_nat_eq_thetaProgressionSum (ZMod.val_lt _)]
    dsimp only [Δ]
    linarith
  have hthetaBridge : squareUnitChebyshevSum p Q - (R.card : ℝ) * Δ ≤
      squareUnitThetaSum p Q := by
    calc
      squareUnitChebyshevSum p Q - (R.card : ℝ) * Δ =
          ∑ u ∈ R,
            (BoundedGaps.Maynard.chebyshevProgressionSum Q p
              (u.1 : ZMod p).val - Δ) := by
        unfold squareUnitChebyshevSum
        rw [Finset.sum_sub_distrib]
        simp [R, nsmul_eq_mul]
      _ ≤ ∑ u ∈ R, Erdos387.thetaAP p (u.1 : ZMod p).val Q :=
        Finset.sum_le_sum hpoint
      _ = squareUnitThetaSum p Q := rfl
  have hR : Δ ≤ Kψ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
    simpa only [Δ] using hψQ
  calc
    (1 / 2 : ℝ) * (Q : ℝ) -
        K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
        ((1 / 2 : ℝ) * (Q : ℝ) -
          Kχ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3) -
          (R.card : ℝ) *
            (Kψ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
      dsimp [K]
      ring
    _ ≤ squareUnitChebyshevSum p Q - (R.card : ℝ) * Δ := by
      exact sub_le_sub hχQ
        (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _))
    _ ≤ squareUnitThetaSum p Q := hthetaBridge

/-- The local logarithmic derivative has the exact density-one-half main
term.  The fixed subtraction is the finite contribution through `2`; it is
kept explicit so that no endpoint-dependent information is discarded. -/
theorem exists_eventually_specialLocalLogMass_sharp_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ K C : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        specialLocalLogMass p Q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, htheta⟩ :=
    exists_eventually_squareUnitThetaSum_sharp_lower (p := p) hp2
  let C : ℝ := squareUnitThetaSum p 2
  refine ⟨K, C, ?_⟩
  filter_upwards [htheta, eventually_ge_atTop 2] with Q hthetaQ hQ2
  have htail := squareUnitThetaSum_sub_eq_tail_sum (p := p) hQ2
  calc
    (1 / 2 : ℝ) * (Q : ℝ) -
        K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        squareUnitThetaSum p Q - C := sub_le_sub_right hthetaQ C
    _ = ∑ l ∈ squareUnitPrimeTail p Q, Real.log l := by
      simpa only [C] using htail
    _ ≤ specialAllowedPrimeLog p Q :=
      squareUnitPrimeTail_log_le_specialAllowedPrimeLog hp4
    _ ≤ specialLocalLogMass p Q :=
      specialAllowedPrimeLog_le_specialLocalLogMass p Q

/-- A fixed additive loss is absorbed by the third-logarithmic-power error
scale. -/
private theorem eventually_one_le_natCast_div_log_cube :
    ∀ᶠ Q : ℕ in atTop,
      (1 : ℝ) ≤ (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
  have hlogTendsto : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpolyRaw :=
    ((isLittleO_rpow_exp_pos_mul_atTop 3
      (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hlogTendsto).eventuallyLE
  filter_upwards [hpolyRaw, eventually_ge_atTop 2] with Q hpolyRawQ hQ2
  have hlogpos : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hQpos : (0 : ℝ) < Q := by positivity
  have hrpowpos : 0 < Real.rpow (Real.log (Q : ℝ)) (3 : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hpolyRpow : Real.rpow (Real.log (Q : ℝ)) (3 : ℝ) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log (Q : ℝ)) := by
    change ‖Real.rpow (Real.log (Q : ℝ)) (3 : ℝ)‖ ≤
      ‖Real.exp ((1 / 2 : ℝ) * Real.log (Q : ℝ))‖ at hpolyRawQ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpowpos,
      abs_of_pos (Real.exp_pos _)] at hpolyRawQ
    exact hpolyRawQ
  have hpoly : Real.log (Q : ℝ) ^ 3 ≤ Real.sqrt (Q : ℝ) := by
    calc
      Real.log (Q : ℝ) ^ 3 =
          Real.rpow (Real.log (Q : ℝ)) (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (Q : ℝ)) := hpolyRpow
      _ = Real.sqrt (Q : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hQpos]
        congr 1
        ring
  have hsqrtQ : Real.sqrt (Q : ℝ) ≤ (Q : ℝ) := by
    have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
    have hsqrtSq : Real.sqrt (Q : ℝ) ^ 2 = (Q : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hsqrtNonneg := Real.sqrt_nonneg (Q : ℝ)
    nlinarith
  rw [le_div_iff₀ (pow_pos hlogpos 3)]
  simpa only [one_mul] using hpoly.trans hsqrtQ

/-- Clean sharp form of the local logarithmic-derivative estimate. -/
theorem exists_eventually_specialLocalLogMass_half_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ K : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
        specialLocalLogMass p Q := by
  obtain ⟨K, C, hmass⟩ :=
    exists_eventually_specialLocalLogMass_sharp_lower hp hp4
  refine ⟨K + |C|, ?_⟩
  filter_upwards [hmass, eventually_one_le_natCast_div_log_cube]
      with Q hmassQ hratio
  have hC : C ≤ |C| * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
    calc
      C ≤ |C| := le_abs_self C
      _ ≤ |C| * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hratio (abs_nonneg C))
  calc
    (1 / 2 : ℝ) * (Q : ℝ) -
        (K + |C|) * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
        (1 / 2 : ℝ) * (Q : ℝ) -
          K * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) -
          |C| * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by ring
    _ ≤
        ((1 / 2 : ℝ) * (Q : ℝ) -
          K * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3)) - C := by
      exact sub_le_sub_left hC _
    _ =
        (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C := by
      ring
    _ ≤ specialLocalLogMass p Q := hmassQ

private abbrev LocalLogSourceIndex :=
  Sigma fun _n : ℕ => Sigma fun _l : ℕ => ℕ

private abbrev LocalLogTargetIndex :=
  Sigma fun _m : ℕ => Sigma fun _l : ℕ => ℕ

/-- Indices `(n,l,k)` with `n ≤ N`, `l | n`, and
`1 ≤ k ≤ v_l(n)`. -/
private def localLogSourceSet (N : ℕ) : Finset LocalLogSourceIndex :=
  (Finset.Icc 1 N).sigma fun n =>
    n.primeFactors.sigma fun l => Finset.Icc 1 (n.factorization l)

/-- Convolution indices `(m,l,k)` with `m l^k ≤ N`. -/
private def localLogTargetSet (N : ℕ) : Finset LocalLogTargetIndex :=
  (Finset.Icc 1 N).sigma fun m =>
    ((N / m + 1).primesBelow).sigma fun l =>
      Finset.Icc 1 (Nat.log l (N / m))

/-- Removing `l^k` from a source integer produces its convolution index. -/
private def localLogSourceToTarget (z : LocalLogSourceIndex) :
    LocalLogTargetIndex :=
  ⟨z.1 / z.2.1 ^ z.2.2, z.2⟩

private theorem localLogSource_pow_dvd {N : ℕ} {z : LocalLogSourceIndex}
    (hz : z ∈ localLogSourceSet N) : z.2.1 ^ z.2.2 ∣ z.1 := by
  rcases z with ⟨n, l, k⟩
  simp only [localLogSourceSet, Finset.mem_sigma] at hz
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hz.2.1
  have hn0 : n ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hz.1).1)
  exact (hl.pow_dvd_iff_le_factorization hn0).2
    (Finset.mem_Icc.mp hz.2.2).2

private theorem localLogSource_reconstruct {N : ℕ}
    {z : LocalLogSourceIndex} (hz : z ∈ localLogSourceSet N) :
    (localLogSourceToTarget z).1 *
        (localLogSourceToTarget z).2.1 ^
          (localLogSourceToTarget z).2.2 = z.1 := by
  rcases z with ⟨n, l, k⟩
  exact Nat.div_mul_cancel (localLogSource_pow_dvd hz)

private theorem localLogSourceToTarget_injOn (N : ℕ) :
    Set.InjOn localLogSourceToTarget
      (localLogSourceSet N : Set LocalLogSourceIndex) := by
  intro z hz w hw heq
  have htail : z.2 = w.2 := congrArg Sigma.snd heq
  have hhead : z.1 = w.1 := by
    calc
      z.1 = (localLogSourceToTarget z).1 *
          (localLogSourceToTarget z).2.1 ^
            (localLogSourceToTarget z).2.2 :=
        (localLogSource_reconstruct hz).symm
      _ = (localLogSourceToTarget w).1 *
          (localLogSourceToTarget w).2.1 ^
            (localLogSourceToTarget w).2.2 := by rw [heq]
      _ = w.1 := localLogSource_reconstruct hw
  cases z
  cases w
  simp_all

private theorem localLogSourceToTarget_mem {N : ℕ}
    {z : LocalLogSourceIndex} (hz : z ∈ localLogSourceSet N) :
    localLogSourceToTarget z ∈ localLogTargetSet N := by
  rcases z with ⟨n, l, k⟩
  simp only [localLogSourceSet, Finset.mem_sigma] at hz
  rcases hz with ⟨hnIcc, hlmem, hkIcc⟩
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
  have hn0 : n ≠ 0 := hnpos.ne'
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hlmem
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hpowpos : 0 < l ^ k := pow_pos hl.pos k
  have hpowdvd : l ^ k ∣ n :=
    (hl.pow_dvd_iff_le_factorization hn0).2 (Finset.mem_Icc.mp hkIcc).2
  have hmpos : 0 < n / l ^ k :=
    Nat.div_pos (Nat.le_of_dvd hnpos hpowdvd) hpowpos
  have hmN : n / l ^ k ≤ N := (Nat.div_le_self n _).trans (Finset.mem_Icc.mp hnIcc).2
  have hmul : l ^ k * (n / l ^ k) ≤ N := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hpowdvd]
    exact (Finset.mem_Icc.mp hnIcc).2
  have hpowQ : l ^ k ≤ N / (n / l ^ k) := by
    rw [Nat.le_div_iff_mul_le hmpos]
    exact hmul
  have hlQ : l < N / (n / l ^ k) + 1 :=
    Nat.lt_succ_of_le ((Nat.le_self_pow hkpos.ne' l).trans hpowQ)
  have hklog : k ≤ Nat.log l (N / (n / l ^ k)) :=
    Nat.le_log_of_pow_le hl.one_lt hpowQ
  simp only [localLogSourceToTarget, localLogTargetSet, Finset.mem_sigma]
  exact ⟨Finset.mem_Icc.mpr ⟨hmpos, hmN⟩,
    Nat.mem_primesBelow.mpr ⟨hlQ, hl⟩,
    Finset.mem_Icc.mpr ⟨hkpos, hklog⟩⟩

private theorem localLogSourceToTarget_surjOn (N : ℕ) :
    ∀ w ∈ localLogTargetSet N,
      ∃ z ∈ localLogSourceSet N, localLogSourceToTarget z = w := by
  intro w hw
  rcases w with ⟨m, l, k⟩
  simp only [localLogTargetSet, Finset.mem_sigma] at hw
  rcases hw with ⟨hmIcc, hlmem, hkIcc⟩
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmIcc).1
  have hl : l.Prime := Nat.prime_of_mem_primesBelow hlmem
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hQ0 : N / m ≠ 0 := by
    intro hQ
    have : k ≤ 0 := by simpa [hQ] using (Finset.mem_Icc.mp hkIcc).2
    omega
  have hpowQ : l ^ k ≤ N / m :=
    Nat.pow_le_of_le_log hQ0 (Finset.mem_Icc.mp hkIcc).2
  have hmulN : m * l ^ k ≤ N := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hpowQ
  have hnpos : 0 < m * l ^ k := Nat.mul_pos hmpos (pow_pos hl.pos k)
  have hl_dvd : l ∣ m * l ^ k := by
    exact dvd_mul_of_dvd_right (dvd_pow_self l hkpos.ne') m
  have hlpf : l ∈ (m * l ^ k).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, hl_dvd, hnpos.ne'⟩
  have hkfac : k ≤ (m * l ^ k).factorization l := by
    apply (hl.pow_dvd_iff_le_factorization hnpos.ne').1
    exact dvd_mul_left (l ^ k) m
  let z : LocalLogSourceIndex := ⟨m * l ^ k, l, k⟩
  have hz : z ∈ localLogSourceSet N := by
    simp only [z, localLogSourceSet, Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨hnpos, hmulN⟩, hlpf,
      Finset.mem_Icc.mpr ⟨hkpos, hkfac⟩⟩
  refine ⟨z, hz, ?_⟩
  simp only [z, localLogSourceToTarget]
  congr 1
  exact Nat.mul_div_left m (pow_pos hl.pos k)

/-- The one-prime logarithmic identities assemble into an identity over all
prime powers dividing a nonzero integer. -/
private theorem specialLocalIndicator_log_eq_source_sum
    (p : ℕ) {n : ℕ} (hn : n ≠ 0) :
    specialLocalIndicator p n * Real.log (n : ℝ) =
      ∑ l ∈ n.primeFactors,
        ∑ k ∈ Finset.Icc 1 (n.factorization l),
          specialLocalIndicator p (n / l ^ k) *
            specialLocalLogCoeff p l k := by
  rw [PrimePowerConvolution448.weighted_log_eq_sum_primeFactors
    (specialLocalIndicator p) (fun {_ _} hcop =>
      specialLocalIndicator_mul_of_coprime (p := p) hcop) hn]
  apply Finset.sum_congr rfl
  intro l hlmem
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hlmem
  let e := n.factorization l
  have hdecomp : l ^ e * ordCompl[l] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n l
  rw [show ordProj[l] n = l ^ e by rfl,
    specialLocalIndicator_prime_pow_log_convolution hl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hke : k ≤ e := (Finset.mem_Icc.mp hk).2
  have hquot : n / l ^ k = l ^ (e - k) * ordCompl[l] n := by
    calc
      n / l ^ k = (l ^ e * ordCompl[l] n) / l ^ k := by rw [hdecomp]
      _ = (l ^ k * l ^ (e - k) * ordCompl[l] n) / l ^ k := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hke]
      _ = l ^ (e - k) * ordCompl[l] n := by
        rw [Nat.mul_assoc, Nat.mul_div_right _ (pow_pos hl.pos k)]
  have hcop : (l ^ (e - k)).Coprime (ordCompl[l] n) :=
    (Nat.coprime_ordCompl hl hn).pow_left _
  rw [hquot, specialLocalIndicator_mul_of_coprime (p := p) hcop]
  ring

private noncomputable def localLogSourceWeight
    (p : ℕ) (z : LocalLogSourceIndex) : ℝ :=
  specialLocalIndicator p (z.1 / z.2.1 ^ z.2.2) *
    specialLocalLogCoeff p z.2.1 z.2.2

private noncomputable def localLogTargetWeight
    (p : ℕ) (z : LocalLogTargetIndex) : ℝ :=
  specialLocalIndicator p z.1 *
    specialLocalLogCoeff p z.2.1 z.2.2

private theorem localLogSourceWeight_map
    (p : ℕ) (z : LocalLogSourceIndex) :
    localLogSourceWeight p z =
      localLogTargetWeight p (localLogSourceToTarget z) := by
  rfl

/-- Exact global logarithmic convolution for the complete local norm
indicator.  Unlike the generic upper-bound convolution, no terms are lost:
the source and target index sets above are in bijection. -/
theorem specialLocalIndicator_log_convolution (p N : ℕ) :
    HalberstamScratch.logPartialSum (specialLocalIndicator p) N =
      ∑ m ∈ Finset.Icc 1 N,
        specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
  let e : {z // z ∈ localLogSourceSet N} ↪ LocalLogTargetIndex :=
    ⟨fun z => localLogSourceToTarget z.1,
      fun z w hzw =>
        Subtype.ext (localLogSourceToTarget_injOn N z.2 w.2 hzw)⟩
  let U : Finset LocalLogTargetIndex := (localLogSourceSet N).attach.map e
  have hsource :
      HalberstamScratch.logPartialSum (specialLocalIndicator p) N =
        ∑ z ∈ localLogSourceSet N, localLogSourceWeight p z := by
    unfold HalberstamScratch.logPartialSum localLogSourceSet
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_sigma]
    exact specialLocalIndicator_log_eq_source_sum p
      (Nat.ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
  have hU : U = localLogTargetSet N := by
    ext w
    constructor
    · intro hw
      rw [Finset.mem_map] at hw
      rcases hw with ⟨z, hz, rfl⟩
      exact localLogSourceToTarget_mem z.2
    · intro hw
      rcases localLogSourceToTarget_surjOn N w hw with ⟨z, hz, hzw⟩
      rw [Finset.mem_map]
      exact ⟨⟨z, hz⟩, Finset.mem_attach _ _, hzw⟩
  have himage :
      (∑ z ∈ localLogSourceSet N, localLogSourceWeight p z) =
        ∑ w ∈ localLogTargetSet N, localLogTargetWeight p w := by
    rw [← hU, ← Finset.sum_attach]
    change (∑ z ∈ (localLogSourceSet N).attach,
        localLogSourceWeight p z.1) =
      ∑ w ∈ (localLogSourceSet N).attach.map e,
        localLogTargetWeight p w
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun z _ => localLogSourceWeight_map p z.1
  have htarget :
      (∑ w ∈ localLogTargetSet N, localLogTargetWeight p w) =
        ∑ m ∈ Finset.Icc 1 N,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
    unfold localLogTargetSet localLogTargetWeight specialLocalLogMass
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mul_sum]
  rw [hsource, himage, htarget]

/-- In the canonical decomposition `n = b²a` with squarefree kernel `a`,
an inert-prime valuation is even exactly when that prime does not divide
`a`.  This is the local algebra behind the square-convolution form of the
Bernays counting function. -/
theorem even_padicValNat_sq_mul_squarefree_iff
    {l a b : ℕ} (hl : l.Prime) (ha : 0 < a) (hb : 0 < b)
    (hsq : Squarefree a) :
    Even (padicValNat l (b ^ 2 * a)) ↔ ¬ l ∣ a := by
  let _ : Fact l.Prime := ⟨hl⟩
  rw [padicValNat.mul (pow_ne_zero _ hb.ne') ha.ne',
    padicValNat.pow]
  by_cases hla : l ∣ a
  · have hvala : padicValNat l a = 1 := by
      rw [← Nat.factorization_def a hl]
      exact Nat.factorization_eq_one_of_squarefree hsq hl hla
    rw [hvala]
    simp [hla, parity_simps]
  · rw [padicValNat.eq_zero_of_not_dvd hla]
    simp [hla, parity_simps]

/-- Local admissibility of `b²a`, for squarefree `a`, depends only on the
prime divisors of `a`: each of them must be split or ramified rather than an
obstruction prime. -/
theorem specialLocallyAdmissible_sq_mul_squarefree_iff
    {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hsq : Squarefree a) :
    SpecialLocallyAdmissible p (b ^ 2 * a) ↔
      ∀ l : ℕ, l.Prime → IsQuadraticObstruction (p ^ 3) l → ¬ l ∣ a := by
  constructor
  · intro h l hl hobs
    exact (even_padicValNat_sq_mul_squarefree_iff hl ha hb hsq).mp
      (h l hl hobs)
  · intro h l hl hobs
    exact (even_padicValNat_sq_mul_squarefree_iff hl ha hb hsq).mpr
      (h l hl hobs)

/-- Every positive locally admissible integer is a square times a positive
squarefree integer supported only at non-obstruction primes, and conversely.
This is the exact finite factorization to which the half-dimensional
multiplicative counting theorem is applied. -/
theorem specialLocallyAdmissible_iff_exists_squarefree_kernel
    {p n : ℕ} (hn : 0 < n) :
    SpecialLocallyAdmissible p n ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a ∧
        ∀ l : ℕ, l.Prime → IsQuadraticObstruction (p ^ 3) l → ¬ l ∣ a := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
    refine ⟨a, b, ha, hb, hab, hsq, ?_⟩
    rw [← specialLocallyAdmissible_sq_mul_squarefree_iff ha hb hsq]
    simpa only [hab] using h
  · rintro ⟨a, b, ha, hb, rfl, hsq, hsupport⟩
    exact (specialLocallyAdmissible_sq_mul_squarefree_iff ha hb hsq).mpr
      hsupport

/-- The positive decomposition of an integer as a square times a squarefree
kernel is unique.  The proof reads prime-factorization exponents modulo two;
it is used below to turn the square-convolution parametrization into an exact
cardinality identity rather than merely a surjection. -/
theorem sq_mul_squarefree_unique
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsa : Squarefree a) (hsc : Squarefree c)
    (heq : b ^ 2 * a = d ^ 2 * c) : a = c ∧ b = d := by
  have hac : a = c := by
    apply Nat.eq_of_factorization_eq ha.ne' hc.ne'
    intro q
    by_cases hq : q.Prime
    · have hf := congrArg (fun n : ℕ => n.factorization q) heq
      rw [Nat.factorization_mul (pow_ne_zero _ hb.ne') ha.ne',
        Nat.factorization_mul (pow_ne_zero _ hd.ne') hc.ne',
        Nat.factorization_pow, Nat.factorization_pow] at hf
      change 2 * b.factorization q + a.factorization q =
        2 * d.factorization q + c.factorization q at hf
      have ha1 := hsa.natFactorization_le_one q
      have hc1 := hsc.natFactorization_le_one q
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq,
        Nat.factorization_eq_zero_of_not_prime _ hq]
  subst c
  refine ⟨rfl, ?_⟩
  have hpows : b ^ 2 = d ^ 2 := Nat.eq_of_mul_eq_mul_right ha heq
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hpows

/-- Squarefree kernels whose prime factors satisfy all local conditions for
the special form. -/
def IsSpecialSquarefreeKernel (p a : ℕ) : Prop :=
  Squarefree a ∧
    ∀ l : ℕ, l.Prime → IsQuadraticObstruction (p ^ 3) l → ¬ l ∣ a

local instance isSpecialSquarefreeKernelDecidable (p : ℕ) :
    DecidablePred (IsSpecialSquarefreeKernel p) := Classical.decPred _

/-- The finite square-convolution parametrization of locally admissible
integers through `N`.  Both coordinates are bounded by `N`; the last filter
is the actual hyperbolic constraint `b²a ≤ N`. -/
noncomputable def specialLocalKernelPairs (p N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun z =>
    IsSpecialSquarefreeKernel p z.1 ∧ z.2 ^ 2 * z.1 ≤ N)

@[simp] theorem mem_specialLocalKernelPairs {p N a b : ℕ} :
    (a, b) ∈ specialLocalKernelPairs p N ↔
      a ∈ Finset.Icc 1 N ∧ b ∈ Finset.Icc 1 N ∧
        IsSpecialSquarefreeKernel p a ∧ b ^ 2 * a ≤ N := by
  classical
  simp [specialLocalKernelPairs, and_assoc]

local instance specialLocallyAdmissibleDecidable (p : ℕ) :
    DecidablePred (SpecialLocallyAdmissible p) := Classical.decPred _

/-- Positive locally admissible integers through `N`. -/
noncomputable def specialLocalValues (p N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (SpecialLocallyAdmissible p)

/-- The image of the square-convolution parametrization. -/
noncomputable def specialLocalKernelValues (p N : ℕ) : Finset ℕ := by
  classical
  exact (specialLocalKernelPairs p N).image fun z => z.2 ^ 2 * z.1

/-- Squarefree kernels through `N` satisfying every local condition.  This
is the `b = 1` slice of `specialLocalKernelPairs`; analytically it is the
half-dimensional sifted set to which the beta sieve is applied. -/
noncomputable def specialSquarefreeKernels (p N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (IsSpecialSquarefreeKernel p)

@[simp] theorem mem_specialSquarefreeKernels {p N a : ℕ} :
    a ∈ specialSquarefreeKernels p N ↔
      a ∈ Finset.Icc 1 N ∧ IsSpecialSquarefreeKernel p a := by
  classical
  simp [specialSquarefreeKernels]

/-- Locally admissible values missed by the principal ring class represented
by `X² + p³Y²`.  Bernays' class-mixing argument proves that this exception
set is negligible compared with the local norm set. -/
noncomputable def specialRingClassExceptions (p N : ℕ) : Finset ℕ :=
  specialLocalValues p N \ specialFormValues p N

@[simp] theorem mem_specialLocalValues {p N n : ℕ} :
    n ∈ specialLocalValues p N ↔
      n ∈ Finset.Icc 1 N ∧ SpecialLocallyAdmissible p n := by
  classical
  simp [specialLocalValues]

/-- The finite local-set cardinality is the ordinary partial sum of its
`0/1` multiplicative indicator. -/
theorem specialLocalValues_card_eq_indicator_partialSum (p N : ℕ) :
    ((specialLocalValues p N).card : ℝ) =
      HalberstamScratch.partialSum (specialLocalIndicator p) N := by
  classical
  simp [specialLocalValues, HalberstamScratch.partialSum,
    specialLocalIndicator]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hadm⟩
    exact ⟨⟨hn1, hnN⟩, ⟨lt_of_lt_of_le Nat.zero_lt_one hn1, hadm⟩⟩
  · rintro ⟨⟨hn1, hnN⟩, _hn0, hadm⟩
    exact ⟨⟨hn1, hnN⟩, hadm⟩

/-- The finite image of positive squarefree kernels and square multipliers is
exactly the complete local norm set. -/
theorem specialLocalKernelValues_eq_specialLocalValues (p N : ℕ) :
    specialLocalKernelValues p N = specialLocalValues p N := by
  classical
  ext n
  constructor
  · intro hn
    rw [specialLocalKernelValues, Finset.mem_image] at hn
    rcases hn with ⟨⟨a, b⟩, hab, rfl⟩
    rw [mem_specialLocalKernelPairs] at hab
    rcases hab.2.2.1 with ⟨hsa, hsupport⟩
    have ha : 0 < a := (Finset.mem_Icc.mp hab.1).1
    have hb : 0 < b := (Finset.mem_Icc.mp hab.2.1).1
    rw [mem_specialLocalValues]
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr ?_, hab.2.2.2⟩, ?_⟩
    · exact (Nat.mul_ne_zero (pow_ne_zero 2 hb.ne') ha.ne')
    exact (specialLocallyAdmissible_sq_mul_squarefree_iff ha hb hsa).mpr
      hsupport
  · intro hn
    rw [mem_specialLocalValues] at hn
    obtain ⟨a, b, ha, hb, hab, hsa, hsupport⟩ :=
      (specialLocallyAdmissible_iff_exists_squarefree_kernel
        (Finset.mem_Icc.mp hn.1).1).mp hn.2
    have hvalue : b ^ 2 * a ≤ N := by
      rw [hab]
      exact (Finset.mem_Icc.mp hn.1).2
    have haN : a ≤ N := by
      calc
        a ≤ b ^ 2 * a := by
          exact Nat.le_mul_of_pos_left a (pow_pos hb 2)
        _ ≤ N := hvalue
    have hbN : b ≤ N := by
      calc
        b ≤ b * b := Nat.le_mul_of_pos_right b hb
        _ = b ^ 2 := by ring
        _ ≤ b ^ 2 * a := Nat.le_mul_of_pos_right (b ^ 2) ha
        _ ≤ N := hvalue
    rw [specialLocalKernelValues, Finset.mem_image]
    refine ⟨(a, b), ?_, hab⟩
    rw [mem_specialLocalKernelPairs]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, haN⟩,
      Finset.mem_Icc.mpr ⟨hb, hbN⟩, ⟨hsa, hsupport⟩, hvalue⟩

/-- The square-convolution parametrization has no collisions. -/
theorem specialLocalKernelMap_injOn (p N : ℕ) :
    Set.InjOn (fun z : ℕ × ℕ => z.2 ^ 2 * z.1)
      (specialLocalKernelPairs p N : Set (ℕ × ℕ)) := by
  intro z hz w hw heq
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  change (a, b) ∈ specialLocalKernelPairs p N at hz
  change (c, d) ∈ specialLocalKernelPairs p N at hw
  rw [mem_specialLocalKernelPairs] at hz hw
  obtain ⟨hac, hbd⟩ := sq_mul_squarefree_unique
    (Finset.mem_Icc.mp hz.1).1 (Finset.mem_Icc.mp hz.2.1).1
    (Finset.mem_Icc.mp hw.1).1 (Finset.mem_Icc.mp hw.2.1).1
    hz.2.2.1.1 hw.2.2.1.1 heq
  simp [hac, hbd]

/-- Exact finite square-convolution formula for the local count. -/
theorem specialLocalValues_card_eq_specialLocalKernelPairs_card (p N : ℕ) :
    (specialLocalValues p N).card = (specialLocalKernelPairs p N).card := by
  rw [← specialLocalKernelValues_eq_specialLocalValues]
  exact Finset.card_image_iff.mpr (specialLocalKernelMap_injOn p N)

/-- The squarefree-kernel slice injects into the complete local norm set.
Consequently the local lower bound needs only a lower-bound sieve for
squarefree integers supported on the allowed primes; the square multiplier
convolution can only increase the count. -/
theorem specialSquarefreeKernels_subset_specialLocalValues (p N : ℕ) :
    specialSquarefreeKernels p N ⊆ specialLocalValues p N := by
  classical
  intro a ha
  rw [mem_specialSquarefreeKernels] at ha
  rw [mem_specialLocalValues]
  refine ⟨ha.1, ?_⟩
  rcases ha.2 with ⟨hsa, hsupport⟩
  have ha0 : 0 < a := (Finset.mem_Icc.mp ha.1).1
  simpa using
    (specialLocallyAdmissible_sq_mul_squarefree_iff
      (p := p) (b := 1) ha0 (by decide) hsa).mpr hsupport

theorem specialSquarefreeKernels_card_le_specialLocalValues_card (p N : ℕ) :
    (specialSquarefreeKernels p N).card ≤ (specialLocalValues p N).card :=
  Finset.card_le_card (specialSquarefreeKernels_subset_specialLocalValues p N)

/-- Every represented value satisfies every inert-prime parity condition. -/
theorem specialFormValues_subset_specialLocalValues (p N : ℕ) :
    specialFormValues p N ⊆ specialLocalValues p N := by
  classical
  intro n hn
  rw [mem_specialFormValues] at hn
  rcases hn with ⟨hnIcc, u, _hu, v, _hv, huv⟩
  rw [mem_specialLocalValues]
  refine ⟨hnIcc, ?_⟩
  intro l hl hobs
  have haniso : FormAnisotropicAt (p ^ 3) l :=
    formAnisotropicAt_of_not_isSquare_neg hl hobs
  rw [huv]
  exact even_padicValNat_of_specialForm hl haniso
    (huv ▸ lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1)

/-- Exact decomposition of the local norm set into values of the principal
form and the values missed by that ring class. -/
theorem specialRingClassExceptions_card_add_specialFormCount
    (p N : ℕ) :
    (specialRingClassExceptions p N).card + specialFormCount p N =
      (specialLocalValues p N).card := by
  classical
  exact Finset.card_sdiff_add_card_eq_card
    (specialFormValues_subset_specialLocalValues p N)

/-- Simultaneous even-valuation conditions at a finite collection of local
obstruction primes. -/
def ParityAdmissible (L : Finset ℕ) (n : ℕ) : Prop :=
  ∀ l ∈ L, Even (padicValNat l n)

local instance parityAdmissibleDecidable (L : Finset ℕ) :
    DecidablePred (ParityAdmissible L) := Classical.decPred _

/-- The number of positive integers at most `N` satisfying all parity
conditions in `L`. -/
noncomputable def parityAdmissibleCount (L : Finset ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (ParityAdmissible L)).card

theorem parityAdmissible_mul_iff_of_coprime
    {L : Finset ℕ} (hLprime : ∀ l ∈ L, l.Prime)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : m.Coprime n) :
    ParityAdmissible L (m * n) ↔
      ParityAdmissible L m ∧ ParityAdmissible L n := by
  constructor
  · intro hmn
    constructor
    · intro l hlL
      have hl := hLprime l hlL
      let _ : Fact l.Prime := ⟨hl⟩
      have heven := hmn l hlL
      rw [padicValNat.mul hm hn] at heven
      by_cases hln : l ∣ n
      · have hlm : ¬l ∣ m := by
          intro hlm
          exact hl.ne_one (Nat.eq_one_of_dvd_coprimes hcop hlm hln)
        rw [padicValNat.eq_zero_of_not_dvd hlm]
        exact Even.zero
      · rw [padicValNat.eq_zero_of_not_dvd hln, add_zero] at heven
        exact heven
    · intro l hlL
      have hl := hLprime l hlL
      let _ : Fact l.Prime := ⟨hl⟩
      have heven := hmn l hlL
      rw [padicValNat.mul hm hn] at heven
      by_cases hlm : l ∣ m
      · have hln : ¬l ∣ n := by
          intro hln
          exact hl.ne_one (Nat.eq_one_of_dvd_coprimes hcop hlm hln)
        rw [padicValNat.eq_zero_of_not_dvd hln]
        exact Even.zero
      · rw [padicValNat.eq_zero_of_not_dvd hlm, zero_add] at heven
        exact heven
  · rintro ⟨hmEven, hnEven⟩ l hlL
    have hl := hLprime l hlL
    let _ : Fact l.Prime := ⟨hl⟩
    rw [padicValNat.mul hm hn]
    exact (hmEven l hlL).add (hnEven l hlL)

/-- Zero-one multiplicative weight of the finite parity sieve. -/
noncomputable def parityWeight (L : Finset ℕ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else if ParityAdmissible L n then 1 else 0

@[simp] theorem parityWeight_zero (L : Finset ℕ) : parityWeight L 0 = 0 := by
  simp [parityWeight]

theorem parityWeight_one (L : Finset ℕ) : parityWeight L 1 = 1 := by
  simp [parityWeight, ParityAdmissible]

theorem parityWeight_nonneg (L : Finset ℕ) (n : ℕ) :
    0 ≤ parityWeight L n := by
  simp only [parityWeight]
  split_ifs <;> norm_num

theorem parityWeight_le_one (L : Finset ℕ) (n : ℕ) :
    parityWeight L n ≤ 1 := by
  simp only [parityWeight]
  split_ifs <;> norm_num

theorem parityWeight_mul_of_coprime
    {L : Finset ℕ} (hLprime : ∀ l ∈ L, l.Prime)
    {m n : ℕ} (hcop : m.Coprime n) :
    parityWeight L (m * n) = parityWeight L m * parityWeight L n := by
  by_cases hm : m = 0
  · subst m
    simp [parityWeight]
  by_cases hn : n = 0
  · subst n
    simp [parityWeight]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [parityWeight, parityWeight, parityWeight, if_neg hm, if_neg hn,
    if_neg hmn]
  have hiff := parityAdmissible_mul_iff_of_coprime hLprime hm hn hcop
  by_cases hmm : ParityAdmissible L m <;>
    by_cases hnn : ParityAdmissible L n <;> simp [hmm, hnn, hiff]

theorem parityWeight_prime_pow_le_one (L : Finset ℕ) {p j : ℕ}
    (_hp : p.Prime) :
    parityWeight L (p ^ (j + 1)) ≤ (1 : ℝ) * 1 ^ j := by
  simpa using parityWeight_le_one L (p ^ (j + 1))

/-- Halberstam--Richert reduces the finite parity count to its Euler
product. -/
theorem parityWeight_mean_le_euler
    (L : Finset ℕ) (hLprime : ∀ l ∈ L, l.Prime)
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, parityWeight L n) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, parityWeight L (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  exact HalberstamComplete448.halberstam_richert_explicit
    (parityWeight L) (parityWeight_zero L) (parityWeight_one L)
    (fun {_ _} hcop ↦ parityWeight_mul_of_coprime hLprime hcop)
    (parityWeight_nonneg L) 1 1 (by norm_num) (by norm_num) (by norm_num)
    (fun p hp j ↦ parityWeight_prime_pow_le_one L hp) N hN

theorem parityWeight_sum_eq_count (L : Finset ℕ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, parityWeight L n) =
      (parityAdmissibleCount L N : ℝ) := by
  classical
  rw [parityAdmissibleCount, Finset.cast_card, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  by_cases hadm : ParityAdmissible L n <;>
    simp [parityWeight, hn0, hadm]

theorem parityAdmissible_prime_pow_iff
    {L : Finset ℕ} (hLprime : ∀ l ∈ L, l.Prime)
    {p j : ℕ} (hp : p.Prime) :
    ParityAdmissible L (p ^ j) ↔ p ∉ L ∨ Even j := by
  constructor
  · intro hadm
    by_cases hpL : p ∈ L
    · right
      let _ : Fact p.Prime := ⟨hp⟩
      simpa using hadm p hpL
    · exact Or.inl hpL
  · intro h l hlL
    have hl := hLprime l hlL
    let _ : Fact l.Prime := ⟨hl⟩
    rcases h with hpL | hj
    · have hlp : l ≠ p := by
        intro hlpeq
        subst l
        exact hpL hlL
      have hnDiv : ¬ l ∣ p ^ j := by
        intro hdiv
        have hlDivP : l ∣ p := hl.dvd_of_dvd_pow hdiv
        exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp hlDivP)
      rw [padicValNat.eq_zero_of_not_dvd hnDiv]
      exact Even.zero
    · by_cases hlp : l = p
      · subst l
        simpa using hj
      · have hnDiv : ¬ l ∣ p ^ j := by
          intro hdiv
          have hlDivP : l ∣ p := hl.dvd_of_dvd_pow hdiv
          exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp hlDivP)
        rw [padicValNat.eq_zero_of_not_dvd hnDiv]
        exact Even.zero

theorem parityWeight_prime_pow
    {L : Finset ℕ} (hLprime : ∀ l ∈ L, l.Prime)
    (p j : ℕ) (hp : p.Prime) :
    parityWeight L (p ^ j) =
      if p ∈ L then (if Even j then 1 else 0) else 1 := by
  rw [parityWeight, if_neg (pow_ne_zero _ hp.ne_zero)]
  by_cases hpL : p ∈ L <;> by_cases hj : Even j <;>
    simp [hpL, hj, parityAdmissible_prime_pow_iff hLprime hp]

/-- Even natural numbers, parametrized by their halves. -/
def evenNatEquiv1081 : ℕ ≃ {n : ℕ // Even n} where
  toFun k := ⟨2 * k, ⟨k, by omega⟩⟩
  invFun n := n.1 / 2
  left_inv k := by simp
  right_inv n := by
    apply Subtype.ext
    rcases n.2 with ⟨k, hk⟩
    dsimp
    omega

theorem tsum_even_geometric1081 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℕ, if Even j then r ^ j else 0) = (1 - r ^ 2)⁻¹ := by
  calc
    (∑' j : ℕ, if Even j then r ^ j else 0) =
        ∑' j : {n : ℕ // Even n}, r ^ (j : ℕ) := by
          symm
          calc
            (∑' j : {n : ℕ // Even n}, r ^ (j : ℕ)) =
                ∑' j : ℕ, ({n : ℕ | Even n} : Set ℕ).indicator
                  (fun n ↦ r ^ n) j :=
              tsum_subtype ({n : ℕ | Even n} : Set ℕ) (fun n ↦ r ^ n)
            _ = ∑' j : ℕ, if Even j then r ^ j else 0 := by
              apply tsum_congr
              intro j
              by_cases hj : Even j <;> simp [Set.indicator, hj]
    _ = ∑' k : ℕ, r ^ ((evenNatEquiv1081 k : {n : ℕ // Even n}) : ℕ) := by
      exact (evenNatEquiv1081.tsum_eq
        (fun j : {n : ℕ // Even n} ↦ r ^ (j : ℕ))).symm
    _ = ∑' k : ℕ, (r ^ 2) ^ k := by
      congr 1
      funext k
      dsimp [evenNatEquiv1081]
      rw [← pow_mul]
    _ = (1 - r ^ 2)⁻¹ :=
      tsum_geometric_of_lt_one (sq_nonneg r) (by nlinarith)

/-- Exact Euler factor of the complete local-norm indicator.  At an
obstruction prime only even valuations occur, whereas every valuation is
allowed at every other prime. -/
theorem specialLocalIndicator_eulerFactor
    {p l : ℕ} (hl : l.Prime) :
    (∑' j : ℕ,
        specialLocalIndicator p (l ^ j) / ((l ^ j : ℕ) : ℝ)) =
      if IsQuadraticObstruction (p ^ 3) l then
        (1 - ((l : ℝ)⁻¹) ^ 2)⁻¹
      else (1 - (l : ℝ)⁻¹)⁻¹ := by
  let r : ℝ := (l : ℝ)⁻¹
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity : (0 : ℝ) < l)).2 hlR
  by_cases hobs : IsQuadraticObstruction (p ^ 3) l
  · rw [if_pos hobs]
    calc
      (∑' j : ℕ,
          specialLocalIndicator p (l ^ j) / ((l ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, if Even j then r ^ j else 0 := by
            apply tsum_congr
            intro j
            rw [specialLocalIndicator_prime_pow hl]
            by_cases hj : Even j
            · have hjodd : ¬ Odd j := Nat.not_odd_iff_even.mpr hj
              simp [hobs, hj, hjodd, r, div_eq_mul_inv, inv_pow]
            · have hjodd : Odd j := Nat.not_even_iff_odd.mp hj
              simp [hobs, hj, hjodd]
      _ = (1 - r ^ 2)⁻¹ := tsum_even_geometric1081 hr0 hr1
      _ = (1 - ((l : ℝ)⁻¹) ^ 2)⁻¹ := by rfl
  · rw [if_neg hobs]
    calc
      (∑' j : ℕ,
          specialLocalIndicator p (l ^ j) / ((l ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, r ^ j := by
            apply tsum_congr
            intro j
            rw [specialLocalIndicator_prime_pow hl]
            simp [hobs, r, div_eq_mul_inv, inv_pow]
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
      _ = (1 - (l : ℝ)⁻¹)⁻¹ := by rfl

/-! ### A finite Euler-product lower-bound mechanism

The following finite identities implement the probabilistic truncation step in
the elementary local-norm lower bound.  A subset `S` of allowed primes has
weight `1 / ∏ q ∈ S, q`; Markov's inequality for its logarithmic size shows
that products at most `N` retain a fixed fraction of the complete finite Euler
product whenever the first logarithmic moment is small enough. -/

def subsetReciprocalWeight (S : Finset ℕ) : ℝ :=
  ∏ q ∈ S, (q : ℝ)⁻¹

def subsetLogSize (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, Real.log q

def squarefreeEulerMass (P : Finset ℕ) : ℝ :=
  ∏ q ∈ P, (1 + (q : ℝ)⁻¹)

def primeLogReciprocalMass (P : Finset ℕ) : ℝ :=
  ∑ q ∈ P, Real.log q * (q : ℝ)⁻¹

theorem sum_powerset_subsetReciprocalWeight (P : Finset ℕ) :
    (∑ S ∈ P.powerset, subsetReciprocalWeight S) =
      squarefreeEulerMass P := by
  rw [squarefreeEulerMass, Finset.prod_one_add]
  rfl

theorem powerset_weighted_log_le
    (P : Finset ℕ) (hP : ∀ q ∈ P, 1 ≤ q) :
    (∑ S ∈ P.powerset,
        subsetReciprocalWeight S * subsetLogSize S) ≤
      squarefreeEulerMass P * primeLogReciprocalMass P := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [subsetReciprocalWeight, subsetLogSize,
      squarefreeEulerMass, primeLogReciprocalMass]
  | @insert a P ha ih =>
      have ha1 : (1 : ℕ) ≤ a := hP a (Finset.mem_insert_self _ _)
      have haR : (0 : ℝ) ≤ (a : ℝ)⁻¹ := by positivity
      have hlog : 0 ≤ Real.log (a : ℝ) :=
        Real.log_nonneg (by exact_mod_cast ha1)
      have ih' := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
      rw [Finset.sum_powerset_insert ha]
      have hselected :
          (∑ S ∈ P.powerset,
              subsetReciprocalWeight (insert a S) *
                subsetLogSize (insert a S)) =
            (a : ℝ)⁻¹ *
                (∑ S ∈ P.powerset,
                  subsetReciprocalWeight S * subsetLogSize S) +
              (Real.log (a : ℝ) * (a : ℝ)⁻¹) *
                squarefreeEulerMass P := by
        calc
          (∑ S ∈ P.powerset,
              subsetReciprocalWeight (insert a S) *
                subsetLogSize (insert a S)) =
              ∑ S ∈ P.powerset,
                ((a : ℝ)⁻¹ * subsetReciprocalWeight S) *
                  (Real.log (a : ℝ) + subsetLogSize S) := by
            apply Finset.sum_congr rfl
            intro S hS
            have haS : a ∉ S :=
              Finset.notMem_of_mem_powerset_of_notMem hS ha
            unfold subsetReciprocalWeight subsetLogSize
            rw [Finset.prod_insert haS, Finset.sum_insert haS]
          _ = (a : ℝ)⁻¹ *
                (∑ S ∈ P.powerset,
                  subsetReciprocalWeight S * subsetLogSize S) +
              (Real.log (a : ℝ) * (a : ℝ)⁻¹) *
                squarefreeEulerMass P := by
            rw [← sum_powerset_subsetReciprocalWeight]
            calc
              (∑ S ∈ P.powerset,
                  ((a : ℝ)⁻¹ * subsetReciprocalWeight S) *
                    (Real.log (a : ℝ) + subsetLogSize S)) =
                  (∑ S ∈ P.powerset,
                    ((a : ℝ)⁻¹ * Real.log (a : ℝ)) *
                      subsetReciprocalWeight S) +
                    ∑ S ∈ P.powerset,
                      (a : ℝ)⁻¹ *
                        (subsetReciprocalWeight S * subsetLogSize S) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro S hS
                ring
              _ = _ := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
                ring
      rw [hselected]
      simp only [squarefreeEulerMass, primeLogReciprocalMass,
        Finset.prod_insert ha, Finset.sum_insert ha]
      let Z : ℝ := ∏ q ∈ P, (1 + (q : ℝ)⁻¹)
      let L : ℝ := ∑ q ∈ P, Real.log q * (q : ℝ)⁻¹
      change
        (∑ S ∈ P.powerset,
              subsetReciprocalWeight S * subsetLogSize S) +
            ((a : ℝ)⁻¹ *
                (∑ S ∈ P.powerset,
                  subsetReciprocalWeight S * subsetLogSize S) +
              (Real.log (a : ℝ) * (a : ℝ)⁻¹) * Z) ≤
          ((1 + (a : ℝ)⁻¹) * Z) *
            (Real.log (a : ℝ) * (a : ℝ)⁻¹ + L)
      have ihZL :
          (∑ S ∈ P.powerset,
              subsetReciprocalWeight S * subsetLogSize S) ≤ Z * L := by
        simpa [Z, L, squarefreeEulerMass, primeLogReciprocalMass] using ih'
      have hZ : 0 ≤ Z := by
        dsimp [Z]
        positivity
      have hL : 0 ≤ L := by
        dsimp [L]
        apply Finset.sum_nonneg
        intro q hq
        apply mul_nonneg
        · exact Real.log_nonneg (by
            exact_mod_cast hP q (Finset.mem_insert_of_mem hq))
        · positivity
      calc
        (∑ S ∈ P.powerset,
              subsetReciprocalWeight S * subsetLogSize S) +
            ((a : ℝ)⁻¹ *
                (∑ S ∈ P.powerset,
                  subsetReciprocalWeight S * subsetLogSize S) +
              (Real.log (a : ℝ) * (a : ℝ)⁻¹) * Z) =
            (1 + (a : ℝ)⁻¹) *
                (∑ S ∈ P.powerset,
                  subsetReciprocalWeight S * subsetLogSize S) +
              (Real.log (a : ℝ) * (a : ℝ)⁻¹) * Z := by
          ring
        _ ≤ (1 + (a : ℝ)⁻¹) * (Z * L) +
              (Real.log (a : ℝ) * (a : ℝ)⁻¹) * Z := by
          gcongr
        _ ≤ ((1 + (a : ℝ)⁻¹) * Z) *
              (Real.log (a : ℝ) * (a : ℝ)⁻¹ + L) := by
          nlinarith [mul_nonneg
            (mul_nonneg hlog haR) (mul_nonneg haR hZ)]

def boundedSubsetEulerMass (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ S ∈ P.powerset.filter (fun S => ∏ q ∈ S, q ≤ N),
    subsetReciprocalWeight S

theorem subsetLogSize_eq_log_prod
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) :
    subsetLogSize S =
      Real.log (((∏ q ∈ S, q : ℕ) : ℕ) : ℝ) := by
  unfold subsetLogSize
  rw [Nat.cast_prod, Real.log_prod]
  intro q hq
  exact_mod_cast (hS q hq).ne_zero

theorem subsetReciprocalWeight_eq_inv_prod (S : Finset ℕ) :
    subsetReciprocalWeight S =
      ((((∏ q ∈ S, q : ℕ) : ℕ) : ℝ))⁻¹ := by
  unfold subsetReciprocalWeight
  rw [Nat.cast_prod, Finset.prod_inv_distrib]

theorem boundedSubsetEulerMass_lower_of_log_moment
    (P : Finset ℕ) (N : ℕ) (c : ℝ)
    (hP : ∀ q ∈ P, q.Prime) (hN : 2 ≤ N)
    (_hc0 : 0 ≤ c) (_hc1 : c < 1)
    (hmass : primeLogReciprocalMass P ≤ c * Real.log (N : ℝ)) :
    (1 - c) * squarefreeEulerMass P ≤ boundedSubsetEulerMass P N := by
  classical
  let good : Finset (Finset ℕ) :=
    P.powerset.filter (fun S => ∏ q ∈ S, q ≤ N)
  let bad : Finset (Finset ℕ) :=
    P.powerset.filter (fun S => ¬ ∏ q ∈ S, q ≤ N)
  let G : ℝ := ∑ S ∈ good, subsetReciprocalWeight S
  let B : ℝ := ∑ S ∈ bad, subsetReciprocalWeight S
  let Z : ℝ := squarefreeEulerMass P
  let M : ℝ := ∑ S ∈ P.powerset,
    subsetReciprocalWeight S * subsetLogSize S
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hweight (S : Finset ℕ) : 0 ≤ subsetReciprocalWeight S := by
    unfold subsetReciprocalWeight
    positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z, squarefreeEulerMass]
    positivity
  have hM : M ≤ Z * primeLogReciprocalMass P := by
    dsimp [M, Z]
    exact powerset_weighted_log_le P
      (fun q hq => (hP q hq).one_le)
  have hbadPoint : ∀ S ∈ bad,
      Real.log (N : ℝ) * subsetReciprocalWeight S ≤
        subsetReciprocalWeight S * subsetLogSize S := by
    intro S hSbad
    have hSpow : S ∈ P.powerset :=
      (Finset.mem_filter.mp hSbad).1
    have hSsub : S ⊆ P := Finset.mem_powerset.mp hSpow
    have hprod : N < ∏ q ∈ S, q := by
      have := (Finset.mem_filter.mp hSbad).2
      omega
    have hlogle : Real.log (N : ℝ) ≤ subsetLogSize S := by
      rw [subsetLogSize_eq_log_prod
        (fun q hq => hP q (hSsub hq))]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hprod.le)
    calc
      Real.log (N : ℝ) * subsetReciprocalWeight S ≤
          subsetLogSize S * subsetReciprocalWeight S :=
        mul_le_mul_of_nonneg_right hlogle (hweight S)
      _ = subsetReciprocalWeight S * subsetLogSize S := by ring
  have hlogB : Real.log (N : ℝ) * B ≤ M := by
    calc
      Real.log (N : ℝ) * B =
          ∑ S ∈ bad,
            Real.log (N : ℝ) * subsetReciprocalWeight S := by
        dsimp [B]
        rw [Finset.mul_sum]
      _ ≤ ∑ S ∈ bad,
          subsetReciprocalWeight S * subsetLogSize S :=
        Finset.sum_le_sum hbadPoint
      _ ≤ M := by
        dsimp [M, bad]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro S hS _
          exact mul_nonneg (hweight S) (by
            unfold subsetLogSize
            apply Finset.sum_nonneg
            intro q hq
            exact Real.log_nonneg (by exact_mod_cast
              (hP q (Finset.mem_powerset.mp hS hq)).one_le))
  have hB : B ≤ c * Z := by
    have hMupper : M ≤ Z * (c * Real.log (N : ℝ)) :=
      hM.trans (mul_le_mul_of_nonneg_left hmass hZ)
    have hmul : Real.log (N : ℝ) * B ≤
        Real.log (N : ℝ) * (c * Z) := by
      calc
        Real.log (N : ℝ) * B ≤ M := hlogB
        _ ≤ Z * (c * Real.log (N : ℝ)) := hMupper
        _ = Real.log (N : ℝ) * (c * Z) := by ring
    nlinarith
  have hsplit : G + B = Z := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := P.powerset) (p := fun S => ∏ q ∈ S, q ≤ N)
      (f := subsetReciprocalWeight)
    dsimp [G, B, good, bad, Z]
    exact h.trans (sum_powerset_subsetReciprocalWeight P)
  change (1 - c) * Z ≤ G
  linarith

/-- The finite set of non-obstruction primes through `Q`. -/
noncomputable def specialAllowedPrimesFinite (p Q : ℕ) : Finset ℕ := by
  classical
  exact (Q + 1).primesBelow.filter
    (fun l => ¬ IsQuadraticObstruction (p ^ 3) l)

@[simp] theorem mem_specialAllowedPrimesFinite {p Q l : ℕ} :
    l ∈ specialAllowedPrimesFinite p Q ↔
      l.Prime ∧ l ≤ Q ∧ ¬ IsQuadraticObstruction (p ^ 3) l := by
  classical
  rw [specialAllowedPrimesFinite, Finset.mem_filter,
    Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hlQ, hl⟩, hallowed⟩
    exact ⟨hl, Nat.lt_succ_iff.mp (by simpa using hlQ), hallowed⟩
  · rintro ⟨hl, hlQ, hallowed⟩
    exact ⟨⟨by simpa using Nat.lt_succ_iff.mpr hlQ, hl⟩, hallowed⟩

/-- Products distinguish subsets of a finite set of primes. -/
theorem prod_injOn_prime_subsets1081 {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) {S | S ⊆ P} := by
  intro A hA B hB hprod
  change (∏ p ∈ A, p) = (∏ p ∈ B, p) at hprod
  ext p
  constructor
  · intro hpA
    have pp := hprime p (hA hpA)
    have hpdvd : p ∣ ∏ q ∈ B, q := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (fun q => q) hpA
    obtain ⟨q, hqB, hpq⟩ :=
      (Prime.dvd_finsetProd_iff pp.prime (fun q : ℕ => q)).mp hpdvd
    have pq : q.Prime := hprime q (hB hqB)
    have : p = q := (Nat.prime_dvd_prime_iff_eq pp pq).mp hpq
    simpa [this] using hqB
  · intro hpB
    have pp := hprime p (hB hpB)
    have hpdvd : p ∣ ∏ q ∈ A, q := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem (fun q => q) hpB
    obtain ⟨q, hqA, hpq⟩ :=
      (Prime.dvd_finsetProd_iff pp.prime (fun q : ℕ => q)).mp hpdvd
    have pq : q.Prime := hprime q (hA hqA)
    have : p = q := (Nat.prime_dvd_prime_iff_eq pp pq).mp hpq
    simpa [this] using hqA

/-- A squarefree product of allowed primes satisfies every local parity
condition. -/
theorem specialLocallyAdmissible_prod_allowed
    {p Q : ℕ} {S : Finset ℕ}
    (hS : S ⊆ specialAllowedPrimesFinite p Q) :
    SpecialLocallyAdmissible p (∏ q ∈ S, q) := by
  intro l hl hobs
  have hnDiv : ¬ l ∣ ∏ q ∈ S, q := by
    intro hdiv
    obtain ⟨q, hqS, hlq⟩ :=
      (Prime.dvd_finsetProd_iff hl.prime (fun q : ℕ => q)).mp hdiv
    have hqData := mem_specialAllowedPrimesFinite.mp (hS hqS)
    have hlqeq : l = q :=
      (Nat.prime_dvd_prime_iff_eq hl hqData.1).mp hlq
    subst q
    exact hqData.2.2 hobs
  rw [padicValNat.eq_zero_of_not_dvd hnDiv]
  exact Even.zero

/-- The retained subset Euler mass injects into the reciprocal-weighted
partial sum of the complete local indicator. -/
theorem boundedSubsetEulerMass_le_localReciprocal
    (p Q N : ℕ) :
    boundedSubsetEulerMass (specialAllowedPrimesFinite p Q) N ≤
      HalberstamScratch.reciprocalPartialSum
        (specialLocalIndicator p) N := by
  classical
  let P := specialAllowedPrimesFinite p Q
  let good : Finset (Finset ℕ) :=
    P.powerset.filter (fun S => ∏ q ∈ S, q ≤ N)
  let prodMap : Finset ℕ → ℕ := fun S => ∏ q ∈ S, q
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact (mem_specialAllowedPrimesFinite.mp hq).1
  have hgoodSub : ∀ S ∈ good, S ⊆ P := by
    intro S hS
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hinj : Set.InjOn prodMap good := by
    intro A hA B hB
    exact prod_injOn_prime_subsets1081 hprime (hgoodSub A hA)
      (hgoodSub B hB)
  have himageSub : good.image prodMap ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨S, hSgood, rfl⟩ := Finset.mem_image.mp hn
    have hpos : 0 < prodMap S := by
      dsimp [prodMap]
      exact Finset.prod_pos fun q hq =>
        (hprime q (hgoodSub S hSgood hq)).pos
    exact Finset.mem_Icc.mpr
      ⟨hpos, (Finset.mem_filter.mp hSgood).2⟩
  have hindicator : ∀ n ∈ good.image prodMap,
      specialLocalIndicator p n / (n : ℝ) = (n : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨S, hSgood, rfl⟩ := Finset.mem_image.mp hn
    have hpos : 0 < prodMap S := by
      dsimp [prodMap]
      exact Finset.prod_pos fun q hq =>
        (hprime q (hgoodSub S hSgood hq)).pos
    have hadm : SpecialLocallyAdmissible p (prodMap S) :=
      specialLocallyAdmissible_prod_allowed (hgoodSub S hSgood)
    rw [specialLocalIndicator]
    simp [hpos, hadm, div_eq_mul_inv]
  calc
    boundedSubsetEulerMass (specialAllowedPrimesFinite p Q) N =
        ∑ S ∈ good, ((prodMap S : ℕ) : ℝ)⁻¹ := by
      dsimp [good, P, prodMap, boundedSubsetEulerMass]
      apply Finset.sum_congr rfl
      intro S hS
      exact subsetReciprocalWeight_eq_inv_prod S
    _ = ∑ n ∈ good.image prodMap, (n : ℝ)⁻¹ := by
      rw [Finset.sum_image hinj]
    _ = ∑ n ∈ good.image prodMap,
        specialLocalIndicator p n / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hindicator n hn).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        specialLocalIndicator p n / (n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himageSub
      intro n hnIcc hnImage
      exact div_nonneg (specialLocalIndicator_nonneg p n) (by positivity)
    _ = HalberstamScratch.reciprocalPartialSum
        (specialLocalIndicator p) N := rfl

/-- The first logarithmic moment of the allowed primes is bounded by the
corresponding unrestricted prime Mertens sum. -/
theorem primeLogReciprocalMass_allowed_le (p Q : ℕ) :
    primeLogReciprocalMass (specialAllowedPrimesFinite p Q) ≤
      BoundedGaps.Maynard.primeLogHarmonicSum Q := by
  classical
  have hsubset : specialAllowedPrimesFinite p Q ⊆ Nat.primesLE Q := by
    intro q hq
    have h := mem_specialAllowedPrimesFinite.mp hq
    exact Nat.mem_primesLE.mpr ⟨h.2.1, h.1⟩
  have hsum :
      (∑ q ∈ specialAllowedPrimesFinite p Q,
          Real.log q * (q : ℝ)⁻¹) ≤
        ∑ q ∈ Nat.primesLE Q, Real.log q * (q : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro q hqAll hqAllowed
    have hq : q.Prime := Nat.prime_of_mem_primesLE hqAll
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hq.one_le))
      (by positivity)
  simpa [primeLogReciprocalMass,
    BoundedGaps.Maynard.primeLogHarmonicSum, div_eq_mul_inv] using hsum

/-- With a square-root prime cutoff, the first logarithmic moment consumes
strictly less than the available logarithmic budget. -/
theorem eventually_primeLogReciprocalMass_allowed_sqrt_le
    (p : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      primeLogReciprocalMass
          (specialAllowedPrimesFinite p N.sqrt) ≤
        (3 / 4 : ℝ) * Real.log (N : ℝ) := by
  obtain ⟨C, hC⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hlogTendsto : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hCsmall : ∀ᶠ N : ℕ in atTop,
      C ≤ (1 / 4 : ℝ) * Real.log (N : ℝ) := by
    have h := hlogTendsto.eventually (eventually_ge_atTop (4 * C))
    filter_upwards [h] with N hN
    linarith
  filter_upwards [hCsmall, eventually_ge_atTop 1] with N hCsmallN hN
  have hsqrtPos : 0 < N.sqrt := Nat.sqrt_pos.2 hN
  have hsqrtSq : N.sqrt ^ 2 ≤ N := Nat.sqrt_le' N
  have hlogSqrt : Real.log (N.sqrt : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (N : ℝ) := by
    have hlogPow : Real.log ((N.sqrt : ℝ) ^ 2) ≤
        Real.log (N : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hsqrtSq
    rw [Real.log_pow] at hlogPow
    norm_num at hlogPow ⊢
    nlinarith
  have hMertens := hC N.sqrt
  have hprimeUpper :
      BoundedGaps.Maynard.primeLogHarmonicSum N.sqrt ≤
        Real.log (N.sqrt : ℝ) + C := by
    linarith [le_abs_self
      (BoundedGaps.Maynard.primeLogHarmonicSum N.sqrt -
        Real.log (N.sqrt : ℝ))]
  exact (primeLogReciprocalMass_allowed_le p N.sqrt).trans (by
    linarith)


noncomputable def specialAllowedPrimeLogIndicator (p n : ℕ) : ℝ := by
  classical
  exact if n.Prime ∧ ¬ IsQuadraticObstruction (p ^ 3) n then
    Real.log n else 0

def reciprocalNatWeight1081 (n : ℕ) : ℝ := (n : ℝ)⁻¹

def reciprocalNatDifference1081 (n : ℕ) : ℝ :=
  reciprocalNatWeight1081 n - reciprocalNatWeight1081 (n + 1)

noncomputable def specialAllowedPrimeLogHarmonic (p n : ℕ) : ℝ :=
  ∑ l ∈ specialAllowedPrimesFinite p n, Real.log l / (l : ℝ)

theorem sum_range_specialAllowedPrimeLogIndicator (p n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), specialAllowedPrimeLogIndicator p k) =
      specialAllowedPrimeLog p n := by
  classical
  unfold specialAllowedPrimeLogIndicator specialAllowedPrimeLog
  rw [show (n + 1).primesBelow =
      (Finset.range (n + 1)).filter Nat.Prime by rfl,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : k.Prime <;>
    by_cases hobs : IsQuadraticObstruction (p ^ 3) k <;>
    simp [hp, hobs]

theorem reciprocalNatDifference1081_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ reciprocalNatDifference1081 n := by
  unfold reciprocalNatDifference1081 reciprocalNatWeight1081
  exact sub_nonneg.mpr (inv_anti₀ (by positivity)
    (by exact_mod_cast Nat.le_succ n))

theorem specialAllowedPrimeLogHarmonic_eq_abel
    (p : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    specialAllowedPrimeLogHarmonic p n =
      reciprocalNatWeight1081 n * specialAllowedPrimeLog p n +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalNatDifference1081 k * specialAllowedPrimeLog p k := by
  have hparts := Finset.sum_Ico_by_parts reciprocalNatWeight1081
    (specialAllowedPrimeLogIndicator p)
    (show 2 < n + 1 by omega)
  simp only [smul_eq_mul] at hparts
  have hleft :
      (∑ k ∈ Finset.Ico 2 (n + 1),
          reciprocalNatWeight1081 k * specialAllowedPrimeLogIndicator p k) =
        specialAllowedPrimeLogHarmonic p n := by
    classical
    unfold specialAllowedPrimeLogHarmonic
    calc
      (∑ k ∈ Finset.Ico 2 (n + 1),
          reciprocalNatWeight1081 k * specialAllowedPrimeLogIndicator p k) =
          ∑ k ∈ Finset.Ico 2 (n + 1),
            if k.Prime ∧ ¬ IsQuadraticObstruction (p ^ 3) k then
              Real.log k / (k : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            unfold reciprocalNatWeight1081 specialAllowedPrimeLogIndicator
            by_cases h : k.Prime ∧
                ¬ IsQuadraticObstruction (p ^ 3) k <;>
              simp [h, div_eq_mul_inv, mul_comm]
      _ = ∑ k ∈ (Finset.Ico 2 (n + 1)).filter
            (fun k => k.Prime ∧
              ¬ IsQuadraticObstruction (p ^ 3) k),
            Real.log k / (k : ℝ) := by
          rw [Finset.sum_filter]
      _ = ∑ k ∈ specialAllowedPrimesFinite p n,
            Real.log k / (k : ℝ) := by
          apply Finset.sum_congr
          · ext k
            simp only [Finset.mem_filter, Finset.mem_Ico,
              mem_specialAllowedPrimesFinite]
            constructor
            · rintro ⟨⟨hk2, hkn⟩, hkprime, hkallowed⟩
              exact ⟨hkprime, by omega, hkallowed⟩
            · rintro ⟨hkprime, hkn, hkallowed⟩
              exact ⟨⟨hkprime.two_le, by omega⟩, hkprime, hkallowed⟩
          · intro k hk
            rfl
  rw [hleft] at hparts
  have hsum2 :
      (∑ k ∈ Finset.range 2, specialAllowedPrimeLogIndicator p k) = 0 := by
    classical
    norm_num [Finset.sum_range_succ, specialAllowedPrimeLogIndicator]
  rw [hsum2, mul_zero, sub_zero] at hparts
  simp only [Nat.add_sub_cancel] at hparts
  rw [sum_range_specialAllowedPrimeLogIndicator] at hparts
  rw [hparts]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_range_specialAllowedPrimeLogIndicator]
  simp only [reciprocalNatDifference1081]
  ring

theorem inv_mul_log_sq_le_diff_inv_log1081 (n : ℕ) (hn : 3 ≤ n) :
    1 / ((n : ℝ) * (Real.log n) ^ 2) ≤
      1 / Real.log (n - 1 : ℝ) - 1 / Real.log n := by
  have h_mean_value : ∃ c ∈ Set.Ioo (n - 1 : ℝ) n,
      deriv (fun x => -1 / Real.log x) c =
        ((-1 / Real.log n) - (-1 / Real.log (n - 1))) /
          (n - (n - 1)) := by
    apply_rules [exists_deriv_eq_slope] <;> norm_num
    · exact continuousOn_of_forall_continuousAt fun x hx =>
        ContinuousAt.div continuousAt_const
          (Real.continuousAt_log (by
            linarith [hx.1, show (n : ℝ) ≥ 3 by norm_cast]))
          (ne_of_gt (Real.log_pos (by
            linarith [hx.1, show (n : ℝ) ≥ 3 by norm_cast])))
    · exact DifferentiableOn.div (differentiableOn_const _)
        (DifferentiableOn.log differentiableOn_id fun x hx => by
          linarith [hx.1, show (n : ℝ) ≥ 3 by norm_cast])
        fun x hx => ne_of_gt <| Real.log_pos <| by
          linarith [hx.1, show (n : ℝ) ≥ 3 by norm_cast]
  obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := h_mean_value
  have h_deriv_ge :
      1 / (c * (Real.log c) ^ 2) ≥
        1 / (n * (Real.log n) ^ 2) := by
    gcongr
    · exact mul_pos
        (by linarith [show (n : ℝ) ≥ 3 by norm_cast])
        (sq_pos_of_pos (Real.log_pos (by
          linarith [show (n : ℝ) ≥ 3 by norm_cast])))
    · exact Real.log_nonneg
        (by linarith [show (n : ℝ) ≥ 3 by norm_cast])
    · linarith [show (n : ℝ) ≥ 3 by norm_cast]
  have hc0 : c ≠ 0 := by
    linarith [show (n : ℝ) ≥ 3 by norm_cast]
  have hlogc0 : Real.log c ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by
      linarith [show (n : ℝ) ≥ 3 by norm_cast]))
  norm_num [hc0, hlogc0, div_eq_mul_inv] at *
  ring_nf at *
  linarith

theorem partial_sum_inv_mul_log_sq_le1081 (N : ℕ) :
    ∑ n ∈ Finset.Icc 3 N,
        1 / ((n : ℝ) * (Real.log n) ^ 2) ≤
      1 / Real.log 2 := by
  by_cases hN : 3 ≤ N
  · have hterm :
        (∑ n ∈ Finset.Icc 3 N,
            1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
          ∑ n ∈ Finset.Icc 3 N,
            (1 / Real.log (n - 1 : ℝ) - 1 / Real.log n) := by
      exact Finset.sum_le_sum fun n hn =>
        inv_mul_log_sq_le_diff_inv_log1081 n (Finset.mem_Icc.mp hn).1
    have htel :
        (∑ n ∈ Finset.Icc 3 N,
            (1 / Real.log (n - 1 : ℝ) - 1 / Real.log n)) =
          1 / Real.log 2 - 1 / Real.log N := by
      clear hterm
      induction N, hN using Nat.le_induction with
      | base => norm_num
      | succ N hN ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]
          norm_num
    rw [htel] at hterm
    exact hterm.trans (sub_le_self _
      (one_div_nonneg.mpr (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ N by omega)))))
  · have hempty : Finset.Icc 3 N = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp
    positivity

theorem exists_eventually_specialAllowedPrimeLog_sharp_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ K C : ℝ, ∀ᶠ Q : ℕ in atTop,
      (1 / 2 : ℝ) * (Q : ℝ) -
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        specialAllowedPrimeLog p Q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, htheta⟩ :=
    exists_eventually_squareUnitThetaSum_sharp_lower (p := p) hp2
  let C : ℝ := squareUnitThetaSum p 2
  refine ⟨K, C, ?_⟩
  filter_upwards [htheta, eventually_ge_atTop 2] with Q hthetaQ hQ2
  have htail := squareUnitThetaSum_sub_eq_tail_sum (p := p) hQ2
  calc
    (1 / 2 : ℝ) * (Q : ℝ) -
        K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        squareUnitThetaSum p Q - C := sub_le_sub_right hthetaQ C
    _ = ∑ l ∈ squareUnitPrimeTail p Q, Real.log l := by
      simpa only [C] using htail
    _ ≤ specialAllowedPrimeLog p Q :=
      squareUnitPrimeTail_log_le_specialAllowedPrimeLog hp4

theorem exists_global_specialAllowedPrimeLog_sharp_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ Q : ℕ, 3 ≤ Q →
        (1 / 2 : ℝ) * (Q : ℝ) -
            K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
          specialAllowedPrimeLog p Q := by
  obtain ⟨K₀, C₀, hlarge⟩ :=
    exists_eventually_specialAllowedPrimeLog_sharp_lower hp hp4
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 hlarge
  let K : ℝ := |K₀|
  let deficit (Q : ℕ) : ℝ :=
    (1 / 2 : ℝ) * (Q : ℝ) -
      K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 -
        specialAllowedPrimeLog p Q
  let D : ℝ := ∑ Q ∈ Finset.Ico 3 Q₀, |deficit Q|
  let C : ℝ := |C₀| + D
  refine ⟨K, C, abs_nonneg _, ?_, ?_⟩
  · exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun Q hQ => abs_nonneg _)
  intro Q hQ3
  have hlog : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hratio : 0 ≤ (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by positivity
  by_cases hlate : Q₀ ≤ Q
  · have hbase := hQ₀ Q hlate
    have hK : K₀ ≤ K := le_abs_self K₀
    have hC : C₀ ≤ C := by
      dsimp [C]
      have hD : 0 ≤ D := by
        dsimp [D]
        exact Finset.sum_nonneg fun q hq => abs_nonneg _
      linarith [le_abs_self C₀]
    have hKratio :
        K₀ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 ≤
          K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by
      calc
        K₀ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 =
            K₀ * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) := by ring
        _ ≤ K * ((Q : ℝ) / Real.log (Q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hK hratio
        _ = K * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 := by ring
    dsimp [K]
    calc
      (1 / 2 : ℝ) * (Q : ℝ) -
          |K₀| * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C ≤
        (1 / 2 : ℝ) * (Q : ℝ) -
          K₀ * (Q : ℝ) / Real.log (Q : ℝ) ^ 3 - C₀ := by
            dsimp [K] at hKratio
            linarith
      _ ≤ specialAllowedPrimeLog p Q := hbase
  · have hQmem : Q ∈ Finset.Ico 3 Q₀ :=
      Finset.mem_Ico.mpr ⟨hQ3, by omega⟩
    have hterm : |deficit Q| ≤ D := by
      dsimp [D]
      exact Finset.single_le_sum
        (fun q hq => abs_nonneg (deficit q)) hQmem
    have hdef : deficit Q ≤ C := by
      dsimp [C]
      linarith [le_abs_self (deficit Q), abs_nonneg C₀]
    dsimp [deficit, K] at hdef ⊢
    linarith

theorem one_le_log_nat_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) ≤ Real.log (n : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  calc
    Real.exp 1 ≤ (2.7182818286 : ℝ) := Real.exp_one_lt_d9.le
    _ ≤ (2.9 : ℝ) := by norm_num
    _ ≤ 3 := by norm_num
    _ ≤ (n : ℝ) := by exact_mod_cast hn

theorem reciprocalNatDifference1081_mul_nat {n : ℕ} (hn : 1 ≤ n) :
    reciprocalNatDifference1081 n * (n : ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hs0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold reciprocalNatDifference1081 reciprocalNatWeight1081
  push_cast
  field_simp
  ring

theorem reciprocalNatDifference1081_error_le
    {n : ℕ} (hn : 3 ≤ n) :
    reciprocalNatDifference1081 n *
        ((n : ℝ) / Real.log (n : ℝ) ^ 3) ≤
      1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog1 := one_le_log_nat_of_three_le hn
  have hlog0 : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hden :
      (n : ℝ) * Real.log (n : ℝ) ^ 2 ≤
        ((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 3 := by
    have hsqcube : Real.log (n : ℝ) ^ 2 ≤
        Real.log (n : ℝ) ^ 3 := by
      calc
        Real.log (n : ℝ) ^ 2 =
            Real.log (n : ℝ) ^ 2 * 1 := by ring
        _ ≤ Real.log (n : ℝ) ^ 2 * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog1 (sq_nonneg (Real.log (n : ℝ)))
        _ = Real.log (n : ℝ) ^ 3 := by ring
    calc
      (n : ℝ) * Real.log (n : ℝ) ^ 2 ≤
          ((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n)
          (sq_nonneg (Real.log (n : ℝ)))
      _ ≤ ((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hsqcube (by positivity)
  calc
    reciprocalNatDifference1081 n *
        ((n : ℝ) / Real.log (n : ℝ) ^ 3) =
      (reciprocalNatDifference1081 n * (n : ℝ)) /
        Real.log (n : ℝ) ^ 3 := by ring
    _ = (((n + 1 : ℕ) : ℝ)⁻¹) /
        Real.log (n : ℝ) ^ 3 := by
      rw [reciprocalNatDifference1081_mul_nat (show 1 ≤ n by omega)]
    _ = 1 / (((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 3) := by
        field_simp
    _ ≤ 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by
      exact one_div_le_one_div_of_le
        (mul_pos hn0 (pow_pos hlog0 2)) hden

theorem sum_reciprocalNatDifference1081 {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Finset.Ico m n, reciprocalNatDifference1081 k) =
      reciprocalNatWeight1081 m - reciprocalNatWeight1081 n := by
  calc
    (∑ k ∈ Finset.Ico m n, reciprocalNatDifference1081 k) =
        -(∑ k ∈ Finset.Ico m n,
          (reciprocalNatWeight1081 (k + 1) -
            reciprocalNatWeight1081 k)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [reciprocalNatDifference1081]
      ring
    _ = -(reciprocalNatWeight1081 n - reciprocalNatWeight1081 m) := by
      rw [Erdos469.sum_Ico_succ_sub reciprocalNatWeight1081 hmn]
    _ = reciprocalNatWeight1081 m - reciprocalNatWeight1081 n := by ring

theorem half_log_le_reciprocalNat_abel_main {n : ℕ} (hn : 3 ≤ n) :
    (1 / 2 : ℝ) * Real.log (n : ℝ) -
        (1 / 2 : ℝ) * Real.log 4 ≤
      reciprocalNatWeight1081 n * ((1 / 2 : ℝ) * (n : ℝ)) +
        ∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k * ((1 / 2 : ℝ) * (k : ℝ)) := by
  have hpoint : ∀ k ∈ Finset.Ico 3 n,
      Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) ≤
        reciprocalNatDifference1081 k * (k : ℝ) := by
    intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
    have hlog := Erdos469.log_succ_sub_log_le_inv
      (n := k + 1) (by omega : 2 ≤ k + 1)
    rw [reciprocalNatDifference1081_mul_nat (by omega : 1 ≤ k)]
    simpa [Nat.add_assoc] using hlog
  have hsum :
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log 4 ≤
        ∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k * (k : ℝ) := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log 4 =
          ∑ k ∈ Finset.Ico 3 n,
            (Real.log ((k + 2 : ℕ) : ℝ) -
              Real.log ((k + 1 : ℕ) : ℝ)) := by
        symm
        simpa [Nat.add_assoc] using
          (Erdos469.sum_Ico_succ_sub
            (fun k : ℕ => Real.log ((k + 1 : ℕ) : ℝ)) hn)
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hlogMono : Real.log (n : ℝ) ≤
      Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
  have hendpoint : reciprocalNatWeight1081 n *
      ((1 / 2 : ℝ) * (n : ℝ)) = 1 / 2 := by
    unfold reciprocalNatWeight1081
    field_simp
  rw [hendpoint]
  have hscaled := mul_le_mul_of_nonneg_left
    (hsum.trans' (sub_le_sub_right hlogMono (Real.log 4)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (1 / 2 : ℝ) * Real.log (n : ℝ) -
        (1 / 2 : ℝ) * Real.log 4 ≤
      (1 / 2 : ℝ) + (1 / 2 : ℝ) *
        (∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k * (k : ℝ)) := by
            linarith
    _ = (1 / 2 : ℝ) +
        ∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k * ((1 / 2 : ℝ) * (k : ℝ)) := by
      rw [Finset.mul_sum]
      apply congrArg (fun x : ℝ => (1 / 2 : ℝ) + x)
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem specialAllowedPrimeLog_nonneg (p Q : ℕ) :
    0 ≤ specialAllowedPrimeLog p Q := by
  classical
  unfold specialAllowedPrimeLog
  apply Finset.sum_nonneg
  intro l hl
  split_ifs
  · exact le_rfl
  · exact Real.log_nonneg (by exact_mod_cast
      (Nat.prime_of_mem_primesBelow hl).one_le)

theorem reciprocalNat_abel_error_sum_le
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    {n : ℕ} (hn : 3 ≤ n) :
    reciprocalNatWeight1081 n *
          (K * (n : ℝ) / Real.log (n : ℝ) ^ 3 + C) +
        ∑ k ∈ Finset.Ico 3 n,
          reciprocalNatDifference1081 k *
            (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C) ≤
      2 * K + 2 * C + K / Real.log 2 := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog1 := one_le_log_nat_of_three_le hn
  have hlogpos : 0 < Real.log (n : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog1
  have hlogcube : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  have hendK : reciprocalNatWeight1081 n *
      (K * (n : ℝ) / Real.log (n : ℝ) ^ 3) ≤ K := by
    have heq : reciprocalNatWeight1081 n *
        (K * (n : ℝ) / Real.log (n : ℝ) ^ 3) =
          K / Real.log (n : ℝ) ^ 3 := by
      unfold reciprocalNatWeight1081
      field_simp
    rw [heq]
    exact (div_le_iff₀ (pow_pos hlogpos 3)).2
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlogcube hK)
  have hendC : reciprocalNatWeight1081 n * C ≤ C := by
    unfold reciprocalNatWeight1081
    have hinv : ((n : ℝ)⁻¹) ≤ 1 := by
      exact (inv_le_one₀ hnpos).2 (by exact_mod_cast (show 1 ≤ n by omega))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv hC
  have hsumK :
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          (K * (k : ℝ) / Real.log (k : ℝ) ^ 3)) ≤
        K / Real.log 2 := by
    calc
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          (K * (k : ℝ) / Real.log (k : ℝ) ^ 3)) ≤
          ∑ k ∈ Finset.Ico 3 n,
            K * (1 / ((k : ℝ) * Real.log (k : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
        calc
          reciprocalNatDifference1081 k *
              (K * (k : ℝ) / Real.log (k : ℝ) ^ 3) =
            K * (reciprocalNatDifference1081 k *
              ((k : ℝ) / Real.log (k : ℝ) ^ 3)) := by ring
          _ ≤ K * (1 / ((k : ℝ) * Real.log (k : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (reciprocalNatDifference1081_error_le hk3) hK
      _ ≤ ∑ k ∈ Finset.Icc 3 n,
            K * (1 / ((k : ℝ) * Real.log (k : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1,
            (Finset.mem_Ico.mp hk).2.le⟩
        · intro k hk hkn
          positivity
      _ = K * (∑ k ∈ Finset.Icc 3 n,
            1 / ((k : ℝ) * Real.log (k : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
      _ ≤ K * (1 / Real.log 2) :=
        mul_le_mul_of_nonneg_left (partial_sum_inv_mul_log_sq_le1081 n) hK
      _ = K / Real.log 2 := by ring
  have hsumC :
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k * C) ≤ C := by
    have hsumDiff := sum_reciprocalNatDifference1081 (m := 3) (n := n) hn
    have hweightN : 0 ≤ reciprocalNatWeight1081 n := by
      unfold reciprocalNatWeight1081
      positivity
    have hdiffLe :
        (∑ k ∈ Finset.Ico 3 n, reciprocalNatDifference1081 k) ≤ 1 := by
      calc
        (∑ k ∈ Finset.Ico 3 n, reciprocalNatDifference1081 k) =
            reciprocalNatWeight1081 3 - reciprocalNatWeight1081 n :=
          hsumDiff
        _ ≤ reciprocalNatWeight1081 3 := sub_le_self _ hweightN
        _ ≤ 1 := by norm_num [reciprocalNatWeight1081]
    calc
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k * C) =
          (∑ k ∈ Finset.Ico 3 n,
            reciprocalNatDifference1081 k) * C := by
        rw [Finset.sum_mul]
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hdiffLe hC
      _ = C := one_mul C
  have hend : reciprocalNatWeight1081 n *
      (K * (n : ℝ) / Real.log (n : ℝ) ^ 3 + C) ≤ K + C := by
    rw [mul_add]
    exact add_le_add hendK hendC
  have hsum :
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C)) ≤
        K / Real.log 2 + C := by
    calc
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C)) =
          (∑ k ∈ Finset.Ico 3 n,
            reciprocalNatDifference1081 k *
              (K * (k : ℝ) / Real.log (k : ℝ) ^ 3)) +
          ∑ k ∈ Finset.Ico 3 n,
            reciprocalNatDifference1081 k * C := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ K / Real.log 2 + C := add_le_add hsumK hsumC
  linarith

theorem exists_specialAllowedPrimeLogHarmonic_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 3 ≤ n →
      (1 / 2 : ℝ) * Real.log (n : ℝ) - E ≤
        specialAllowedPrimeLogHarmonic p n := by
  obtain ⟨K, C, hK, hC, htheta⟩ :=
    exists_global_specialAllowedPrimeLog_sharp_lower hp hp4
  let E₀ : ℝ := 2 * K + 2 * C + K / Real.log 2
  let E : ℝ := (1 / 2 : ℝ) * Real.log 4 + E₀
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hE₀ : 0 ≤ E₀ := by
    dsimp [E₀]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨E, hE, ?_⟩
  intro n hn
  let main : ℝ :=
    reciprocalNatWeight1081 n * ((1 / 2 : ℝ) * (n : ℝ)) +
      ∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k * ((1 / 2 : ℝ) * (k : ℝ))
  let err : ℝ :=
    reciprocalNatWeight1081 n *
        (K * (n : ℝ) / Real.log (n : ℝ) ^ 3 + C) +
      ∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C)
  have hmain : (1 / 2 : ℝ) * Real.log (n : ℝ) -
      (1 / 2 : ℝ) * Real.log 4 ≤ main := by
    dsimp [main]
    exact half_log_le_reciprocalNat_abel_main hn
  have herr : err ≤ E₀ := by
    dsimp [err, E₀]
    exact reciprocalNat_abel_error_sum_le hK hC hn
  have hweight : 0 ≤ reciprocalNatWeight1081 n := by
    unfold reciprocalNatWeight1081
    positivity
  have hendpoint :
      reciprocalNatWeight1081 n *
          ((1 / 2 : ℝ) * (n : ℝ) -
            K * (n : ℝ) / Real.log (n : ℝ) ^ 3 - C) ≤
        reciprocalNatWeight1081 n * specialAllowedPrimeLog p n :=
    mul_le_mul_of_nonneg_left (htheta n hn) hweight
  have hsum :
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          ((1 / 2 : ℝ) * (k : ℝ) -
            K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C)) ≤
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalNatDifference1081 k * specialAllowedPrimeLog p k := by
    calc
      (∑ k ∈ Finset.Ico 3 n,
        reciprocalNatDifference1081 k *
          ((1 / 2 : ℝ) * (k : ℝ) -
            K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C)) ≤
          ∑ k ∈ Finset.Ico 3 n,
            reciprocalNatDifference1081 k * specialAllowedPrimeLog p k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
        exact mul_le_mul_of_nonneg_left (htheta k hk3)
          (reciprocalNatDifference1081_nonneg (by omega))
      _ ≤ ∑ k ∈ Finset.Ico 2 n,
            reciprocalNatDifference1081 k * specialAllowedPrimeLog p k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have hkI := Finset.mem_Ico.mp hk
          exact Finset.mem_Ico.mpr
            ⟨(show 2 ≤ 3 by norm_num).trans hkI.1, hkI.2⟩
        · intro k hk hkn
          exact mul_nonneg
            (reciprocalNatDifference1081_nonneg
              ((show 1 ≤ 2 by norm_num).trans (Finset.mem_Ico.mp hk).1))
            (specialAllowedPrimeLog_nonneg p k)
  have haber : main - err ≤ specialAllowedPrimeLogHarmonic p n := by
    rw [specialAllowedPrimeLogHarmonic_eq_abel p
      ((show 2 ≤ 3 by norm_num).trans hn)]
    have hcombined := add_le_add hendpoint hsum
    calc
      main - err =
          reciprocalNatWeight1081 n *
              ((1 / 2 : ℝ) * (n : ℝ) -
                K * (n : ℝ) / Real.log (n : ℝ) ^ 3 - C) +
            ∑ k ∈ Finset.Ico 3 n,
              reciprocalNatDifference1081 k *
                ((1 / 2 : ℝ) * (k : ℝ) -
                  K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C) := by
        have hsumExpand :
            (∑ k ∈ Finset.Ico 3 n,
              reciprocalNatDifference1081 k *
                ((1 / 2 : ℝ) * (k : ℝ) -
                  K * (k : ℝ) / Real.log (k : ℝ) ^ 3 - C)) =
              (∑ k ∈ Finset.Ico 3 n,
                reciprocalNatDifference1081 k *
                  ((1 / 2 : ℝ) * (k : ℝ))) -
              ∑ k ∈ Finset.Ico 3 n,
                reciprocalNatDifference1081 k *
                  (K * (k : ℝ) / Real.log (k : ℝ) ^ 3 + C) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        dsimp [main, err]
        rw [hsumExpand]
        ring
      _ ≤ _ := hcombined
  dsimp [E]
  linarith

noncomputable def specialAllowedPrimeLogHarmonicIndicator
    (p n : ℕ) : ℝ := by
  classical
  exact if n.Prime ∧ ¬ IsQuadraticObstruction (p ^ 3) n then
    Real.log n / (n : ℝ) else 0

noncomputable def specialAllowedPrimeReciprocal (p n : ℕ) : ℝ :=
  ∑ l ∈ specialAllowedPrimesFinite p n, (l : ℝ)⁻¹

theorem sum_range_specialAllowedPrimeLogHarmonicIndicator (p n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        specialAllowedPrimeLogHarmonicIndicator p k) =
      specialAllowedPrimeLogHarmonic p n := by
  classical
  unfold specialAllowedPrimeLogHarmonicIndicator
    specialAllowedPrimeLogHarmonic
  rw [show specialAllowedPrimesFinite p n =
      (Finset.range (n + 1)).filter
        (fun k => k.Prime ∧
          ¬ IsQuadraticObstruction (p ^ 3) k) by
      ext k
      rw [mem_specialAllowedPrimesFinite, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨hkprime, hkn, hkallowed⟩
        exact ⟨Nat.lt_succ_iff.mpr hkn, hkprime, hkallowed⟩
      · rintro ⟨hkn, hkprime, hkallowed⟩
        exact ⟨hkprime, Nat.lt_succ_iff.mp hkn, hkallowed⟩,
    Finset.sum_filter]

theorem specialAllowedPrimeReciprocal_eq_abel
    (p : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    specialAllowedPrimeReciprocal p n =
      Erdos469.reciprocalLogWeight n *
          specialAllowedPrimeLogHarmonic p n +
        ∑ k ∈ Finset.Ico 2 n,
          Erdos469.reciprocalLogDifference k *
            specialAllowedPrimeLogHarmonic p k := by
  have hparts := Finset.sum_Ico_by_parts Erdos469.reciprocalLogWeight
    (specialAllowedPrimeLogHarmonicIndicator p)
    (show 2 < n + 1 by omega)
  simp only [smul_eq_mul] at hparts
  have hleft :
      (∑ k ∈ Finset.Ico 2 (n + 1),
          Erdos469.reciprocalLogWeight k *
            specialAllowedPrimeLogHarmonicIndicator p k) =
        specialAllowedPrimeReciprocal p n := by
    classical
    unfold specialAllowedPrimeReciprocal
    calc
      (∑ k ∈ Finset.Ico 2 (n + 1),
          Erdos469.reciprocalLogWeight k *
            specialAllowedPrimeLogHarmonicIndicator p k) =
          ∑ k ∈ Finset.Ico 2 (n + 1),
            if k.Prime ∧ ¬ IsQuadraticObstruction (p ^ 3) k then
              (k : ℝ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
        have hlog : Real.log (k : ℝ) ≠ 0 :=
          ne_of_gt (Real.log_pos (by exact_mod_cast
            (show 1 < k by omega)))
        unfold Erdos469.reciprocalLogWeight
          specialAllowedPrimeLogHarmonicIndicator
        by_cases h : k.Prime ∧
            ¬ IsQuadraticObstruction (p ^ 3) k
        · simp [h, div_eq_mul_inv, hlog]
        · simp [h]
      _ = ∑ k ∈ (Finset.Ico 2 (n + 1)).filter
            (fun k => k.Prime ∧
              ¬ IsQuadraticObstruction (p ^ 3) k),
            (k : ℝ)⁻¹ := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ specialAllowedPrimesFinite p n, (k : ℝ)⁻¹ := by
        apply Finset.sum_congr
        · ext k
          simp only [Finset.mem_filter, Finset.mem_Ico,
            mem_specialAllowedPrimesFinite]
          constructor
          · rintro ⟨⟨hk2, hkn⟩, hkprime, hkallowed⟩
            exact ⟨hkprime, by omega, hkallowed⟩
          · rintro ⟨hkprime, hkn, hkallowed⟩
            exact ⟨⟨hkprime.two_le, by omega⟩, hkprime, hkallowed⟩
        · intro k hk
          rfl
  rw [hleft] at hparts
  have hsum2 :
      (∑ k ∈ Finset.range 2,
        specialAllowedPrimeLogHarmonicIndicator p k) = 0 := by
    classical
    norm_num [Finset.sum_range_succ,
      specialAllowedPrimeLogHarmonicIndicator]
  rw [hsum2, mul_zero, sub_zero] at hparts
  simp only [Nat.add_sub_cancel] at hparts
  rw [sum_range_specialAllowedPrimeLogHarmonicIndicator] at hparts
  rw [hparts]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_range_specialAllowedPrimeLogHarmonicIndicator]
  simp only [Erdos469.reciprocalLogDifference]
  ring

theorem specialAllowedPrimeLogHarmonic_nonneg (p n : ℕ) :
    0 ≤ specialAllowedPrimeLogHarmonic p n := by
  classical
  unfold specialAllowedPrimeLogHarmonic
  apply Finset.sum_nonneg
  intro l hl
  have hlprime := (mem_specialAllowedPrimesFinite.mp hl).1
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hlprime.one_le))
    (by positivity)

theorem sum_reciprocalLogDifference1081 {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Finset.Ico m n, Erdos469.reciprocalLogDifference k) =
      Erdos469.reciprocalLogWeight m -
        Erdos469.reciprocalLogWeight n := by
  calc
    (∑ k ∈ Finset.Ico m n, Erdos469.reciprocalLogDifference k) =
        -(∑ k ∈ Finset.Ico m n,
          (Erdos469.reciprocalLogWeight (k + 1) -
            Erdos469.reciprocalLogWeight k)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Erdos469.reciprocalLogDifference]
      ring
    _ = -(Erdos469.reciprocalLogWeight n -
        Erdos469.reciprocalLogWeight m) := by
      rw [Erdos469.sum_Ico_succ_sub Erdos469.reciprocalLogWeight hmn]
    _ = Erdos469.reciprocalLogWeight m -
        Erdos469.reciprocalLogWeight n := by ring

theorem exists_secondAbelMain_logLog_lower :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 3 ≤ n →
      Real.log (Real.log (n : ℝ)) - D ≤
        Erdos469.reciprocalLogWeight n * Real.log (n : ℝ) +
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k * Real.log (k : ℝ) := by
  let D₀ : ℝ :=
    |1 - Real.log (Real.log (2 : ℝ))| +
      (Real.log (2 : ℝ))⁻¹ ^ 2 * Erdos469.naturalSquareSeries
  let t₂ : ℝ :=
    Erdos469.reciprocalLogDifference 2 * Real.log (2 : ℝ)
  let D : ℝ := D₀ + |t₂|
  have hD₀ : 0 ≤ D₀ := by
    dsimp [D₀]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (sq_nonneg _)
        Erdos469.naturalSquareSeries_nonneg)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg hD₀ (abs_nonneg _)
  refine ⟨D, hD, ?_⟩
  intro n hn
  have hfull := Erdos469.reciprocalPrimeMain_eq_abelLog
    ((show 2 ≤ 3 by norm_num).trans hn)
  have hsplit := Finset.sum_Ico_consecutive
    (fun k : ℕ => Erdos469.reciprocalLogDifference k * Real.log (k : ℝ))
    (show 2 ≤ 3 by norm_num) hn
  have hmainEq :
      Erdos469.reciprocalLogWeight n * Real.log (n : ℝ) +
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k * Real.log (k : ℝ) =
        Erdos469.reciprocalPrimeMain n - t₂ := by
    rw [hfull]
    dsimp [t₂]
    have h23 :
        (∑ k ∈ Finset.Ico 2 3,
          Erdos469.reciprocalLogDifference k * Real.log (k : ℝ)) =
            Erdos469.reciprocalLogDifference 2 * Real.log (2 : ℝ) := by
      norm_num
    rw [← hsplit, h23]
    ring
  have herr := Erdos469.abs_reciprocalPrimeMain_sub_logLog_le
    ((show 2 ≤ 3 by norm_num).trans hn)
  have hlower : Real.log (Real.log (n : ℝ)) - D₀ ≤
      Erdos469.reciprocalPrimeMain n := by
    dsimp [D₀]
    linarith [neg_le_abs
      (Erdos469.reciprocalPrimeMain n -
        Real.log (Real.log (n : ℝ)))]
  rw [hmainEq]
  dsimp [D]
  linarith [le_abs_self t₂]

theorem exists_specialAllowedPrimeReciprocal_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ n : ℕ, 3 ≤ n →
      (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) - F ≤
        specialAllowedPrimeReciprocal p n := by
  obtain ⟨E, hE, hB⟩ :=
    exists_specialAllowedPrimeLogHarmonic_lower hp hp4
  obtain ⟨D, hD, hmain⟩ := exists_secondAbelMain_logLog_lower
  let w3 : ℝ := Erdos469.reciprocalLogWeight 3
  let F : ℝ := (1 / 2 : ℝ) * D + E * w3
  have hw3 : 0 ≤ w3 := by
    dsimp [w3, Erdos469.reciprocalLogWeight]
    positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  refine ⟨F, hF, ?_⟩
  intro n hn
  let main : ℝ :=
    Erdos469.reciprocalLogWeight n * Real.log (n : ℝ) +
      ∑ k ∈ Finset.Ico 3 n,
        Erdos469.reciprocalLogDifference k * Real.log (k : ℝ)
  have hmainLower : Real.log (Real.log (n : ℝ)) - D ≤ main := by
    dsimp [main]
    exact hmain n hn
  have hweightN : 0 ≤ Erdos469.reciprocalLogWeight n := by
    unfold Erdos469.reciprocalLogWeight
    positivity
  have hendpoint :
      Erdos469.reciprocalLogWeight n *
          ((1 / 2 : ℝ) * Real.log (n : ℝ) - E) ≤
        Erdos469.reciprocalLogWeight n *
          specialAllowedPrimeLogHarmonic p n :=
    mul_le_mul_of_nonneg_left (hB n hn) hweightN
  have hsum :
      (∑ k ∈ Finset.Ico 3 n,
        Erdos469.reciprocalLogDifference k *
          ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) ≤
        ∑ k ∈ Finset.Ico 2 n,
          Erdos469.reciprocalLogDifference k *
            specialAllowedPrimeLogHarmonic p k := by
    calc
      (∑ k ∈ Finset.Ico 3 n,
        Erdos469.reciprocalLogDifference k *
          ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) ≤
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              specialAllowedPrimeLogHarmonic p k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
        exact mul_le_mul_of_nonneg_left (hB k hk3)
          (Erdos469.reciprocalLogDifference_nonneg
            ((show 2 ≤ 3 by norm_num).trans hk3))
      _ ≤ ∑ k ∈ Finset.Ico 2 n,
            Erdos469.reciprocalLogDifference k *
              specialAllowedPrimeLogHarmonic p k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have hkI := Finset.mem_Ico.mp hk
          exact Finset.mem_Ico.mpr
            ⟨(show 2 ≤ 3 by norm_num).trans hkI.1, hkI.2⟩
        · intro k hk hkn
          exact mul_nonneg
            (Erdos469.reciprocalLogDifference_nonneg
              (Finset.mem_Ico.mp hk).1)
            (specialAllowedPrimeLogHarmonic_nonneg p k)
  have herrorEq :
      Erdos469.reciprocalLogWeight n * E +
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k * E = E * w3 := by
    have hsum3 := sum_reciprocalLogDifference1081
      (m := 3) (n := n) hn
    have hsumE :
        (∑ k ∈ Finset.Ico 3 n,
          Erdos469.reciprocalLogDifference k * E) =
            (∑ k ∈ Finset.Ico 3 n,
              Erdos469.reciprocalLogDifference k) * E := by
      rw [Finset.sum_mul]
    rw [hsumE, hsum3]
    dsimp [w3]
    ring
  have haber : (1 / 2 : ℝ) * main - E * w3 ≤
      specialAllowedPrimeReciprocal p n := by
    rw [specialAllowedPrimeReciprocal_eq_abel p
      ((show 2 ≤ 3 by norm_num).trans hn)]
    have hcombined := add_le_add hendpoint hsum
    have hexpand :
        Erdos469.reciprocalLogWeight n *
            ((1 / 2 : ℝ) * Real.log (n : ℝ) - E) +
          ∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              ((1 / 2 : ℝ) * Real.log (k : ℝ) - E) =
          (1 / 2 : ℝ) * main - E * w3 := by
      have hsumExpand :
          (∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) =
            (1 / 2 : ℝ) *
                (∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k *
                    Real.log (k : ℝ)) -
              ∑ k ∈ Finset.Ico 3 n,
                Erdos469.reciprocalLogDifference k * E := by
        calc
          (∑ k ∈ Finset.Ico 3 n,
            Erdos469.reciprocalLogDifference k *
              ((1 / 2 : ℝ) * Real.log (k : ℝ) - E)) =
              ∑ k ∈ Finset.Ico 3 n,
                ((1 / 2 : ℝ) *
                    (Erdos469.reciprocalLogDifference k *
                      Real.log (k : ℝ)) -
                  Erdos469.reciprocalLogDifference k * E) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = (∑ k ∈ Finset.Ico 3 n,
                (1 / 2 : ℝ) *
                  (Erdos469.reciprocalLogDifference k *
                    Real.log (k : ℝ))) -
                ∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k * E := by
            rw [Finset.sum_sub_distrib]
          _ = (1 / 2 : ℝ) *
                (∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k *
                    Real.log (k : ℝ)) -
                ∑ k ∈ Finset.Ico 3 n,
                  Erdos469.reciprocalLogDifference k * E := by
            rw [Finset.mul_sum]
      dsimp [main]
      rw [hsumExpand]
      rw [← herrorEq]
      ring
    rw [← hexpand]
    exact hcombined
  dsimp [F]
  linarith

/-- The quadratic Taylor remainder for `log (1 + x)` has the sign and
size needed for the squarefree Euler product. -/
theorem log_one_add_lower1081 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have hbase := Real.one_sub_inv_le_log_of_pos hpos
  have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [heq] at hbase
  have hfrac : x - x ^ 2 ≤ x / (1 + x) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  exact hfrac.trans hbase

theorem finite_sum_inv_sq_le_naturalSquareSeries (P : Finset ℕ) :
    (∑ q ∈ P, (q : ℝ)⁻¹ ^ 2) ≤ Erdos469.naturalSquareSeries := by
  calc
    (∑ q ∈ P, (q : ℝ)⁻¹ ^ 2) =
        ∑ q ∈ P, 1 / (q : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [one_div, inv_pow]
    _ ≤ ∑' q : ℕ, 1 / (q : ℝ) ^ 2 := by
      apply Erdos469.summable_naturalSquareSeries.sum_le_tsum
      intro q hq
      positivity
    _ = Erdos469.naturalSquareSeries := by
      rfl

theorem squarefreeEulerMass_pos (P : Finset ℕ) :
    0 < squarefreeEulerMass P := by
  unfold squarefreeEulerMass
  apply Finset.prod_pos
  intro q hq
  positivity

theorem specialAllowedPrimeReciprocal_sub_squareSeries_le_logEulerMass
    (p Q : ℕ) :
    specialAllowedPrimeReciprocal p Q - Erdos469.naturalSquareSeries ≤
      Real.log (squarefreeEulerMass (specialAllowedPrimesFinite p Q)) := by
  let P := specialAllowedPrimesFinite p Q
  have hsq : (∑ q ∈ P, (q : ℝ)⁻¹ ^ 2) ≤
      Erdos469.naturalSquareSeries :=
    finite_sum_inv_sq_le_naturalSquareSeries P
  have hnonzero : ∀ q ∈ P, (1 + (q : ℝ)⁻¹) ≠ 0 := by
    intro q hq
    positivity
  calc
    specialAllowedPrimeReciprocal p Q - Erdos469.naturalSquareSeries =
        (∑ q ∈ P, (q : ℝ)⁻¹) -
          Erdos469.naturalSquareSeries := by
      rfl
    _ ≤ (∑ q ∈ P, (q : ℝ)⁻¹) -
          ∑ q ∈ P, (q : ℝ)⁻¹ ^ 2 := by
      exact sub_le_sub_left hsq _
    _ = ∑ q ∈ P, ((q : ℝ)⁻¹ - (q : ℝ)⁻¹ ^ 2) := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ q ∈ P, Real.log (1 + (q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q hq
      exact log_one_add_lower1081 (by positivity)
    _ = Real.log (squarefreeEulerMass P) := by
      rw [squarefreeEulerMass, Real.log_prod hnonzero]

theorem exp_half_log_eq_sqrt_log {x : ℝ} (hx : 1 < x) :
    Real.exp ((1 / 2 : ℝ) * Real.log (Real.log x)) =
      Real.sqrt (Real.log x) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsqrt : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog
  rw [← Real.exp_log hsqrt]
  congr 1
  rw [Real.log_sqrt hlog.le]
  ring

theorem exists_squarefreeEulerMass_allowed_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q : ℕ, 3 ≤ Q →
      c * Real.sqrt (Real.log (Q : ℝ)) ≤
        squarefreeEulerMass (specialAllowedPrimesFinite p Q) := by
  obtain ⟨F, hF, hrec⟩ :=
    exists_specialAllowedPrimeReciprocal_lower hp hp4
  let C : ℝ := F + Erdos469.naturalSquareSeries
  let c : ℝ := Real.exp (-C)
  have hc : 0 < c := by
    dsimp [c]
    exact Real.exp_pos _
  refine ⟨c, hc, ?_⟩
  intro Q hQ
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hQ)
  have hlog :=
    specialAllowedPrimeReciprocal_sub_squareSeries_le_logEulerMass p Q
  have hrecQ := hrec Q hQ
  have hlogLower :
      (1 / 2 : ℝ) * Real.log (Real.log (Q : ℝ)) - C ≤
        Real.log (squarefreeEulerMass (specialAllowedPrimesFinite p Q)) := by
    dsimp [C]
    linarith
  have hexp := Real.exp_le_exp.mpr hlogLower
  rw [Real.exp_log (squarefreeEulerMass_pos _)] at hexp
  have hleft :
      Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (Q : ℝ)) - C) =
        c * Real.sqrt (Real.log (Q : ℝ)) := by
    rw [Real.exp_sub, exp_half_log_eq_sqrt_log hQreal]
    dsimp [c]
    rw [Real.exp_neg]
    simp only [div_eq_mul_inv]
    ring
  rw [hleft] at hexp
  exact hexp

theorem quarter_log_nat_le_log_sqrt {N : ℕ} (hN : 16 ≤ N) :
    (1 / 4 : ℝ) * Real.log (N : ℝ) ≤
      Real.log (N.sqrt : ℝ) := by
  have hs4 : 4 ≤ N.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hNlt : N < (N.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hsquare : (N.sqrt + 1) ^ 2 ≤ (2 * N.sqrt) ^ 2 := by
    nlinarith
  have hNfour : N ≤ 4 * N.sqrt ^ 2 := by
    have hlt : N < (2 * N.sqrt) ^ 2 := hNlt.trans_le hsquare
    nlinarith
  have hlogUpper : Real.log (N : ℝ) ≤
      Real.log (4 * (N.sqrt : ℝ) ^ 2) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hNfour
  have hlogUpper' : Real.log (N : ℝ) ≤
      Real.log (4 : ℝ) + 2 * Real.log (N.sqrt : ℝ) := by
    calc
      Real.log (N : ℝ) ≤
          Real.log (4 * (N.sqrt : ℝ) ^ 2) := hlogUpper
      _ = Real.log (4 : ℝ) + Real.log ((N.sqrt : ℝ) ^ 2) := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity)]
      _ = Real.log (4 : ℝ) + 2 * Real.log (N.sqrt : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hlog16 : Real.log (16 : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog4 : Real.log (4 : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (N : ℝ) := by
    have hlog16eq : Real.log (16 : ℝ) = 2 * Real.log (4 : ℝ) := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog16eq] at hlog16
    linarith
  linarith

theorem half_sqrt_log_nat_le_sqrt_log_sqrt {N : ℕ} (hN : 16 ≤ N) :
    (1 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
      Real.sqrt (Real.log (N.sqrt : ℝ)) := by
  have hquarter := quarter_log_nat_le_log_sqrt hN
  have hsqrt := Real.sqrt_le_sqrt hquarter
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hid : Real.sqrt ((1 / 4 : ℝ) * Real.log (N : ℝ)) =
      (1 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
  rw [hid] at hsqrt
  exact hsqrt

theorem exists_eventually_specialLocalReciprocal_sqrtLog_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N := by
  obtain ⟨c₀, hc₀, hEuler⟩ :=
    exists_squarefreeEulerMass_allowed_lower hp hp4
  let c : ℝ := c₀ / 8
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_primeLogReciprocalMass_allowed_sqrt_le p,
      eventually_ge_atTop 16] with N hmoment hN
  have hsqrt3 : 3 ≤ N.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hprime : ∀ q ∈ specialAllowedPrimesFinite p N.sqrt, q.Prime := by
    intro q hq
    exact (mem_specialAllowedPrimesFinite.mp hq).1
  have hretained := boundedSubsetEulerMass_lower_of_log_moment
    (specialAllowedPrimesFinite p N.sqrt) N (3 / 4 : ℝ)
    hprime (by omega) (by norm_num) (by norm_num) hmoment
  have hbridge := boundedSubsetEulerMass_le_localReciprocal p N.sqrt N
  have hEulerN := hEuler N.sqrt hsqrt3
  have hsqrtCompare := half_sqrt_log_nat_le_sqrt_log_sqrt hN
  dsimp [c]
  calc
    c₀ / 8 * Real.sqrt (Real.log (N : ℝ)) ≤
        (1 / 4 : ℝ) *
          (c₀ * Real.sqrt (Real.log (N.sqrt : ℝ))) := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrtCompare hc₀.le]
    _ ≤ (1 / 4 : ℝ) *
          squarefreeEulerMass (specialAllowedPrimesFinite p N.sqrt) := by
      exact mul_le_mul_of_nonneg_left hEulerN (by norm_num)
    _ ≤ boundedSubsetEulerMass
          (specialAllowedPrimesFinite p N.sqrt) N := by
      norm_num at hretained ⊢
      exact hretained
    _ ≤ HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N := hbridge

theorem specialLocalLogMass_nonneg (p Q : ℕ) :
    0 ≤ specialLocalLogMass p Q := by
  unfold specialLocalLogMass
  apply Finset.sum_nonneg
  intro l hl
  have hlprime := Nat.prime_of_mem_primesBelow hl
  apply Finset.sum_nonneg
  intro k hk
  exact specialLocalLogCoeff_nonneg p k hlprime

theorem tendsto_nat_sqrt_atTop1081 : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b ^ 2, ?_⟩
  intro N hN
  exact Nat.le_sqrt'.2 hN

/-- Integer division loses at most a factor two once the divisor lies below
the dividend. -/
theorem half_real_div_le_nat_div {N m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (N : ℝ) / (2 * (m : ℝ)) ≤ ((N / m : ℕ) : ℝ) := by
  have hq : 1 ≤ N / m := (Nat.one_le_div_iff hm).2 hmN
  have hrem : N % m < m := Nat.mod_lt N hm
  have hdecomp : N % m + m * (N / m) = N := Nat.mod_add_div N m
  have hmle : m ≤ m * (N / m) := by
    calc
      m = m * 1 := by simp
      _ ≤ m * (N / m) := Nat.mul_le_mul_left m hq
  have hNtwo : N ≤ 2 * (N / m) * m := by
    calc
      N = N % m + m * (N / m) := hdecomp.symm
      N % m + m * (N / m) ≤ m + m * (N / m) :=
        Nat.add_le_add_right hrem.le _
      _ ≤ m * (N / m) + m * (N / m) :=
        Nat.add_le_add_right hmle _
      _ = 2 * (N / m) * m := by ring
  have hNtwoR : (N : ℝ) ≤
      ((N / m : ℕ) : ℝ) * (2 * (m : ℝ)) := by
    exact_mod_cast (show N ≤ (N / m) * (2 * m) by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hNtwo)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2 hNtwoR

theorem logPartialSum_le_log_mul_partialSum
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {N : ℕ} (hN : 1 ≤ N) :
    HalberstamScratch.logPartialSum f N ≤
      Real.log (N : ℝ) * HalberstamScratch.partialSum f N := by
  unfold HalberstamScratch.logPartialSum HalberstamScratch.partialSum
  calc
    (∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 N, f n * Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnI := Finset.mem_Icc.mp hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnle : (n : ℝ) ≤ N := by exact_mod_cast hnI.2
      have hlog := Real.log_le_log hnpos hnle
      exact mul_le_mul_of_nonneg_left hlog (hf n)
    _ = Real.log (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, f n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem exists_eventually_specialLocal_logPartialSum_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.logPartialSum (specialLocalIndicator p) N := by
  obtain ⟨c₀, hc₀, hrec⟩ :=
    exists_eventually_specialLocalReciprocal_sqrtLog_lower hp hp4
  have hrecSqrt := tendsto_nat_sqrt_atTop1081.eventually hrec
  have hmass := eventually_specialLocalLogMass_lower hp hp4
  rw [eventually_atTop] at hmass
  obtain ⟨Q₀, hmass⟩ := hmass
  let c : ℝ := c₀ / 32
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [hrecSqrt, eventually_ge_atTop 16,
      tendsto_nat_sqrt_atTop1081.eventually (eventually_ge_atTop Q₀)]
      with N hrecN hN hsqrtQ₀
  have hsqrtCompare := half_sqrt_log_nat_le_sqrt_log_sqrt hN
  have hrecLower :
      (c₀ / 2) * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N.sqrt := by
    calc
      (c₀ / 2) * Real.sqrt (Real.log (N : ℝ)) =
          c₀ * ((1 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
        ring
      _ ≤ c₀ * Real.sqrt (Real.log (N.sqrt : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtCompare hc₀.le
      _ ≤ HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N.sqrt := hrecN
  have hsmallSub : Finset.Icc 1 N.sqrt ⊆ Finset.Icc 1 N := by
    intro m hm
    have hmI := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨hmI.1, hmI.2.trans (Nat.sqrt_le_self N)⟩
  have hsmallToFull :
      (∑ m ∈ Finset.Icc 1 N.sqrt,
        specialLocalIndicator p m * specialLocalLogMass p (N / m)) ≤
        ∑ m ∈ Finset.Icc 1 N,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsmallSub
    intro m hm hnot
    exact mul_nonneg (specialLocalIndicator_nonneg p m)
      (specialLocalLogMass_nonneg p (N / m))
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc 1 N.sqrt) :
      (1 / 16 : ℝ) * (N : ℝ) *
          (specialLocalIndicator p m / (m : ℝ)) ≤
        specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
    have hmI := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmI.1
    have hmN : m ≤ N := hmI.2.trans (Nat.sqrt_le_self N)
    have hqge : N.sqrt ≤ N / m := by
      apply (Nat.le_div_iff_mul_le hmpos).2
      calc
        N.sqrt * m ≤ N.sqrt * N.sqrt := Nat.mul_le_mul_left _ hmI.2
        _ ≤ N := Nat.sqrt_le N
    have hmassQ := hmass (N / m) (hsqrtQ₀.trans hqge)
    have hdiv := half_real_div_le_nat_div hmpos hmN
    have hscale :
        (1 / 16 : ℝ) * (N : ℝ) / (m : ℝ) ≤
          (1 / 8 : ℝ) * ((N / m : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 1 / 8)
      calc
        (1 / 16 : ℝ) * (N : ℝ) / (m : ℝ) =
            (1 / 8 : ℝ) * ((N : ℝ) / (2 * (m : ℝ))) := by
          field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmpos.ne']
          ring
        _ ≤ (1 / 8 : ℝ) * ((N / m : ℕ) : ℝ) := this
    calc
      (1 / 16 : ℝ) * (N : ℝ) *
          (specialLocalIndicator p m / (m : ℝ)) =
          specialLocalIndicator p m *
            ((1 / 16 : ℝ) * (N : ℝ) / (m : ℝ)) := by ring
      _ ≤ specialLocalIndicator p m *
          ((1 / 8 : ℝ) * ((N / m : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hscale
          (specialLocalIndicator_nonneg p m)
      _ ≤ specialLocalIndicator p m * specialLocalLogMass p (N / m) :=
        mul_le_mul_of_nonneg_left hmassQ
          (specialLocalIndicator_nonneg p m)
  have hconv := specialLocalIndicator_log_convolution p N
  rw [hconv]
  dsimp [c]
  calc
    c₀ / 32 * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        (1 / 16 : ℝ) * (N : ℝ) *
          HalberstamScratch.reciprocalPartialSum
            (specialLocalIndicator p) N.sqrt := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrecLower hNnonneg]
    _ = ∑ m ∈ Finset.Icc 1 N.sqrt,
          (1 / 16 : ℝ) * (N : ℝ) *
            (specialLocalIndicator p m / (m : ℝ)) := by
      unfold HalberstamScratch.reciprocalPartialSum
      rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.Icc 1 N.sqrt,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
      exact Finset.sum_le_sum hpoint
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) :=
      hsmallToFull

theorem exists_eventually_specialLocalValues_lower_fixed
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * landauScale N ≤ ((specialLocalValues p N).card : ℝ) := by
  obtain ⟨c, hc, hlogLower⟩ :=
    exists_eventually_specialLocal_logPartialSum_lower hp hp4
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlogLower, eventually_ge_atTop 3] with N hlower hN
  have hupper := logPartialSum_le_log_mul_partialSum
    (specialLocalIndicator p) (specialLocalIndicator_nonneg p) (show 1 ≤ N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtpos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  have hsquare : Real.sqrt (Real.log (N : ℝ)) ^ 2 =
      Real.log (N : ℝ) := Real.sq_sqrt hlogpos.le
  have hcombined :
      c * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        Real.log (N : ℝ) *
          HalberstamScratch.partialSum (specialLocalIndicator p) N :=
    hlower.trans hupper
  have hcancel :
      c * (N : ℝ) ≤
        HalberstamScratch.partialSum (specialLocalIndicator p) N *
          Real.sqrt (Real.log (N : ℝ)) := by
    apply le_of_mul_le_mul_right ?_ hsqrtpos
    calc
      c * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
          Real.log (N : ℝ) *
            HalberstamScratch.partialSum (specialLocalIndicator p) N := hcombined
      _ = (HalberstamScratch.partialSum (specialLocalIndicator p) N *
            Real.sqrt (Real.log (N : ℝ))) *
              Real.sqrt (Real.log (N : ℝ)) := by
        calc
          Real.log (N : ℝ) *
              HalberstamScratch.partialSum (specialLocalIndicator p) N =
              Real.sqrt (Real.log (N : ℝ)) ^ 2 *
                HalberstamScratch.partialSum (specialLocalIndicator p) N := by
            rw [hsquare]
          _ = (HalberstamScratch.partialSum (specialLocalIndicator p) N *
                Real.sqrt (Real.log (N : ℝ))) *
                  Real.sqrt (Real.log (N : ℝ)) := by ring
  rw [specialLocalValues_card_eq_indicator_partialSum]
  unfold landauScale
  rw [show c * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) =
      (c * (N : ℝ)) / Real.sqrt (Real.log (N : ℝ)) by ring]
  exact (div_le_iff₀ hsqrtpos).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel)

/-- Exact local Euler factor for the finite parity weight. -/
theorem parityWeight_eulerFactor
    {L : Finset ℕ} (hLprime : ∀ l ∈ L, l.Prime)
    (p : ℕ) (hp : p.Prime) :
    (∑' j : ℕ, parityWeight L (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
      else (1 - (p : ℝ)⁻¹)⁻¹ := by
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity : (0 : ℝ) < p)).2 hpR
  by_cases hpL : p ∈ L
  · rw [if_pos hpL]
    calc
      (∑' j : ℕ, parityWeight L (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, if Even j then r ^ j else 0 := by
            apply tsum_congr
            intro j
            rw [parityWeight_prime_pow hLprime p j hp]
            by_cases hj : Even j <;>
              simp [hpL, hj, r, div_eq_mul_inv, inv_pow]
      _ = (1 - r ^ 2)⁻¹ := tsum_even_geometric1081 hr0 hr1
      _ = (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹ := by rfl
  · rw [if_neg hpL]
    calc
      (∑' j : ℕ, parityWeight L (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, r ^ j := by
            apply tsum_congr
            intro j
            rw [parityWeight_prime_pow hLprime p j hp]
            simp [hpL, r, div_eq_mul_inv, inv_pow]
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
      _ = (1 - (p : ℝ)⁻¹)⁻¹ := by rfl

/-- A value represented by both special forms satisfies every local parity
condition which is anisotropic for at least one of the forms. -/
theorem specialPairValues_subset_parityAdmissible
    {p q N : ℕ} (L : Finset ℕ)
    (hL : ∀ l ∈ L, l.Prime ∧
      (FormAnisotropicAt (p ^ 3) l ∨ FormAnisotropicAt (q ^ 3) l)) :
    specialFormValues p N ∩ specialFormValues q N ⊆
      (Finset.Icc 1 N).filter (ParityAdmissible L) := by
  classical
  intro n hn
  rcases Finset.mem_inter.mp hn with ⟨hnp, hnq⟩
  rw [mem_specialFormValues] at hnp hnq
  rcases hnp with ⟨hnIcc, u, _hu, v, _hv, huv⟩
  rcases hnq with ⟨_hnIcc', a, _ha, b, _hb, hab⟩
  rw [Finset.mem_filter]
  refine ⟨hnIcc, ?_⟩
  intro l hlL
  rcases hL l hlL with ⟨hl, haniso | haniso⟩
  · rw [huv]
    exact even_padicValNat_of_specialForm hl haniso
      (huv ▸ lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1)
  · rw [hab]
    exact even_padicValNat_of_specialForm hl haniso
      (hab ▸ lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1)

/-- The represented-value intersection is bounded by the corresponding
finite parity-sieve count. -/
theorem specialPairCount_le_parityAdmissibleCount
    {p q N : ℕ} (L : Finset ℕ)
    (hL : ∀ l ∈ L, l.Prime ∧
      (FormAnisotropicAt (p ^ 3) l ∨ FormAnisotropicAt (q ^ 3) l)) :
    specialPairCount p q N ≤ parityAdmissibleCount L N := by
  classical
  exact Finset.card_le_card (specialPairValues_subset_parityAdmissible L hL)

/-- End-to-end reduction of a represented-value intersection to the explicit
Halberstam--Richert Euler product attached to any finite set of obstruction
primes. -/
theorem specialPairCount_le_parityEulerProduct
    {p q N : ℕ} (L : Finset ℕ)
    (hL : ∀ l ∈ L, l.Prime ∧
      (FormAnisotropicAt (p ^ 3) l ∨ FormAnisotropicAt (q ^ 3) l))
    (hN : 2 ≤ N) :
    (specialPairCount p q N : ℝ) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ l ∈ (N + 1).primesBelow,
            ∑' j : ℕ, parityWeight L (l ^ j) / ((l ^ j : ℕ) : ℝ) := by
  have hLprime : ∀ l ∈ L, l.Prime := fun l hl ↦ (hL l hl).1
  calc
    (specialPairCount p q N : ℝ) ≤
        (parityAdmissibleCount L N : ℝ) := by
      exact_mod_cast specialPairCount_le_parityAdmissibleCount L hL
    _ = ∑ n ∈ Finset.Icc 1 N, parityWeight L n :=
      (parityWeight_sum_eq_count L N).symm
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ l ∈ (N + 1).primesBelow,
              ∑' j : ℕ, parityWeight L (l ^ j) /
                ((l ^ j : ℕ) : ℝ) :=
      parityWeight_mean_le_euler L hLprime N hN

/-- The same pair bound with every local factor evaluated. -/
theorem specialPairCount_le_explicitParityEulerProduct
    {p q N : ℕ} (L : Finset ℕ)
    (hL : ∀ l ∈ L, l.Prime ∧
      (FormAnisotropicAt (p ^ 3) l ∨ FormAnisotropicAt (q ^ 3) l))
    (hN : 2 ≤ N) :
    (specialPairCount p q N : ℝ) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ l ∈ (N + 1).primesBelow,
            if l ∈ L then (1 - ((l : ℝ)⁻¹) ^ 2)⁻¹
            else (1 - (l : ℝ)⁻¹)⁻¹ := by
  have hLprime : ∀ l ∈ L, l.Prime := fun l hl ↦ (hL l hl).1
  calc
    (specialPairCount p q N : ℝ) ≤
        (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ l ∈ (N + 1).primesBelow,
              ∑' j : ℕ, parityWeight L (l ^ j) /
                ((l ^ j : ℕ) : ℝ) :=
      specialPairCount_le_parityEulerProduct L hL hN
    _ = (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ l ∈ (N + 1).primesBelow,
              if l ∈ L then (1 - ((l : ℝ)⁻¹) ^ 2)⁻¹
              else (1 - (l : ℝ)⁻¹)⁻¹ := by
      congr 1
      apply Finset.prod_congr rfl
      intro l hl
      exact parityWeight_eulerFactor hLprime l
        (Nat.prime_of_mem_primesBelow hl)

/-- The canonical finite set of local obstructions for a pair of special
forms, truncated at `N`. -/
noncomputable def specialPairObstructionPrimes (p q N : ℕ) : Finset ℕ := by
  classical
  exact (N + 1).primesBelow.filter fun l ↦
    IsQuadraticObstruction (p ^ 3) l ∨ IsQuadraticObstruction (q ^ 3) l

@[simp] theorem mem_specialPairObstructionPrimes {p q N l : ℕ} :
    l ∈ specialPairObstructionPrimes p q N ↔
      l.Prime ∧ l < N + 1 ∧
        (IsQuadraticObstruction (p ^ 3) l ∨
          IsQuadraticObstruction (q ^ 3) l) := by
  classical
  simp [specialPairObstructionPrimes, Nat.mem_primesBelow, and_left_comm,
    and_assoc]

/-- Canonical pair-sieve bound.  At this point only an estimate for the
displayed, completely explicit quadratic-character Euler product remains. -/
theorem specialPairCount_le_quadraticObstructionEulerProduct
    {p q N : ℕ} (hN : 2 ≤ N) :
    (specialPairCount p q N : ℝ) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ l ∈ (N + 1).primesBelow,
            if l ∈ specialPairObstructionPrimes p q N then
              (1 - ((l : ℝ)⁻¹) ^ 2)⁻¹
            else (1 - (l : ℝ)⁻¹)⁻¹ := by
  apply specialPairCount_le_explicitParityEulerProduct
    (specialPairObstructionPrimes p q N) _ hN
  intro l hl
  rw [mem_specialPairObstructionPrimes] at hl
  refine ⟨hl.1, ?_⟩
  rcases hl.2.2 with hp | hq
  · exact Or.inl (formAnisotropicAt_of_not_isSquare_neg hl.1 hp)
  · exact Or.inr (formAnisotropicAt_of_not_isSquare_neg hl.1 hq)

/-! ### Euler-product suppression from reciprocal obstruction mass -/

/-- The extra local factor contributed by imposing even valuation at a
prime. -/
noncomputable def obstructionPenalty (L : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ L then (1 + (p : ℝ)⁻¹)⁻¹ else 1

theorem obstructionPenalty_nonneg (L : Finset ℕ) {p : ℕ}
    (_hp : p.Prime) : 0 ≤ obstructionPenalty L p := by
  unfold obstructionPenalty
  split_ifs <;> positivity

theorem explicitParityEulerFactor_eq_mertens_mul_penalty
    (L : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    (if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
      else (1 - (p : ℝ)⁻¹)⁻¹) =
      (Erdos469.mertensLinearFactor p)⁻¹ * obstructionPenalty L p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hminus : (1 - (p : ℝ)⁻¹) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 hpR))
  have hplus : (1 + (p : ℝ)⁻¹) ≠ 0 := by
    positivity
  unfold Erdos469.mertensLinearFactor obstructionPenalty
  simp only [zpow_neg, zpow_ofNat, pow_one]
  by_cases hpL : p ∈ L
  · rw [if_pos hpL, if_pos hpL]
    rw [← mul_inv, show
      (1 - (p : ℝ)⁻¹) * (1 + (p : ℝ)⁻¹) =
        1 - ((p : ℝ)⁻¹) ^ 2 by ring]
  · simp [hpL]

/-- Pointwise exponential bound for an obstruction penalty.  The quadratic
term is summable, so the linear reciprocal-prime mass controls the product. -/
theorem obstructionPenalty_le_exp (L : Finset ℕ) {p : ℕ}
    (hp : p.Prime) :
    obstructionPenalty L p ≤
      Real.exp (if p ∈ L then -(p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2 else 0) := by
  by_cases hpL : p ∈ L
  · rw [obstructionPenalty, if_pos hpL, if_pos hpL]
    let r : ℝ := (p : ℝ)⁻¹
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hr0 : 0 ≤ r := by positivity
    have hrhalf : r ≤ 1 / 2 := by
      dsimp [r]
      simpa [one_div] using
        (inv_le_inv₀ hp0 (by positivity : (0 : ℝ) < 2)).2
          (by exact_mod_cast hp.two_le)
    have hden : 0 < r + 2 := by positivity
    have hrat : r - r ^ 2 ≤ 2 * r / (r + 2) := by
      rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg r, mul_nonneg hr0 (sub_nonneg.mpr hrhalf)]
    have hlog : r - r ^ 2 ≤ Real.log (1 + r) :=
      hrat.trans (Real.le_log_one_add_of_nonneg hr0)
    calc
      (1 + (p : ℝ)⁻¹)⁻¹ = Real.exp (-Real.log (1 + r)) := by
        dsimp [r]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ ≤ Real.exp (-r + r ^ 2) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-(p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2) := by rfl
  · simp [obstructionPenalty, hpL]

/-- Finite reciprocal mass of the obstruction primes inside an ambient
prime set. -/
noncomputable def obstructionReciprocalMass
    (P L : Finset ℕ) : ℝ :=
  ∑ p ∈ P.filter (fun p ↦ p ∈ L), (p : ℝ)⁻¹

/-- Every prime in the geometric shell union is in the canonical
quadratic-obstruction set at the final endpoint. -/
theorem geometricPairObstructionPrimesBetween_subset
    {p q k₀ K : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hk₀ : 3 ≤ k₀) :
    geometricPairObstructionPrimesBetween hpq k₀ K ⊆
      specialPairObstructionPrimes p q (geometricEndpoint K) := by
  intro l hl
  rw [geometricPairObstructionPrimesBetween, Finset.mem_biUnion] at hl
  rcases hl with ⟨k, hk, hl⟩
  have hkI := Finset.mem_Icc.mp hk
  rw [geometricPairObstructionPrimes, Finset.mem_biUnion] at hl
  rcases hl with ⟨a, ha, hla⟩
  have hldata := Finset.mem_filter.mp hla
  have hlI := Finset.mem_Ioc.mp hldata.1
  have hlprime : l.Prime := hldata.2.1
  have hlle : l ≤ geometricEndpoint K := by
    dsimp [geometricEndpoint]
    exact hlI.2.trans (Nat.floor_mono
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4 / 3) (by omega)))
  have hl2 : l ≠ 2 := by
    have hlLower : (4 / 3 : ℝ) ^ k < (l : ℝ) :=
      Nat.lt_of_floor_lt hlI.1
    have hthree : (2 : ℝ) < (4 / 3 : ℝ) ^ 3 := by norm_num
    have hpow : (4 / 3 : ℝ) ^ 3 ≤ (4 / 3 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (hk₀.trans hkI.1)
    intro heq
    subst l
    norm_num at hlLower hthree hpow
    linarith
  rw [mem_specialPairObstructionPrimes]
  refine ⟨hlprime, by omega, ?_⟩
  exact pairNonresidueResidue_is_obstruction hpq hp4 hq4 hlprime hl2 ha
    hldata.2.2

/-- The explicit shell union supplies a lower bound for the canonical
obstruction reciprocal mass. -/
theorem geometricPairObstructionPrimesBetween_sum_le_mass
    {p q k₀ K : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hk₀ : 3 ≤ k₀) :
    (∑ l ∈ geometricPairObstructionPrimesBetween hpq k₀ K,
        (l : ℝ)⁻¹) ≤
      obstructionReciprocalMass ((geometricEndpoint K) + 1).primesBelow
        (specialPairObstructionPrimes p q (geometricEndpoint K)) := by
  unfold obstructionReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    rw [Finset.mem_filter]
    have hobs :=
      geometricPairObstructionPrimesBetween_subset hpq hp4 hq4 hk₀ hl
    rw [mem_specialPairObstructionPrimes] at hobs
    exact ⟨Nat.mem_primesBelow.mpr ⟨hobs.2.1, hobs.1⟩,
      (mem_specialPairObstructionPrimes.mpr hobs)⟩
  · intro l hl _
    positivity

/-- Splitting the harmonic sum at a fixed index loses only a fixed finite
prefix. -/
theorem harmonic_le_prefix_add_tail {k₀ K : ℕ}
    (hk₀ : 1 ≤ k₀) (hK : k₀ ≤ K) :
    (harmonic K : ℝ) ≤
      (∑ k ∈ Finset.Icc 1 (k₀ - 1), (k : ℝ)⁻¹) +
        ∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hdis : Disjoint (Finset.Icc 1 (k₀ - 1)) (Finset.Icc k₀ K) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hxI := Finset.mem_Icc.mp hx
    have hyI := Finset.mem_Icc.mp hy
    omega
  rw [← Finset.sum_union hdis]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_union]
    have hxI := Finset.mem_Icc.mp hx
    by_cases hxk : x < k₀
    · left
      rw [Finset.mem_Icc]
      omega
    · right
      rw [Finset.mem_Icc]
      omega
  · intro x hx _
    positivity

/-- Finite families of primes congruent to `3 mod 4` have arbitrarily
large reciprocal mass.  This is the exact finite form of Dirichlet's
theorem needed for the diagonal Bernays argument below. -/
theorem exists_threeModFourPrimeFamily_reciprocal_ge (R : ℝ) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p % 4 = 3) ∧
        R ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1
    (eventually_geometricAPPrimes_reciprocal_lower
      (q := 4) (a := 3) (by norm_num) (by norm_num) (by norm_num))
  let k₀ : ℕ := max 1 k₁
  let d : ℝ := (6 / 25 : ℝ) /
    (((4 : ℕ).totient : ℝ) * Real.log (4 / 3 : ℝ))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  let preMass : ℝ :=
    ∑ k ∈ Finset.Icc 1 (k₀ - 1), (k : ℝ)⁻¹
  have hharm : Tendsto (fun K : ℕ => (harmonic K : ℝ)) atTop atTop := by
    have hlog : Tendsto (fun K : ℕ => Real.log (K + 1 : ℕ)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    apply tendsto_atTop_mono' atTop (Eventually.of_forall fun K => ?_) hlog
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic K
  have hlarge : ∀ᶠ K : ℕ in atTop,
      preMass + R / d ≤ (harmonic K : ℝ) :=
    (tendsto_atTop.1 hharm) (preMass + R / d)
  obtain ⟨K, hKlarge, hK₀⟩ :=
    (hlarge.and (eventually_ge_atTop k₀)).exists
  let P := geometricAPPrimesBetween 4 3 k₀ K
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    change p ∈ geometricAPPrimesBetween 4 3 k₀ K at hp
    rw [geometricAPPrimesBetween, Finset.mem_biUnion] at hp
    rcases hp with ⟨k, _hk, hpk⟩
    exact (Finset.mem_filter.mp hpk).2
  · have hk₀one : 1 ≤ k₀ := by
      dsimp [k₀]
      exact le_max_left _ _
    have htail := harmonic_le_prefix_add_tail hk₀one hK₀
    have hRtail : R ≤ d *
        (∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹) := by
      have hdiv : R ≤ d * (R / d) := by
        field_simp [hd.ne']
        exact le_rfl
      have : R / d ≤
          ∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹ := by
        dsimp [preMass] at hKlarge
        linarith
      exact hdiv.trans (mul_le_mul_of_nonneg_left this hd.le)
    change R ≤ ∑ p ∈ P, (p : ℝ)⁻¹
    rw [show P = geometricAPPrimesBetween 4 3 k₀ K by rfl]
    calc
      R ≤ d * (∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹) := hRtail
      _ = ∑ k ∈ Finset.Icc k₀ K, d * (k : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.Icc k₀ K,
          ∑ p ∈ geometricAPPrimes 4 3 k, (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        have hkone : 1 ≤ k := hk₀one.trans (Finset.mem_Icc.mp hk).1
        have hraw := hk₁ k ((le_max_right 1 k₁).trans
          (Finset.mem_Icc.mp hk).1)
        have hkne : (k : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt
            (lt_of_lt_of_le Nat.zero_lt_one hkone))
        have hlogne : Real.log (4 / 3 : ℝ) ≠ 0 :=
          (Real.log_pos (by norm_num)).ne'
        have heq : d * (k : ℝ)⁻¹ =
            (6 / 25 : ℝ) /
              (((4 : ℕ).totient : ℝ) * (k : ℝ) *
                Real.log (4 / 3 : ℝ)) := by
          dsimp [d]
          norm_num [Nat.totient]
          field_simp
        rw [heq]
        exact hraw
      _ = ∑ p ∈ geometricAPPrimesBetween 4 3 k₀ K,
          (p : ℝ)⁻¹ := (geometricAPPrimesBetween_sum_eq 4 3 k₀ K).symm

theorem geometricEndpoint_ge_three {K : ℕ} (hK : 3 ≤ K) :
    3 ≤ geometricEndpoint K := by
  apply Nat.le_floor
  have hpow : (4 / 3 : ℝ) ^ 4 ≤ (4 / 3 : ℝ) ^ (K + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact (by norm_num : (3 : ℝ) ≤ (4 / 3 : ℝ) ^ 4).trans hpow

/-- At geometric endpoints, `log log` of the natural endpoint is no larger
than the logarithm of the shell index. -/
theorem log_log_geometricEndpoint_le {K : ℕ} (hK : 3 ≤ K) :
    Real.log (Real.log (geometricEndpoint K : ℝ)) ≤
      Real.log (K + 1 : ℕ) := by
  have hN3 := geometricEndpoint_ge_three hK
  have hNpos : (0 : ℝ) < geometricEndpoint K := by
    exact_mod_cast (by omega : 0 < geometricEndpoint K)
  have hN1 : (1 : ℝ) < geometricEndpoint K := by
    exact_mod_cast (by omega : 1 < geometricEndpoint K)
  have hfloor : (geometricEndpoint K : ℝ) ≤
      (4 / 3 : ℝ) ^ (K + 1) := by
    dsimp [geometricEndpoint]
    exact Nat.floor_le (by positivity)
  have hlogpow : Real.log (geometricEndpoint K : ℝ) ≤
      Real.log ((4 / 3 : ℝ) ^ (K + 1)) :=
    Real.log_le_log hNpos hfloor
  have hlogb : Real.log (4 / 3 : ℝ) ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h ⊢
    linarith
  have hlogNle : Real.log (geometricEndpoint K : ℝ) ≤
      (K + 1 : ℕ) := by
    rw [Real.log_pow] at hlogpow
    push_cast at hlogpow ⊢
    have hKnonneg : (0 : ℝ) ≤ K + 1 := by positivity
    exact hlogpow.trans (by nlinarith)
  exact Real.log_le_log (Real.log_pos hN1) hlogNle

/-- The canonical pair-obstruction mass has a coefficient strictly larger
than `1/2` in front of `log log` along the geometric endpoints. -/
theorem exists_geometricEndpoint_obstructionMassLower
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ C : ℝ, ∀ K : ℕ, k₀ ≤ K →
      (13 / 25 : ℝ) *
          Real.log (Real.log (geometricEndpoint K : ℝ)) - C ≤
        obstructionReciprocalMass ((geometricEndpoint K) + 1).primesBelow
          (specialPairObstructionPrimes p q (geometricEndpoint K)) := by
  obtain ⟨k₀, hk₀3, hshell⟩ :=
    exists_geometricPairObstruction_harmonic_lower hpq hp2 hq2
  let C : ℝ := (27 / 50 : ℝ) *
    (∑ k ∈ Finset.Icc 1 (k₀ - 1), (k : ℝ)⁻¹)
  refine ⟨k₀, hk₀3, C, ?_⟩
  intro K hK
  have hloglog := log_log_geometricEndpoint_le (hk₀3.trans hK)
  have hharm := harmonic_le_prefix_add_tail (by omega : 1 ≤ k₀) hK
  have hlogharm : Real.log (K + 1 : ℕ) ≤ (harmonic K : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic K
  have htail : Real.log (K + 1 : ℕ) -
      (∑ k ∈ Finset.Icc 1 (k₀ - 1), (k : ℝ)⁻¹) ≤
        ∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹ := by
    linarith
  have hshell' := hshell K hK
  have hmass := geometricPairObstructionPrimesBetween_sum_le_mass
    hpq hp4 hq4 hk₀3 (K := K)
  have hlognonneg : 0 ≤ Real.log (K + 1 : ℕ) := by
    exact Real.log_natCast_nonneg (K + 1)
  calc
    (13 / 25 : ℝ) *
          Real.log (Real.log (geometricEndpoint K : ℝ)) - C ≤
        (27 / 50 : ℝ) * (Real.log (K + 1 : ℕ) -
          (∑ k ∈ Finset.Icc 1 (k₀ - 1), (k : ℝ)⁻¹)) := by
      dsimp [C]
      nlinarith
    _ ≤ (27 / 50 : ℝ) *
        (∑ k ∈ Finset.Icc k₀ K, (k : ℝ)⁻¹) := by
      nlinarith
    _ ≤ ∑ l ∈ geometricPairObstructionPrimesBetween hpq k₀ K,
        (l : ℝ)⁻¹ := hshell'
    _ ≤ obstructionReciprocalMass ((geometricEndpoint K) + 1).primesBelow
        (specialPairObstructionPrimes p q (geometricEndpoint K)) := hmass

theorem obstructionPenalty_prod_le_exp
    (P L : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, obstructionPenalty L p) ≤
      Real.exp (-obstructionReciprocalMass P L +
        Erdos469.naturalSquareSeries) := by
  let S := P.filter fun p ↦ p ∈ L
  have hprod : (∏ p ∈ P, obstructionPenalty L p) ≤
      ∏ p ∈ P,
        Real.exp (if p ∈ L then -(p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2 else 0) := by
    exact Finset.prod_le_prod
      (fun p hp ↦ obstructionPenalty_nonneg L (hPprime p hp))
      (fun p hp ↦ obstructionPenalty_le_exp L (hPprime p hp))
  have hsquare : (∑ p ∈ S, ((p : ℝ)⁻¹) ^ 2) ≤
      Erdos469.naturalSquareSeries := by
    have h := Erdos469.summable_naturalSquareSeries.sum_le_tsum S
      (fun n _ ↦ by positivity)
    simpa [Erdos469.naturalSquareSeries, div_eq_mul_inv, inv_pow] using h
  calc
    (∏ p ∈ P, obstructionPenalty L p) ≤
        ∏ p ∈ P,
          Real.exp (if p ∈ L then -(p : ℝ)⁻¹ +
            ((p : ℝ)⁻¹) ^ 2 else 0) := hprod
    _ = Real.exp (∑ p ∈ P,
          if p ∈ L then -(p : ℝ)⁻¹ +
            ((p : ℝ)⁻¹) ^ 2 else 0) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(∑ p ∈ S, (p : ℝ)⁻¹) +
          ∑ p ∈ S, ((p : ℝ)⁻¹) ^ 2) := by
      congr 1
      dsimp [S]
      rw [← Finset.sum_filter, Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib]
    _ ≤ Real.exp (-(∑ p ∈ S, (p : ℝ)⁻¹) +
          Erdos469.naturalSquareSeries) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-obstructionReciprocalMass P L +
          Erdos469.naturalSquareSeries) := by
      rfl

theorem primesBelow_succ_eq_primesThrough (N : ℕ) :
    (N + 1).primesBelow = Erdos469.primesThrough N := by
  ext p
  simp [Nat.mem_primesBelow, Erdos469.mem_primesThrough, and_comm]

/-- Factor the parity Euler product into the inverse classical Mertens
product and the obstruction penalty. -/
theorem explicitParityEulerProduct_eq
    (L : Finset ℕ) (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
        if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
        else (1 - (p : ℝ)⁻¹)⁻¹) =
      ((∏ p ∈ (N + 1).primesBelow,
          Erdos469.mertensLinearFactor p)⁻¹) *
        ∏ p ∈ (N + 1).primesBelow, obstructionPenalty L p := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact explicitParityEulerFactor_eq_mertens_mul_penalty L
    (Nat.prime_of_mem_primesBelow hp)

/-- Quantitative Euler-product upper bound in terms of the reciprocal mass
of the chosen obstruction primes. -/
theorem explicitParityEulerProduct_le_of_mass
    (L : Finset ℕ) {N : ℕ} (hN : 2 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
        if p ∈ L then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
        else (1 - (p : ℝ)⁻¹)⁻¹) ≤
      (Erdos469.naturalLinearMertensLower / Real.log (N : ℝ))⁻¹ *
        Real.exp (-obstructionReciprocalMass (N + 1).primesBelow L +
          Erdos469.naturalSquareSeries) := by
  let P := (N + 1).primesBelow
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN))
  have hbase : 0 < Erdos469.naturalLinearMertensLower /
      Real.log (N : ℝ) :=
    div_pos Erdos469.naturalLinearMertensLower_pos hlog
  have hPeq : P = Erdos469.primesThrough N :=
    primesBelow_succ_eq_primesThrough N
  have hlinearPos : 0 < ∏ p ∈ P, Erdos469.mertensLinearFactor p := by
    rw [hPeq]
    exact Erdos469.linearMertensProduct_pos N
  have hlinearLower : Erdos469.naturalLinearMertensLower /
      Real.log (N : ℝ) ≤
        ∏ p ∈ P, Erdos469.mertensLinearFactor p := by
    rw [hPeq]
    exact (Erdos469.natural_linearMertensProduct_bounds hN).1
  have hinv : ((∏ p ∈ P, Erdos469.mertensLinearFactor p)⁻¹) ≤
      (Erdos469.naturalLinearMertensLower /
        Real.log (N : ℝ))⁻¹ :=
    (inv_le_inv₀ hlinearPos hbase).2 hlinearLower
  have hpenalty : (∏ p ∈ P, obstructionPenalty L p) ≤
      Real.exp (-obstructionReciprocalMass P L +
        Erdos469.naturalSquareSeries) :=
    obstructionPenalty_prod_le_exp P L fun p hp ↦
      Nat.prime_of_mem_primesBelow hp
  rw [explicitParityEulerProduct_eq]
  exact mul_le_mul hinv hpenalty
    (Finset.prod_nonneg fun r hr ↦ obstructionPenalty_nonneg L
      (Nat.prime_of_mem_primesBelow hr))
    (inv_nonneg.mpr hbase.le)

/-- Pair-count estimate with all sieve mechanics discharged.  Its only
remaining input is the explicit reciprocal mass of the quadratic
obstruction primes. -/
theorem specialPairCount_le_of_obstructionMass
    {p q N : ℕ} (hN : 2 ≤ N) :
    (specialPairCount p q N : ℝ) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ((Erdos469.naturalLinearMertensLower /
            Real.log (N : ℝ))⁻¹ *
            Real.exp (-obstructionReciprocalMass (N + 1).primesBelow
              (specialPairObstructionPrimes p q N) +
              Erdos469.naturalSquareSeries)) := by
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN))
  have hcoefficient : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
          (by norm_num))
        (Nat.cast_nonneg N)) hlog.le
  exact (specialPairCount_le_quadraticObstructionEulerProduct hN).trans
    (mul_le_mul_of_nonneg_left
      (explicitParityEulerProduct_le_of_mass
        (specialPairObstructionPrimes p q N) hN)
      hcoefficient)

/-- If the quadratic obstruction primes have reciprocal mass at least
`beta * log log N - C`, the represented-value intersection has the
corresponding logarithmic saving.  This is kept in exponential form so that
the exact finite inequality has no side condition on `log log N`. -/
theorem specialPairCount_le_of_obstructionMassLower
    {p q N : ℕ} {beta C : ℝ} (hN : 2 ≤ N)
    (hmass : beta * Real.log (Real.log (N : ℝ)) - C ≤
      obstructionReciprocalMass (N + 1).primesBelow
        (specialPairObstructionPrimes p q N)) :
    (specialPairCount p q N : ℝ) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ((Erdos469.naturalLinearMertensLower /
            Real.log (N : ℝ))⁻¹ *
            Real.exp (-beta * Real.log (Real.log (N : ℝ)) + C +
              Erdos469.naturalSquareSeries)) := by
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN))
  have hcoefficient : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
          (by norm_num))
        (Nat.cast_nonneg N)) hlog.le
  have hexp : Real.exp
      (-obstructionReciprocalMass (N + 1).primesBelow
          (specialPairObstructionPrimes p q N) +
        Erdos469.naturalSquareSeries) ≤
      Real.exp (-beta * Real.log (Real.log (N : ℝ)) + C +
        Erdos469.naturalSquareSeries) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hinv : 0 ≤ (Erdos469.naturalLinearMertensLower /
      Real.log (N : ℝ))⁻¹ := by
    exact inv_nonneg.mpr (div_nonneg
      Erdos469.naturalLinearMertensLower_pos.le hlog.le)
  exact (specialPairCount_le_of_obstructionMass hN).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp hinv) hcoefficient)

/-- The pair-overlap estimate at the explicit geometric endpoints, in the
usual power-of-log form.  In particular, the saving `13 / 25` is strictly
larger than the square-root exponent `1 / 2`. -/
theorem exists_geometricEndpoint_specialPairCount_upper
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, k₀ ≤ K →
      (specialPairCount p q (geometricEndpoint K) : ℝ) ≤
        C * (geometricEndpoint K : ℝ) /
          (Real.log (geometricEndpoint K : ℝ)) ^ (13 / 25 : ℝ) := by
  obtain ⟨k₀, hk₀, C₀, hmass⟩ :=
    exists_geometricEndpoint_obstructionMassLower hpq hp4 hq4 hp2 hq2
  let C : ℝ :=
    (HalberstamScratch.explicitMassConstant 1 1 + 1) /
      Erdos469.naturalLinearMertensLower *
        Real.exp (C₀ + Erdos469.naturalSquareSeries)
  have hC : 0 < C := by
    dsimp [C]
    have hH : 0 < HalberstamScratch.explicitMassConstant 1 1 + 1 :=
      lt_of_le_of_lt
        (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
        (lt_add_one _)
    exact mul_pos (div_pos hH Erdos469.naturalLinearMertensLower_pos)
      (Real.exp_pos _)
  refine ⟨k₀, hk₀, C, hC, ?_⟩
  intro K hK
  let N := geometricEndpoint K
  have hN3 : 3 ≤ N := geometricEndpoint_ge_three (hk₀.trans hK)
  have hN2 : 2 ≤ N := by omega
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpair := specialPairCount_le_of_obstructionMassLower
    (p := p) (q := q) (N := N) (beta := (13 / 25 : ℝ))
    (C := C₀) hN2 (hmass K hK)
  have hexp :
      Real.exp (-(13 / 25 : ℝ) * Real.log (Real.log (N : ℝ)) + C₀ +
          Erdos469.naturalSquareSeries) =
        (Real.log (N : ℝ)) ^ (-(13 / 25 : ℝ)) *
          Real.exp (C₀ + Erdos469.naturalSquareSeries) := by
    rw [show -(13 / 25 : ℝ) * Real.log (Real.log (N : ℝ)) + C₀ +
          Erdos469.naturalSquareSeries =
        (-(13 / 25 : ℝ)) * Real.log (Real.log (N : ℝ)) +
          (C₀ + Erdos469.naturalSquareSeries) by ring,
      Real.exp_add]
    congr 1
    rw [Real.rpow_def_of_pos hlog]
    congr 1
    ring
  rw [hexp] at hpair
  have hMpos : 0 < Erdos469.naturalLinearMertensLower :=
    Erdos469.naturalLinearMertensLower_pos
  have hpowpos : 0 < (Real.log (N : ℝ)) ^ (13 / 25 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  change (specialPairCount p q N : ℝ) ≤ _
  calc
    (specialPairCount p q N : ℝ) ≤
        (HalberstamScratch.explicitMassConstant 1 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ((Erdos469.naturalLinearMertensLower /
              Real.log (N : ℝ))⁻¹ *
              ((Real.log (N : ℝ)) ^ (-(13 / 25 : ℝ)) *
                Real.exp (C₀ + Erdos469.naturalSquareSeries))) := hpair
    _ = C * (N : ℝ) /
        (Real.log (N : ℝ)) ^ (13 / 25 : ℝ) := by
      rw [Real.rpow_neg hlog.le]
      dsimp [C]
      field_simp

/-- For every fixed pair of distinct kernels, the overlap is negligible
relative to the Landau scale along the common geometric endpoints.  The
strict saving is `13/25 - 1/2 = 1/50`. -/
theorem eventually_geometricEndpoint_specialPairCount_le_landauScale_mul
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ K : ℕ in atTop,
      (specialPairCount p q (geometricEndpoint K) : ℝ) ≤
        eta * landauScale (geometricEndpoint K) := by
  obtain ⟨k₀, hk₀, C, hC, hpair⟩ :=
    exists_geometricEndpoint_specialPairCount_upper
      hpq hp4 hq4 hp2 hq2
  have hlogTop : Tendsto
      (fun K : ℕ => Real.log (geometricEndpoint K : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp geometricEndpoint_tendsto_atTop)
  have hpowTop : Tendsto
      (fun K : ℕ =>
        (Real.log (geometricEndpoint K : ℝ)) ^ (1 / 50 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp hlogTop
  have hlarge : ∀ᶠ K : ℕ in atTop,
      C / eta ≤
        (Real.log (geometricEndpoint K : ℝ)) ^ (1 / 50 : ℝ) :=
    (tendsto_atTop.1 hpowTop) (C / eta)
  filter_upwards [hlarge, eventually_ge_atTop k₀,
      eventually_ge_atTop 3] with K hKlarge hK₀ hK3
  let N := geometricEndpoint K
  have hN3 : 3 ≤ N := geometricEndpoint_ge_three hK3
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhalf : 0 < (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hdelta : 0 < (Real.log (N : ℝ)) ^ (1 / 50 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hCeta : C ≤ eta *
      (Real.log (N : ℝ)) ^ (1 / 50 : ℝ) := by
    have := (div_le_iff₀ heta).mp hKlarge
    dsimp [N] at *
    nlinarith
  have hupper := hpair K hK₀
  change (specialPairCount p q N : ℝ) ≤ eta * landauScale N
  calc
    (specialPairCount p q N : ℝ) ≤
        C * (N : ℝ) /
          (Real.log (N : ℝ)) ^ (13 / 25 : ℝ) := hupper
    _ = C * (N : ℝ) /
        ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (Real.log (N : ℝ)) ^ (1 / 50 : ℝ)) := by
      rw [← Real.rpow_add hlog]
      congr 3
      norm_num
    _ ≤ (eta * (Real.log (N : ℝ)) ^ (1 / 50 : ℝ)) *
        (N : ℝ) /
        ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (Real.log (N : ℝ)) ^ (1 / 50 : ℝ)) := by
      gcongr
    _ = eta * landauScale N := by
      rw [landauScale, Real.sqrt_eq_rpow]
      field_simp

/-- Any fixed finite family has total ordered-pair overlap at most one
Landau scale along all sufficiently late geometric endpoints. -/
theorem eventually_geometricEndpoint_specialPairSum_le_landauScale
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3) :
    ∀ᶠ K : ℕ in atTop,
      (∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
          (specialPairCount p q (geometricEndpoint K) : ℝ)) ≤
        landauScale (geometricEndpoint K) := by
  let eta : ℝ := 1 / (((P.card : ℝ) ^ 2) + 1)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hAll : ∀ᶠ K : ℕ in atTop,
      ∀ p ∈ P, ∀ q ∈ P.filter (fun q => q ≠ p),
        (specialPairCount p q (geometricEndpoint K) : ℝ) ≤
          eta * landauScale (geometricEndpoint K) := by
    rw [Finset.eventually_all]
    intro p hp
    rw [Finset.eventually_all]
    intro q hq
    have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
    have hqp : q ≠ p := (Finset.mem_filter.mp hq).2
    have hpprime := (hP p hp).1
    have hqprime := (hP q hqP).1
    have hp4 := (hP p hp).2
    have hq4 := (hP q hqP).2
    have hp2 : p ≠ 2 := by
      intro h
      subst p
      norm_num at hp4
    have hq2 : q ≠ 2 := by
      intro h
      subst q
      norm_num at hq4
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : Fact q.Prime := ⟨hqprime⟩
    exact eventually_geometricEndpoint_specialPairCount_le_landauScale_mul
      ((Nat.coprime_primes hpprime hqprime).2 hqp.symm)
      hp4 hq4 hp2 hq2 heta
  filter_upwards [hAll, eventually_ge_atTop 3] with K hK hK3
  let L := landauScale (geometricEndpoint K)
  have hL : 0 ≤ L := by
    have hN3 : 3 ≤ geometricEndpoint K := geometricEndpoint_ge_three hK3
    have hlog : 0 < Real.log (geometricEndpoint K : ℝ) := by
      exact Real.log_pos (by exact_mod_cast
        (show 1 < geometricEndpoint K by omega))
    dsimp [L, landauScale]
    positivity
  have hsub (p : ℕ) (hp : p ∈ P) :
      (∑ q ∈ P.filter (fun q => q ≠ p), eta * L) ≤
        ∑ q ∈ P, eta * L := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro q _ _
      exact mul_nonneg heta.le hL
  calc
    (∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
        (specialPairCount p q (geometricEndpoint K) : ℝ)) ≤
      ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p), eta * L := by
        exact Finset.sum_le_sum fun p hp =>
          Finset.sum_le_sum fun q hq => hK p hp q hq
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, eta * L := by
      exact Finset.sum_le_sum hsub
    _ = (P.card : ℝ) ^ 2 * eta * L := by
      simp
      ring
    _ ≤ L := by
      have hcard : 0 ≤ (P.card : ℝ) ^ 2 := sq_nonneg _
      have hfrac : (P.card : ℝ) ^ 2 * eta ≤ 1 := by
        dsimp [eta]
        rw [one_div, ← div_eq_mul_inv]
        exact (div_le_one (by linarith)).2 (by linarith)
      nlinarith

/-- Uniform lower bound for the squarefree kernel slice.  This is the exact
half-dimensional beta-sieve statement: the excluded primes are the quadratic
obstructions for `X² + p³Y²`, and the extra factor `p⁻¹` is deliberately much
weaker than the true Euler-product constant. -/
def SpecialSquarefreeKernelLower : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ∀ᶠ N : ℕ in atTop,
        2 * c * (p : ℝ)⁻¹ * landauScale N ≤
          ((specialSquarefreeKernels p N).card : ℝ)

/-- Uniform lower bound for the complete local norm set.  This is the
half-dimensional sieve half of the special Bernays theorem; unlike the
principal-form statement, it involves only quadratic characters modulo `p`
and inert-prime parity. -/
def SpecialLocalNormLower : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ∀ᶠ N : ℕ in atTop,
        2 * c * (p : ℝ)⁻¹ * landauScale N ≤
          ((specialLocalValues p N).card : ℝ)

/-- The beta-sieved squarefree slice supplies the same lower bound for the
full local norm set. -/
theorem specialLocalNormLower_of_squarefreeKernelLower
    (hkernel : SpecialSquarefreeKernelLower) : SpecialLocalNormLower := by
  rcases hkernel with ⟨c, hc, hkernel⟩
  refine ⟨c, hc, ?_⟩
  intro p hp hp4
  filter_upwards [hkernel p hp hp4] with N hN
  exact hN.trans (by
    exact_mod_cast specialSquarefreeKernels_card_le_specialLocalValues_card p N)

/-- Qualitative ring-class mixing in the exact strength needed here: for
each fixed conductor, locally admissible integers missed by the principal
class have density zero on the Bernays scale.  The endpoint threshold may
depend on both `p` and `ε`; no varying-discriminant uniformity is asserted. -/
def SpecialRingClassMixing : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ∀ᶠ N : ℕ in atTop,
        ((specialRingClassExceptions p N).card : ℝ) ≤
          ε * (p : ℝ)⁻¹ * landauScale N

/-- The fixed-discriminant Bernays input needed for the diagonal argument.
Its `p⁻¹` dependence is the very weak specialization of the classical
estimate `C(D) ≫_ε |D|⁻ε` to `D = -4p³`.  No uniformity in the endpoint is
required: the threshold may depend on `p`. -/
def SpecialBernaysLower : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ∀ᶠ N : ℕ in atTop,
        c * (p : ℝ)⁻¹ * landauScale N ≤
          (specialFormCount p N : ℝ)

/-- The local half-dimensional sieve and ring-class mixing together give
the fixed-form lower estimate.  The proof is the exact finite decomposition
of the local set followed by subtraction of its exceptional part. -/
theorem specialBernaysLower_of_localNorm_and_ringClass
    (hlocal : SpecialLocalNormLower)
    (hmix : SpecialRingClassMixing) : SpecialBernaysLower := by
  rcases hlocal with ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro p hp hp4
  have hmiss := hmix c hc p hp hp4
  filter_upwards [hlocal p hp hp4, hmiss] with N hlocalN hmissN
  have hdecomp :
      ((specialRingClassExceptions p N).card : ℝ) +
          (specialFormCount p N : ℝ) =
        ((specialLocalValues p N).card : ℝ) := by
    exact_mod_cast specialRingClassExceptions_card_add_specialFormCount p N
  linarith

/-- A limit-form interface for the remaining fixed-discriminant theorem.
The factor `2` is harmless and makes passage from a limiting Bernays
constant to an eventual lower bound completely explicit.  Unlike
`SpecialBernaysLower`, this records both genuinely separate analytic facts:
existence of the Bernays limit for every form `X² + p³Y²`, and the uniform
lower estimate for its constant. -/
def SpecialBernaysAsymptotic : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ∃ C : ℝ,
        2 * c * (p : ℝ)⁻¹ ≤ C ∧
          Tendsto
            (fun N : ℕ ↦
              (specialFormCount p N : ℝ) / landauScale N)
            atTop (nhds C)

/-- The asymptotic Bernays statement, together with its uniform constant
bound, implies the exact eventual inequality consumed by the diagonal
argument.  This theorem discharges all limit manipulation; the unresolved
content is now solely the number-theoretic proof of
`SpecialBernaysAsymptotic`. -/
theorem specialBernaysLower_of_asymptotic
    (h : SpecialBernaysAsymptotic) : SpecialBernaysLower := by
  rcases h with ⟨c, hc, hforms⟩
  refine ⟨c, hc, ?_⟩
  intro p hp hp4
  obtain ⟨C, hC, hlimit⟩ := hforms p hp hp4
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcp : 0 < c * (p : ℝ)⁻¹ :=
    mul_pos hc (inv_pos.mpr hpR)
  have hthreshold : c * (p : ℝ)⁻¹ < C := by
    calc
      c * (p : ℝ)⁻¹ < 2 * c * (p : ℝ)⁻¹ := by nlinarith
      _ ≤ C := hC
  have hratio : ∀ᶠ N : ℕ in atTop,
      c * (p : ℝ)⁻¹ <
        (specialFormCount p N : ℝ) / landauScale N :=
    hlimit.eventually (Ioi_mem_nhds hthreshold)
  filter_upwards [hratio, eventually_ge_atTop 3] with N hratioN hN
  have hNone : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < landauScale N := by
    dsimp [landauScale]
    exact div_pos (by positivity) (Real.sqrt_pos.2 (Real.log_pos hNone))
  exact (le_of_lt hratioN |> (le_div_iff₀ hscale).mp)

/-- A fixed finite prime family inherits the sum of the individual Bernays
lower bounds along the common geometric endpoints. -/
theorem eventually_geometricEndpoint_specialSingleSum_lower
    {c : ℝ}
    (hBernays : ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ∀ᶠ N : ℕ in atTop,
        c * (p : ℝ)⁻¹ * landauScale N ≤
          (specialFormCount p N : ℝ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3) :
    ∀ᶠ K : ℕ in atTop,
      c * (∑ p ∈ P, (p : ℝ)⁻¹) *
          landauScale (geometricEndpoint K) ≤
        ∑ p ∈ P,
          (specialFormCount p (geometricEndpoint K) : ℝ) := by
  have hAll : ∀ᶠ K : ℕ in atTop, ∀ p ∈ P,
      c * (p : ℝ)⁻¹ * landauScale (geometricEndpoint K) ≤
        (specialFormCount p (geometricEndpoint K) : ℝ) := by
    rw [Finset.eventually_all]
    intro p hp
    exact geometricEndpoint_tendsto_atTop.eventually
      (hBernays p (hP p hp).1 (hP p hp).2)
  filter_upwards [hAll] with K hK
  calc
    c * (∑ p ∈ P, (p : ℝ)⁻¹) *
          landauScale (geometricEndpoint K) =
        ∑ p ∈ P,
          c * (p : ℝ)⁻¹ * landauScale (geometricEndpoint K) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ p ∈ P,
        (specialFormCount p (geometricEndpoint K) : ℝ) :=
      Finset.sum_le_sum hK

/-- The complete diagonal and Bonferroni deduction from fixed-form Bernays
lower bounds.  Pair estimates need only be pointwise in each fixed pair,
since a finite family is chosen before the endpoint. -/
theorem not_erdosConjecture_of_specialBernaysLower
    (hBernays : SpecialBernaysLower) : ¬ ErdosConjecture := by
  rintro ⟨a, ha, haLimit⟩
  rcases hBernays with ⟨c, hc, hsingleForm⟩
  obtain ⟨P, hP, hmass⟩ :=
    exists_threeModFourPrimeFamily_reciprocal_ge ((a + 3) / c)
  have hsingle :=
    eventually_geometricEndpoint_specialSingleSum_lower
      hsingleForm P hP
  have hpair :=
    eventually_geometricEndpoint_specialPairSum_le_landauScale P hP
  have hlimit : ∀ᶠ K : ℕ in atTop,
      normalizedCount (geometricEndpoint K) < a + 1 :=
    geometricEndpoint_tendsto_atTop.eventually
      (haLimit.eventually (Iio_mem_nhds (lt_add_one a)))
  obtain ⟨K, ⟨⟨⟨hsingleK, hpairK⟩, hlimitK⟩, hK3⟩⟩ :=
    (((hsingle.and hpair).and hlimit).and
      (eventually_ge_atTop (α := ℕ) 3)).exists
  let N := geometricEndpoint K
  let L := landauScale N
  have hN3 : 3 ≤ N := geometricEndpoint_ge_three hK3
  have hL : 0 < L := by
    have hNpos : (0 : ℝ) < N := by positivity
    have hlog : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    dsimp [L, landauScale]
    positivity
  have hcoefficient : a + 3 ≤
      c * (∑ p ∈ P, (p : ℝ)⁻¹) := by
    calc
      a + 3 = c * ((a + 3) / c) := by
        field_simp [hc.ne']
      _ ≤ c * (∑ p ∈ P, (p : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hmass hc.le
  have hbonf := specialFamily_bonferroni_lower_bound P N
    (fun p hp => (hP p hp).1)
  have hAlower : (a + 2) * L ≤ (A N : ℝ) := by
    change c * (∑ p ∈ P, (p : ℝ)⁻¹) * L ≤ _ at hsingleK
    change (∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
      (specialPairCount p q N : ℝ)) ≤ L at hpairK
    nlinarith
  have hAupper : (A N : ℝ) < (a + 1) * L := by
    change normalizedCount N < a + 1 at hlimitK
    rw [normalizedCount] at hlimitK
    exact (div_lt_iff₀ hL).mp hlimitK
  nlinarith

/-! ## Exact analytic interface for Blomer's finite-family argument -/

/-- After summing over the optimizing family of forms, this is the exponent
of the ordered-pair Bonferroni error. -/
noncomputable def blomerPairFamilyExponent : ℝ :=
  middleRepresentationExponent 2 blomerKappa - 2 * blomerBeta

theorem blomerSingleFamilyExponent_eq_alpha :
    middleRepresentationExponent 1 blomerKappa - blomerBeta =
      blomerGranvilleAlpha := by
  rw [middleRepresentationExponent_one_blomerKappa]
  ring

theorem blomerGranvilleAlpha_lt_pairFamilyExponent :
    blomerGranvilleAlpha < blomerPairFamilyExponent := by
  rw [← blomerSingleFamilyExponent_eq_alpha]
  exact pairExponent_after_family_lt_singleExponent

/-- The two concrete aggregate estimates used after choosing Blomer's
finite prime family.  This proposition exposes the remaining analytic input
at the level immediately before the already-proved Bonferroni inequality:
the first clause is the sum of the one-form lower bounds and the second is
the total ordered-pair upper bound. -/
def BlomerBonferroniBounds : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ P : Finset ℕ,
          (∀ p ∈ P, p.Prime) ∧
          c * (N : ℝ) /
              (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) ≤
            ∑ p ∈ P, (specialFormCount p N : ℝ) ∧
          (∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
              (specialPairCount p q N : ℝ)) ≤
            C * (N : ℝ) /
              (Real.log (N : ℝ)) ^ (blomerPairFamilyExponent - eta)

/-- The checked final assembly of Blomer's lower bound from its two
finite-family estimates.  The strict exponent gap absorbs the complete
ordered-pair error. -/
theorem blomerLowerBound_of_bonferroniBounds
    (h : BlomerBonferroniBounds) : BlomerLowerBound := by
  intro epsilon hepsilon
  let gap : ℝ := blomerPairFamilyExponent - blomerGranvilleAlpha
  have hgap : 0 < gap :=
    sub_pos.mpr blomerGranvilleAlpha_lt_pairFamilyExponent
  let eta : ℝ := min (epsilon / 2) (gap / 4)
  have heta : 0 < eta :=
    lt_min (half_pos hepsilon) (by dsimp [gap]; positivity)
  have heta_eps : eta ≤ epsilon := by
    exact (min_le_left _ _).trans (by linarith)
  have heta_gap : 2 * eta < gap := by
    have hle := min_le_right (epsilon / 2) (gap / 4)
    dsimp [eta]
    linarith
  obtain ⟨c, C, hc, hC, hbounds⟩ := h eta heta
  refine ⟨c / 2, half_pos hc, ?_⟩
  let delta : ℝ :=
    (blomerPairFamilyExponent - eta) -
      (blomerGranvilleAlpha + eta)
  have hdelta : 0 < delta := by
    dsimp [delta, gap] at *
    linarith
  have htendsto : Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpower : ∀ᶠ N : ℕ in atTop,
      2 * C / c ≤ (Real.log (N : ℝ)) ^ delta :=
    (tendsto_atTop.1 htendsto) (2 * C / c)
  filter_upwards [hbounds, hpower, eventually_ge_atTop 3] with
      N hN hpow hN3
  rcases hN with ⟨P, hPprime, hsingle, hpair⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogone : 1 < Real.log (N : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hNpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hN3)
  have hpowmul : 2 * C ≤ c * (Real.log (N : ℝ)) ^ delta := by
    have := (div_le_iff₀ hc).mp hpow
    nlinarith
  have hpairSmall :
      C * (N : ℝ) /
          (Real.log (N : ℝ)) ^ (blomerPairFamilyExponent - eta) ≤
        (c / 2) * (N : ℝ) /
          (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) := by
    rw [show blomerPairFamilyExponent - eta =
        (blomerGranvilleAlpha + eta) + delta by
          dsimp [delta]; ring,
      Real.rpow_add hlog]
    have hpa : 0 <
        (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) :=
      Real.rpow_pos_of_pos hlog _
    have hpd : 0 < (Real.log (N : ℝ)) ^ delta :=
      Real.rpow_pos_of_pos hlog _
    calc
      C * (N : ℝ) /
            ((Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) *
              (Real.log (N : ℝ)) ^ delta) ≤
          (c * (Real.log (N : ℝ)) ^ delta / 2) * (N : ℝ) /
            ((Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) *
              (Real.log (N : ℝ)) ^ delta) := by
        gcongr
        nlinarith
      _ = (c / 2) * (N : ℝ) /
            (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) := by
        field_simp
  have hbonf := specialFamily_bonferroni_lower_bound P N hPprime
  have hmainEta :
      (c / 2) * (N : ℝ) /
          (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) ≤
        (A N : ℝ) := by
    have hsplit :
        c * (N : ℝ) /
            (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) =
          2 * ((c / 2) * (N : ℝ) /
            (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta)) := by
      ring
    rw [hsplit] at hsingle
    linarith
  have hexp : blomerGranvilleAlpha + eta ≤
      blomerGranvilleAlpha + epsilon := by linarith
  have hdenom :
      (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + eta) ≤
        (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hlogone.le hexp
  exact (div_le_div_of_nonneg_left
      (mul_nonneg (half_pos hc).le hNpos.le)
      (Real.rpow_pos_of_pos hlog _)
      hdenom).trans hmainEta

lemma eventually_landauScale_pos :
    ∀ᶠ N : ℕ in atTop, 0 < landauScale N := by
  refine (eventually_ge_atTop 3).mono ?_
  intro N hN
  have hNposNat : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hNoneNat : 1 < N := lt_of_lt_of_le (by decide : 1 < 3) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNposNat
  have hNone : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hNoneNat
  exact div_pos hNpos (Real.sqrt_pos.2 (Real.log_pos hNone))

/-- A divergent lower factor forces the normalized count to diverge. -/
theorem normalizedCount_tendsto_atTop_of_divergentLowerBound
    (hlowerBound : DivergentLowerBound) :
    Tendsto normalizedCount atTop atTop := by
  rcases hlowerBound with ⟨g, hg, hlower⟩
  apply tendsto_atTop_mono' atTop (hlower.and eventually_landauScale_pos |>.mono ?_) hg
  intro N hN
  exact (le_div_iff₀ hN.2).2 hN.1

/-- The completely formal final analytic step: a divergent lower factor is
incompatible with convergence of the normalized count to any real number, and
hence in particular with Erdős's proposed positive constant. -/
theorem not_erdosConjecture_of_divergentLowerBound
    (hlowerBound : DivergentLowerBound) :
    ¬ ErdosConjecture := by
  intro hconj
  rcases hconj with ⟨c, _hc, hc⟩
  have htop : Tendsto normalizedCount atTop atTop :=
    normalizedCount_tendsto_atTop_of_divergentLowerBound hlowerBound
  have hUpper : ∀ᶠ N : ℕ in atTop, normalizedCount N < c + 1 :=
    hc.eventually (Iio_mem_nhds (lt_add_one c))
  have hLower : ∀ᶠ N : ℕ in atTop, c + 1 ≤ normalizedCount N :=
    (tendsto_atTop.1 htop) (c + 1)
  have hFalse : ∀ᶠ _N : ℕ in atTop, False :=
    (hUpper.and hLower).mono fun _N h => (not_lt_of_ge h.2) h.1
  rcases hFalse.exists with ⟨_N, hN⟩
  exact hN

/-- The published Blomer--Granville exponent is strictly below `1 / 2`. -/
theorem blomerGranvilleAlpha_lt_half :
    blomerGranvilleAlpha < (1 : ℝ) / 2 := by
  have hpow : (2 : ℝ) ^ (-1 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  rw [Real.rpow_neg_one] at hpow
  norm_num [blomerGranvilleAlpha]
  linarith

/-- The lower half of Blomer's estimate supplies a factor over the Landau
scale which tends to infinity. -/
theorem divergentLowerBound_of_blomerLowerBound
    (hBlomer : BlomerLowerBound) : DivergentLowerBound := by
  let ε : ℝ := ((1 : ℝ) / 2 - blomerGranvilleAlpha) / 2
  have hgap : 0 < (1 : ℝ) / 2 - blomerGranvilleAlpha :=
    sub_pos.mpr blomerGranvilleAlpha_lt_half
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases hBlomer ε hε with ⟨C, hC, hbound⟩
  let δ : ℝ := (1 : ℝ) / 2 - (blomerGranvilleAlpha + ε)
  have hδ : 0 < δ := by
    dsimp [δ, ε]
    linarith
  refine ⟨fun N : ℕ => C * (Real.log (N : ℝ)) ^ δ, ?_, ?_⟩
  · exact Tendsto.const_mul_atTop hC <|
      (tendsto_rpow_atTop hδ).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  · filter_upwards [hbound, eventually_ge_atTop 3] with N hN hN3
    have hNoneNat : 1 < N := lt_of_lt_of_le (by decide : 1 < 3) hN3
    have hNone : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hNoneNat
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNone
    calc
      C * (Real.log (N : ℝ)) ^ δ * landauScale N =
          C * (N : ℝ) /
            (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + ε) := by
        rw [landauScale]
        calc
          C * (Real.log (N : ℝ)) ^ δ *
                ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) =
              C * (N : ℝ) *
                ((Real.log (N : ℝ)) ^ δ /
                  (Real.log (N : ℝ)) ^ ((1 : ℝ) / 2)) := by
            rw [Real.sqrt_eq_rpow, div_eq_mul_inv]
            ring
          _ = C * (N : ℝ) *
                (Real.log (N : ℝ)) ^ (δ - (1 : ℝ) / 2) := by
            congr 2
            exact (Real.rpow_sub hlog δ ((1 : ℝ) / 2)).symm
          _ = C * (N : ℝ) *
                (Real.log (N : ℝ)) ^ (-(blomerGranvilleAlpha + ε)) := by
            congr 2
            dsimp [δ]
            ring
          _ = C * (N : ℝ) *
                ((Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + ε))⁻¹ := by
            rw [Real.rpow_neg hlog.le]
          _ = C * (N : ℝ) /
                (Real.log (N : ℝ)) ^ (blomerGranvilleAlpha + ε) := by
            rw [div_eq_mul_inv]
      _ ≤ (A N : ℝ) := hN

/-- The exact elementary deduction of the negative answer from the lower half
of Blomer's published estimate. -/
theorem not_erdosConjecture_of_blomerLowerBound
    (hBlomer : BlomerLowerBound) : ¬ ErdosConjecture :=
  not_erdosConjecture_of_divergentLowerBound
    (divergentLowerBound_of_blomerLowerBound hBlomer)

end

end Erdos1081
