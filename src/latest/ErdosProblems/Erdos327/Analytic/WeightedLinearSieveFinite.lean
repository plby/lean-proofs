import ErdosProblems.Erdos327.Analytic.Bonferroni
import ErdosProblems.Erdos327.Analytic.PeriodicLattice
import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveLocal
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.ZMod.QuotientRing

/-!
# Finite weighted three-linear-form sieve

This file combines three entirely finite ingredients:

* the exact one-prime centered and cross weight sums;
* the Chinese remainder theorem for a finite set of distinct primes;
* the periodic rectangular-box estimate and finite Bonferroni inequality.

There are no limiting assertions in this file.  In particular, the
boundary term remains explicit.  The box in the final statements is
exactly `X ≤ u < 2X`, `1 ≤ v ≤ 8X`.
-/

namespace Erdos327.Analytic

open scoped BigOperators

open Finset

variable {ι : Type*}

/-- The squarefree modulus formed from a finite set of primes.  The
subtype formulation makes each divisibility map into the product
canonical. -/
def primeModulus (P : Finset ℕ) : ℕ :=
  ∏ p : P, (p : ℕ)

/-- Every member of `P` divides `primeModulus P`. -/
theorem prime_dvd_primeModulus (P : Finset ℕ) (p : P) :
    (p : ℕ) ∣ primeModulus P := by
  exact Finset.dvd_prod_of_mem (fun q : P ↦ (q : ℕ)) (mem_univ p)

/-- A product of primes is positive. -/
theorem primeModulus_pos
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    0 < primeModulus P := by
  unfold primeModulus
  exact Finset.prod_pos fun p _ ↦
    (hprime p p.property).pos

/-- Distinct members of a finset of primes are pairwise coprime. -/
theorem primeModulus_pairwise_coprime
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Pairwise (Function.onFun Nat.Coprime fun p : P ↦ (p : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes
    (hprime p p.property) (hprime q q.property)).2
  intro hpqval
  exact hpq (Subtype.ext hpqval)

/-- Rebracket a pair of dependent functions as a dependent function
of pairs. -/
def piPairEquiv {κ : Type*} (A B : κ → Type*) :
    ((∀ i, A i) × (∀ i, B i)) ≃ (∀ i, A i × B i) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i ↦ (z i).1, fun i ↦ (z i).2)
  left_inv z := by
    apply Prod.ext <;> funext i <;> rfl
  right_inv z := by
    funext i
    exact Prod.ext rfl rfl

/-- Simultaneous CRT for two residue coordinates and a finite set of
distinct primes. -/
noncomputable def primePairCRT
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (ZMod (primeModulus P) × ZMod (primeModulus P)) ≃
      (∀ p : P, ZMod p × ZMod p) :=
  (Equiv.prodCongr
      (ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
        (primeModulus_pairwise_coprime P hprime)).toEquiv
      (ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
        (primeModulus_pairwise_coprime P hprime)).toEquiv).trans
    (piPairEquiv (fun p : P ↦ ZMod p) (fun p : P ↦ ZMod p))

@[simp] theorem primePairCRT_apply
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) (p : P) :
    primePairCRT P hprime r p =
      (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
        ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2) := by
  unfold primePairCRT piPairEquiv
  apply Prod.ext
  · exact ZMod.prodEquivPi_apply
      (fun q : P ↦ (q : ℕ))
      (primeModulus_pairwise_coprime P hprime) r.1 p
  · exact ZMod.prodEquivPi_apply
      (fun q : P ↦ (q : ℕ))
      (primeModulus_pairwise_coprime P hprime) r.2 p

/-- Product of arbitrary local residue-pair weights, transported to
the squarefree composite modulus. -/
noncomputable def finiteLocalProduct
    (P : Finset ℕ) (w : ∀ p : ℕ, ZMod p × ZMod p → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) : ℝ :=
  ∏ p : P,
    w p
      (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
        ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2)

theorem finiteLocalProduct_eq_crt
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (w : ∀ p : ℕ, ZMod p × ZMod p → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) :
    finiteLocalProduct P w r =
      ∏ p : P, w p (primePairCRT P hprime r p) := by
  classical
  apply Finset.prod_congr rfl
  intro p _
  rw [primePairCRT_apply]

/-- Exact CRT factorization of the total mass of a product of local
weights. -/
theorem sum_finiteLocalProduct
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (w : ∀ p : ℕ, ZMod p × ZMod p → ℝ) :
    (∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        finiteLocalProduct P w r) =
      ∏ p : P, ∑ z : ZMod p × ZMod p, w p z := by
  classical
  calc
    (∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        finiteLocalProduct P w r) =
        ∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
          ∏ p : P, w p (primePairCRT P hprime r p) := by
            apply Finset.sum_congr rfl
            intro r _
            exact finiteLocalProduct_eq_crt P hprime w r
    _ = ∑ z : (∀ p : P, ZMod p × ZMod p),
          ∏ p : P, w p (z p) :=
      (primePairCRT P hprime).sum_comp
        (fun z ↦ ∏ p : P, w p (z p))
    _ = ∏ p : P, ∑ z : ZMod p × ZMod p, w p z :=
      (Fintype.prod_sum (fun p : P ↦ w p)).symm

/-- The centered local factor at `p`, evaluated by reducing a residue
pair modulo `p`. -/
noncomputable def centeredLocalAt
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) (p : P) : ℝ :=
  centeredLocalWeight (qU p) (qV p) (qSum p)
    (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
      ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2)

/-- The cross local factor at `p`, evaluated by reducing a residue pair
modulo `p`. -/
noncomputable def crossLocalAt
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) (p : P) : ℝ :=
  crossLocalWeight (qU p) (qW p) (qLinear p)
    (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
      ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2)

/-- Product of the centered local weights over `P`. -/
noncomputable def centeredFiniteWeight
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) : ℝ :=
  ∏ p : P, centeredLocalAt P qU qV qSum r p

/-- Product of the cross local weights over `P`. -/
noncomputable def crossFiniteWeight
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) : ℝ :=
  ∏ p : P, crossLocalAt P qU qW qLinear r p

theorem centeredFiniteWeight_eq_finiteLocalProduct
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) :
    centeredFiniteWeight P qU qV qSum r =
      finiteLocalProduct P
        (fun p ↦ centeredLocalWeight (qU p) (qV p) (qSum p)) r := by
  rfl

theorem crossFiniteWeight_eq_finiteLocalProduct
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) :
    crossFiniteWeight P qU qW qLinear r =
      finiteLocalProduct P
        (fun p ↦ crossLocalWeight (qU p) (qW p) (qLinear p)) r := by
  rfl

/-- Exact composite-modulus mass for the centered weights. -/
theorem sum_centeredFiniteWeight
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (qU qV qSum : ℕ → ℝ) :
    (∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        centeredFiniteWeight P qU qV qSum r) =
      ∏ p : P,
        ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
          ((p : ℝ) - 1) * (qU p + qV p + qSum p) +
          qU p * qV p * qSum p) := by
  rw [show (∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
      centeredFiniteWeight P qU qV qSum r) =
      ∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        finiteLocalProduct P
          (fun p ↦ centeredLocalWeight (qU p) (qV p) (qSum p)) r by
      apply Finset.sum_congr rfl
      intro r _
      rfl]
  rw [sum_finiteLocalProduct P hprime]
  apply Finset.prod_congr rfl
  intro p _
  exact sum_centeredLocalWeight p (qU p) (qV p) (qSum p)

/-- Exact composite-modulus mass for the cross weights. -/
theorem sum_crossFiniteWeight
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hodd : ∀ p ∈ P, p ≠ 2)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (qU qW qLinear : ℕ → ℝ) :
    (∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        crossFiniteWeight P qU qW qLinear r) =
      ∏ p : P,
        ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
          ((p : ℝ) - 1) * (qU p + qW p + qLinear p) +
          qU p * qW p * qLinear p) := by
  rw [show (∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
      crossFiniteWeight P qU qW qLinear r) =
      ∑ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        finiteLocalProduct P
          (fun p ↦ crossLocalWeight (qU p) (qW p) (qLinear p)) r by
      apply Finset.sum_congr rfl
      intro r _
      rfl]
  rw [sum_finiteLocalProduct P hprime]
  apply Finset.prod_congr rfl
  intro p _
  exact sum_crossLocalWeight p (hprime p p.property)
    (hodd p p.property) (qU p) (qW p) (qLinear p)

private theorem threeIndicatorProduct_nonneg_le_one
    (P₁ P₂ P₃ : Prop) [Decidable P₁] [Decidable P₂] [Decidable P₃]
    (q₁ q₂ q₃ : ℝ)
    (hq₁0 : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1)
    (hq₂0 : 0 ≤ q₂) (hq₂1 : q₂ ≤ 1)
    (hq₃0 : 0 ≤ q₃) (hq₃1 : q₃ ≤ 1) :
    0 ≤ (if P₁ then q₁ else 1) *
        (if P₂ then q₂ else 1) *
        (if P₃ then q₃ else 1) ∧
      (if P₁ then q₁ else 1) *
        (if P₂ then q₂ else 1) *
        (if P₃ then q₃ else 1) ≤ 1 := by
  let a : ℝ := if P₁ then q₁ else 1
  let b : ℝ := if P₂ then q₂ else 1
  let c : ℝ := if P₃ then q₃ else 1
  have ha0 : 0 ≤ a := by
    dsimp [a]
    split <;> simp_all
  have ha1 : a ≤ 1 := by
    dsimp [a]
    split <;> simp_all
  have hb0 : 0 ≤ b := by
    dsimp [b]
    split <;> simp_all
  have hb1 : b ≤ 1 := by
    dsimp [b]
    split <;> simp_all
  have hc0 : 0 ≤ c := by
    dsimp [c]
    split <;> simp_all
  have hc1 : c ≤ 1 := by
    dsimp [c]
    split <;> simp_all
  change 0 ≤ a * b * c ∧ a * b * c ≤ 1
  exact ⟨mul_nonneg (mul_nonneg ha0 hb0) hc0,
    mul_le_one₀ (mul_le_one₀ ha1 hb0 hb1) hc0 hc1⟩

theorem centeredLocalWeight_nonneg_le_one
    {p : ℕ} (qU qV qSum : ℝ)
    (hqU0 : 0 ≤ qU) (hqU1 : qU ≤ 1)
    (hqV0 : 0 ≤ qV) (hqV1 : qV ≤ 1)
    (hqSum0 : 0 ≤ qSum) (hqSum1 : qSum ≤ 1)
    (r : ZMod p × ZMod p) :
    0 ≤ centeredLocalWeight qU qV qSum r ∧
      centeredLocalWeight qU qV qSum r ≤ 1 := by
  exact threeIndicatorProduct_nonneg_le_one
    (r.1 = 0) (r.2 = 0) (r.1 + r.2 = 0)
    qU qV qSum hqU0 hqU1 hqV0 hqV1 hqSum0 hqSum1

theorem crossLocalWeight_nonneg_le_one
    {p : ℕ} (qU qW qLinear : ℝ)
    (hqU0 : 0 ≤ qU) (hqU1 : qU ≤ 1)
    (hqW0 : 0 ≤ qW) (hqW1 : qW ≤ 1)
    (hqLinear0 : 0 ≤ qLinear) (hqLinear1 : qLinear ≤ 1)
    (r : ZMod p × ZMod p) :
    0 ≤ crossLocalWeight qU qW qLinear r ∧
      crossLocalWeight qU qW qLinear r ≤ 1 := by
  exact threeIndicatorProduct_nonneg_le_one
    (r.1 = 0) (r.2 = 0) (2 * r.1 + r.2 = 0)
    qU qW qLinear hqU0 hqU1 hqW0 hqW1
    hqLinear0 hqLinear1

/-- The loss of the centered factor at one prime. -/
noncomputable def centeredPrimeLoss
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P))
    (p : P) : ℝ :=
  1 - centeredLocalAt P qU qV qSum r p

/-- The loss of the cross factor at one prime. -/
noncomputable def crossPrimeLoss
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P))
    (p : P) : ℝ :=
  1 - crossLocalAt P qU qW qLinear r p

/-- Pointwise even Bonferroni upper bound for a product of centered
local weights. -/
theorem centeredFiniteWeight_le_bonferroni
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqV0 : ∀ p ∈ P, 0 ≤ qV p) (hqV1 : ∀ p ∈ P, qV p ≤ 1)
    (hqSum0 : ∀ p ∈ P, 0 ≤ qSum p)
    (hqSum1 : ∀ p ∈ P, qSum p ≤ 1)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) (R : ℕ) :
    centeredFiniteWeight P qU qV qSum r ≤
      bonferroniTruncation univ
        (centeredPrimeLoss P qU qV qSum r) (2 * R + 1) := by
  have hlocal (p : P) :=
    centeredLocalWeight_nonneg_le_one
      (qU p) (qV p) (qSum p)
      (hqU0 p p.property) (hqU1 p p.property)
      (hqV0 p p.property) (hqV1 p p.property)
      (hqSum0 p p.property) (hqSum1 p p.property)
      (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
        ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2)
  have hloss0 :
      ∀ p ∈ (univ : Finset P),
        0 ≤ centeredPrimeLoss P qU qV qSum r p :=
    fun p _ ↦ sub_nonneg.mpr (hlocal p).2
  have hloss1 :
      ∀ p ∈ (univ : Finset P),
        centeredPrimeLoss P qU qV qSum r p ≤ 1 :=
    fun p _ ↦ sub_le_self _ (hlocal p).1
  simpa [centeredFiniteWeight, centeredPrimeLoss] using
    bonferroni_even_upper (univ : Finset P)
      (centeredPrimeLoss P qU qV qSum r) hloss0 hloss1 R

/-- Pointwise even Bonferroni upper bound for a product of cross local
weights. -/
theorem crossFiniteWeight_le_bonferroni
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqW0 : ∀ p ∈ P, 0 ≤ qW p) (hqW1 : ∀ p ∈ P, qW p ≤ 1)
    (hqLinear0 : ∀ p ∈ P, 0 ≤ qLinear p)
    (hqLinear1 : ∀ p ∈ P, qLinear p ≤ 1)
    (r : ZMod (primeModulus P) × ZMod (primeModulus P)) (R : ℕ) :
    crossFiniteWeight P qU qW qLinear r ≤
      bonferroniTruncation univ
        (crossPrimeLoss P qU qW qLinear r) (2 * R + 1) := by
  have hlocal (p : P) :=
    crossLocalWeight_nonneg_le_one
      (qU p) (qW p) (qLinear p)
      (hqU0 p p.property) (hqU1 p p.property)
      (hqW0 p p.property) (hqW1 p p.property)
      (hqLinear0 p p.property) (hqLinear1 p p.property)
      (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
        ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2)
  have hloss0 :
      ∀ p ∈ (univ : Finset P),
        0 ≤ crossPrimeLoss P qU qW qLinear r p :=
    fun p _ ↦ sub_nonneg.mpr (hlocal p).2
  have hloss1 :
      ∀ p ∈ (univ : Finset P),
        crossPrimeLoss P qU qW qLinear r p ≤ 1 :=
    fun p _ ↦ sub_le_self _ (hlocal p).1
  simpa [crossFiniteWeight, crossPrimeLoss] using
    bonferroni_even_upper (univ : Finset P)
      (crossPrimeLoss P qU qW qLinear r) hloss0 hloss1 R

/-- Sum the pointwise centered Bonferroni bound over the exact
three-line box. -/
theorem threeLine_centeredFiniteWeight_le_bonferroniSum
    (P : Finset ℕ) [NeZero (primeModulus P)]
    (qU qV qSum : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqV0 : ∀ p ∈ P, 0 ≤ qV p) (hqV1 : ∀ p ∈ P, qV p ≤ 1)
    (hqSum0 : ∀ p ∈ P, 0 ≤ qSum p)
    (hqSum1 : ∀ p ∈ P, qSum p ≤ 1)
    (X R : ℕ) :
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (centeredFiniteWeight P qU qV qSum) ≤
      periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (fun r ↦ bonferroniTruncation univ
          (centeredPrimeLoss P qU qV qSum r) (2 * R + 1)) := by
  unfold periodicBoxSum
  apply sum_le_sum
  intro z _
  exact centeredFiniteWeight_le_bonferroni
    P qU qV qSum hqU0 hqU1 hqV0 hqV1 hqSum0 hqSum1
    ((z.1 : ZMod (primeModulus P)), (z.2 : ZMod (primeModulus P))) R

/-- Sum the pointwise cross Bonferroni bound over the exact three-line
box. -/
theorem threeLine_crossFiniteWeight_le_bonferroniSum
    (P : Finset ℕ) [NeZero (primeModulus P)]
    (qU qW qLinear : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqW0 : ∀ p ∈ P, 0 ≤ qW p) (hqW1 : ∀ p ∈ P, qW p ≤ 1)
    (hqLinear0 : ∀ p ∈ P, 0 ≤ qLinear p)
    (hqLinear1 : ∀ p ∈ P, qLinear p ≤ 1)
    (X R : ℕ) :
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (crossFiniteWeight P qU qW qLinear) ≤
      periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (fun r ↦ bonferroniTruncation univ
          (crossPrimeLoss P qU qW qLinear r) (2 * R + 1)) := by
  unfold periodicBoxSum
  apply sum_le_sum
  intro z _
  exact crossFiniteWeight_le_bonferroni
    P qU qW qLinear hqU0 hqU1 hqW0 hqW1
    hqLinear0 hqLinear1
    ((z.1 : ZMod (primeModulus P)), (z.2 : ZMod (primeModulus P))) R

/-- Periodic-box bound for an arbitrary product of local weights.  The
CRT makes its main term an exact product of one-prime masses; the
support size in the boundary term is retained exactly. -/
theorem threeLine_finiteLocalProduct_le_exactSupport
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (w : ∀ p : ℕ, ZMod p × ZMod p → ℝ)
    (hw0 : ∀ (p : P) z, 0 ≤ w p z)
    (hw1 : ∀ (p : P) z, w p z ≤ 1) (X : ℕ) :
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (finiteLocalProduct P w) ≤
      ((X : ℝ) / primeModulus P) *
          ((8 * X : ℕ) : ℝ) / primeModulus P *
          (∏ p : P, ∑ z : ZMod p × ZMod p, w p z) +
        (9 * (X : ℝ) / primeModulus P + 1) *
          (residueWeightSupport (primeModulus P)
            (finiteLocalProduct P w)).card := by
  have hproduct0 :
      ∀ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        0 ≤ finiteLocalProduct P w r := by
    intro r
    unfold finiteLocalProduct
    exact Finset.prod_nonneg fun p _ ↦
      hw0 p
        (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
          ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2)
  have hproduct1 :
      ∀ r : ZMod (primeModulus P) × ZMod (primeModulus P),
        finiteLocalProduct P w r ≤ 1 := by
    intro r
    unfold finiteLocalProduct
    exact Finset.prod_le_one
      (fun p _ ↦
        hw0 p
          (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
            ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2))
      (fun p _ ↦
        hw1 p
          (ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.1,
            ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p) r.2))
  calc
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (finiteLocalProduct P w) ≤
      ((X : ℝ) / primeModulus P) *
          ((8 * X : ℕ) : ℝ) / primeModulus P *
          (∑ r, finiteLocalProduct P w r) +
        (9 * (X : ℝ) / primeModulus P + 1) *
          (residueWeightSupport (primeModulus P)
            (finiteLocalProduct P w)).card :=
      threeLine_periodicBoxSum_le
        (primeModulus_pos P hprime) X
        (finiteLocalProduct P w) hproduct0 hproduct1
    _ = _ := by
      rw [sum_finiteLocalProduct P hprime w]

/-- The same bound with the support size replaced by the elementary
upper bound `D²`, where `D = primeModulus P`. -/
theorem threeLine_finiteLocalProduct_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (w : ∀ p : ℕ, ZMod p × ZMod p → ℝ)
    (hw0 : ∀ (p : P) z, 0 ≤ w p z)
    (hw1 : ∀ (p : P) z, w p z ≤ 1) (X : ℕ) :
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (finiteLocalProduct P w) ≤
      ((X : ℝ) / primeModulus P) *
          ((8 * X : ℕ) : ℝ) / primeModulus P *
          (∏ p : P, ∑ z : ZMod p × ZMod p, w p z) +
        (9 * (X : ℝ) / primeModulus P + 1) *
          (primeModulus P : ℝ) ^ 2 := by
  have hbase :=
    threeLine_finiteLocalProduct_le_exactSupport
      P hprime w hw0 hw1 X
  have hcardNat :
      (residueWeightSupport (primeModulus P)
        (finiteLocalProduct P w)).card ≤
          primeModulus P * primeModulus P := by
    calc
      (residueWeightSupport (primeModulus P)
          (finiteLocalProduct P w)).card ≤
          (univ : Finset
            (ZMod (primeModulus P) × ZMod (primeModulus P))).card :=
        card_le_card (filter_subset _ _)
      _ = primeModulus P * primeModulus P := by
        simp [ZMod.card]
  have hcard :
      ((residueWeightSupport (primeModulus P)
        (finiteLocalProduct P w)).card : ℝ) ≤
          (primeModulus P : ℝ) ^ 2 := by
    calc
      ((residueWeightSupport (primeModulus P)
          (finiteLocalProduct P w)).card : ℝ) ≤
          ((primeModulus P * primeModulus P : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ = (primeModulus P : ℝ) ^ 2 := by
        push_cast
        ring
  have hmodulusReal : 0 < (primeModulus P : ℝ) := by
    exact_mod_cast primeModulus_pos P hprime
  have hcoefficient :
      0 ≤ 9 * (X : ℝ) / primeModulus P + 1 := by
    positivity
  exact hbase.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hcard hcoefficient) _)

/-- Fully explicit centered finite-sieve estimate in the
`X ≤ u < 2X`, `1 ≤ v ≤ 8X` box. -/
theorem threeLine_centeredFiniteWeight_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (qU qV qSum : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqV0 : ∀ p ∈ P, 0 ≤ qV p) (hqV1 : ∀ p ∈ P, qV p ≤ 1)
    (hqSum0 : ∀ p ∈ P, 0 ≤ qSum p)
    (hqSum1 : ∀ p ∈ P, qSum p ≤ 1) (X : ℕ) :
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (centeredFiniteWeight P qU qV qSum) ≤
      ((X : ℝ) / primeModulus P) *
          ((8 * X : ℕ) : ℝ) / primeModulus P *
          (∏ p : P,
            ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
              ((p : ℝ) - 1) * (qU p + qV p + qSum p) +
              qU p * qV p * qSum p)) +
        (9 * (X : ℝ) / primeModulus P + 1) *
          (primeModulus P : ℝ) ^ 2 := by
  let w : ∀ p : ℕ, ZMod p × ZMod p → ℝ :=
    fun p ↦ centeredLocalWeight (qU p) (qV p) (qSum p)
  have hw (p : P) (z : ZMod p × ZMod p) :
      0 ≤ w p z ∧ w p z ≤ 1 :=
    centeredLocalWeight_nonneg_le_one
      (qU p) (qV p) (qSum p)
      (hqU0 p p.property) (hqU1 p p.property)
      (hqV0 p p.property) (hqV1 p p.property)
      (hqSum0 p p.property) (hqSum1 p p.property) z
  have hbase :=
    threeLine_finiteLocalProduct_le P hprime w
      (fun p z ↦ (hw p z).1) (fun p z ↦ (hw p z).2) X
  have hmass :
      (∏ p : P, ∑ z : ZMod p × ZMod p, w p z) =
        ∏ p : P,
          ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
            ((p : ℝ) - 1) * (qU p + qV p + qSum p) +
            qU p * qV p * qSum p) := by
    apply Finset.prod_congr rfl
    intro p _
    exact sum_centeredLocalWeight p (qU p) (qV p) (qSum p)
  change periodicBoxSum (primeModulus P) X X 1 (8 * X)
      (finiteLocalProduct P w) ≤ _ at hbase
  rwa [hmass] at hbase

/-- Fully explicit cross finite-sieve estimate in the same box. -/
theorem threeLine_crossFiniteWeight_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hodd : ∀ p ∈ P, p ≠ 2)
    [NeZero (primeModulus P)] [∀ p : P, NeZero (p : ℕ)]
    (qU qW qLinear : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqW0 : ∀ p ∈ P, 0 ≤ qW p) (hqW1 : ∀ p ∈ P, qW p ≤ 1)
    (hqLinear0 : ∀ p ∈ P, 0 ≤ qLinear p)
    (hqLinear1 : ∀ p ∈ P, qLinear p ≤ 1) (X : ℕ) :
    periodicBoxSum (primeModulus P) X X 1 (8 * X)
        (crossFiniteWeight P qU qW qLinear) ≤
      ((X : ℝ) / primeModulus P) *
          ((8 * X : ℕ) : ℝ) / primeModulus P *
          (∏ p : P,
            ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
              ((p : ℝ) - 1) * (qU p + qW p + qLinear p) +
              qU p * qW p * qLinear p)) +
        (9 * (X : ℝ) / primeModulus P + 1) *
          (primeModulus P : ℝ) ^ 2 := by
  let w : ∀ p : ℕ, ZMod p × ZMod p → ℝ :=
    fun p ↦ crossLocalWeight (qU p) (qW p) (qLinear p)
  have hw (p : P) (z : ZMod p × ZMod p) :
      0 ≤ w p z ∧ w p z ≤ 1 :=
    crossLocalWeight_nonneg_le_one
      (qU p) (qW p) (qLinear p)
      (hqU0 p p.property) (hqU1 p p.property)
      (hqW0 p p.property) (hqW1 p p.property)
      (hqLinear0 p p.property) (hqLinear1 p p.property) z
  have hbase :=
    threeLine_finiteLocalProduct_le P hprime w
      (fun p z ↦ (hw p z).1) (fun p z ↦ (hw p z).2) X
  have hmass :
      (∏ p : P, ∑ z : ZMod p × ZMod p, w p z) =
        ∏ p : P,
          ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
            ((p : ℝ) - 1) * (qU p + qW p + qLinear p) +
            qU p * qW p * qLinear p) := by
    apply Finset.prod_congr rfl
    intro p _
    exact sum_crossLocalWeight p (hprime p p.property)
      (hodd p p.property) (qU p) (qW p) (qLinear p)
  change periodicBoxSum (primeModulus P) X X 1 (8 * X)
      (finiteLocalProduct P w) ≤ _ at hbase
  rwa [hmass] at hbase

/-- A congruence class occurs exactly `q` times in an interval of
length `q * d`. -/
theorem card_residueClassIco_mul
    {d : ℕ} (hd : 0 < d) (a q r : ℕ) :
    (residueClassIco d a (q * d) r).card = q := by
  let pred : ℕ → Prop := fun n ↦ n % d = r % d
  have hperiodic : Function.Periodic pred d := by
    intro n
    simp [pred, Nat.add_mod_right]
  have hcount : (q * d).count pred = q := by
    rw [Nat.count_eq_card_filter_range]
    calc
      ((range (q * d)).filter pred).card = (range q).card := by
        refine Finset.card_bij (fun n _ ↦ n / d) ?_ ?_ ?_
        · intro n hn
          have hnrange := (mem_filter.mp hn).1
          rw [mem_range] at hnrange ⊢
          exact (Nat.div_lt_iff_lt_mul hd).2 hnrange
        · intro n hn m hm hdiv
          have hnmod := (mem_filter.mp hn).2
          have hmmod := (mem_filter.mp hm).2
          calc
            n = n % d + d * (n / d) := (Nat.mod_add_div n d).symm
            _ = m % d + d * (m / d) := by rw [hnmod, hmmod, hdiv]
            _ = m := Nat.mod_add_div m d
        · intro k hk
          let n := d * k + r % d
          have hrmod : r % d < d := Nat.mod_lt r hd
          have hnlt : n < q * d := by
            calc
              n = d * k + r % d := rfl
              _ < d * k + d := Nat.add_lt_add_left hrmod _
              _ = (k + 1) * d := by ring
              _ ≤ q * d :=
                Nat.mul_le_mul_right d (Nat.succ_le_iff.mpr (mem_range.mp hk))
          refine ⟨n, ?_, ?_⟩
          · rw [mem_filter]
            constructor
            · exact mem_range.mpr hnlt
            · simp [pred, n]
          · simp [n, Nat.mul_add_div hd, Nat.div_eq_of_lt hrmod]
      _ = q := by simp
  change ((Ico a (a + q * d)).filter pred).card = q
  rw [Nat.filter_Ico_card_eq_of_periodic]
  · exact hcount
  · simpa [nsmul_eq_mul] using hperiodic.nsmul q

/-- Every congruence class occurs at least `X / d` times in an
interval of length `X`. -/
theorem div_le_card_residueClassIco
    {d : ℕ} (hd : 0 < d) (a X r : ℕ) :
    X / d ≤ (residueClassIco d a X r).card := by
  have hsubset :
      residueClassIco d a ((X / d) * d) r ⊆
        residueClassIco d a X r := by
    intro n hn
    rw [mem_residueClassIco] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2.1
      (Nat.add_le_add_left (Nat.div_mul_le_self X d) a), hn.2.2⟩
  calc
    X / d = (residueClassIco d a ((X / d) * d) r).card :=
      (card_residueClassIco_mul hd a (X / d) r).symm
    _ ≤ (residueClassIco d a X r).card := card_le_card hsubset

/-- Real lower bound complementary to `card_zmodFiberIco_le`. -/
theorem card_zmodFiberIco_lower_real
    {d : ℕ} (hd : 0 < d) (a X : ℕ) (r : ZMod d) :
    (X : ℝ) / d - 1 ≤ (zmodFiberIco d a X r).card := by
  let hdNeZero : NeZero d := ⟨hd.ne'⟩
  have hset :
      zmodFiberIco d a X r = residueClassIco d a X r.val := by
    ext n
    simp only [mem_zmodFiberIco, mem_residueClassIco]
    refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
    calc
      (n : ZMod d) = r ↔
          (n : ZMod d) = (r.val : ZMod d) := by
            rw [ZMod.natCast_zmod_val]
      _ ↔ n % d = r.val % d :=
        ZMod.natCast_eq_natCast_iff' n r.val d
  have hnat :
      X / d ≤ (zmodFiberIco d a X r).card := by
    rw [hset]
    exact div_le_card_residueClassIco hd a X r.val
  have hltNat : X < (X / d + 1) * d := by
    calc
      X = X % d + d * (X / d) := (Nat.mod_add_div X d).symm
      _ < d + d * (X / d) :=
        Nat.add_lt_add_right (Nat.mod_lt X hd) _
      _ = (X / d + 1) * d := by ring
  have hfloor :
      (X : ℝ) / d - 1 ≤ (X / d : ℕ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast hltNat.le
  exact hfloor.trans (by exact_mod_cast hnat)

/-- Real upper bound for a one-dimensional residue fiber. -/
theorem card_zmodFiberIco_upper_real
    {d : ℕ} (hd : 0 < d) (a X : ℕ) (r : ZMod d) :
    ((zmodFiberIco d a X r).card : ℝ) ≤ (X : ℝ) / d + 1 := by
  have hnat := card_zmodFiberIco_le hd a X r
  calc
    ((zmodFiberIco d a X r).card : ℝ) ≤
        ((X / d + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((X / d : ℕ) : ℝ) + 1 := by push_cast; rfl
    _ ≤ (X : ℝ) / d + 1 := by
      gcongr
      exact Nat.cast_div_le

/-- A two-dimensional residue fiber differs from its real mean by at
most the standard boundary factor. -/
theorem abs_card_zmodFiberBox_sub_mean_le
    {d : ℕ} (hd : 0 < d) (au Xu av Xv : ℕ)
    (r : ZMod d × ZMod d) :
    |((zmodFiberBox d au Xu av Xv r).card : ℝ) -
        ((Xu : ℝ) / d) * ((Xv : ℝ) / d)| ≤
      (Xu : ℝ) / d + (Xv : ℝ) / d + 1 := by
  let A : ℝ := (zmodFiberIco d au Xu r.1).card
  let B : ℝ := (zmodFiberIco d av Xv r.2).card
  let a : ℝ := (Xu : ℝ) / d
  let b : ℝ := (Xv : ℝ) / d
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hAupper : A ≤ a + 1 :=
    card_zmodFiberIco_upper_real hd au Xu r.1
  have hBupper : B ≤ b + 1 :=
    card_zmodFiberIco_upper_real hd av Xv r.2
  have hAlower : a - 1 ≤ A :=
    card_zmodFiberIco_lower_real hd au Xu r.1
  have hBlower : b - 1 ≤ B :=
    card_zmodFiberIco_lower_real hd av Xv r.2
  have hAabs : |A - a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hBabs : |B - b| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [card_zmodFiberBox]
  push_cast
  change |A * B - a * b| ≤ a + b + 1
  calc
    |A * B - a * b| = |(A - a) * B + a * (B - b)| := by ring_nf
    _ ≤ |(A - a) * B| + |a * (B - b)| := abs_add_le _ _
    _ = |A - a| * |B| + |a| * |B - b| := by
      rw [abs_mul, abs_mul]
    _ ≤ 1 * (b + 1) + a * 1 := by
      apply add_le_add
      · exact mul_le_mul hAabs
          (by simpa [abs_of_nonneg hB0] using hBupper)
          (abs_nonneg B) zero_le_one
      · simpa [abs_of_nonneg ha0] using
          mul_le_mul_of_nonneg_left hBabs ha0
    _ = a + b + 1 := by ring

/-- Two-sided periodic-lattice discrepancy, charged only to residues
where the nonnegative weight is nonzero. -/
theorem abs_periodicBoxSum_sub_mean_le
    {d : ℕ} [NeZero d] (hd : 0 < d) (au Xu av Xv : ℕ)
    (h : ZMod d × ZMod d → ℝ)
    (hnonneg : ∀ r, 0 ≤ h r) (hle : ∀ r, h r ≤ 1) :
    |periodicBoxSum d au Xu av Xv h -
        ((Xu : ℝ) / d) * ((Xv : ℝ) / d) * (∑ r, h r)| ≤
      ((Xu : ℝ) / d + (Xv : ℝ) / d + 1) *
        (residueWeightSupport d h).card := by
  rw [periodicBoxSum_eq_sum_fibers]
  let E : ℝ := (Xu : ℝ) / d + (Xv : ℝ) / d + 1
  have hE0 : 0 ≤ E := by positivity
  have hpoint (r : ZMod d × ZMod d) :
      |((zmodFiberBox d au Xu av Xv r).card : ℝ) -
          ((Xu : ℝ) / d) * ((Xv : ℝ) / d)| * h r ≤
        E * if h r = 0 then 0 else 1 := by
    by_cases hr : h r = 0
    · simp [hr]
    · simp only [if_neg hr]
      exact mul_le_mul
        (abs_card_zmodFiberBox_sub_mean_le hd au Xu av Xv r)
        (hle r) (hnonneg r) hE0
  calc
    |(∑ r, ((zmodFiberBox d au Xu av Xv r).card : ℝ) * h r) -
        ((Xu : ℝ) / d) * ((Xv : ℝ) / d) * (∑ r, h r)| =
      |∑ r, ((((zmodFiberBox d au Xu av Xv r).card : ℝ) -
          ((Xu : ℝ) / d) * ((Xv : ℝ) / d)) * h r)| := by
        congr 1
        rw [mul_sum, ← sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ ≤ ∑ r, |(((zmodFiberBox d au Xu av Xv r).card : ℝ) -
          ((Xu : ℝ) / d) * ((Xv : ℝ) / d)) * h r| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ r, |((zmodFiberBox d au Xu av Xv r).card : ℝ) -
          ((Xu : ℝ) / d) * ((Xv : ℝ) / d)| * h r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [abs_mul, abs_of_nonneg (hnonneg r)]
    _ ≤ ∑ r, E * if h r = 0 then 0 else 1 :=
      sum_le_sum fun r _ ↦ hpoint r
    _ = E * (residueWeightSupport d h).card := by
      rw [← mul_sum]
      congr 1
      simpa [residueWeightSupport] using
        (Finset.sum_boole (R := ℝ) (fun r => h r ≠ 0)
          (univ : Finset (ZMod d × ZMod d)))

/-- Modulus attached to a subset of the outer prime index type `P`. -/
def subsetModulus {P : Finset ℕ} (T : Finset P) : ℕ :=
  ∏ p : T, ((p : P) : ℕ)

theorem subsetPrime_dvd_subsetModulus
    {P : Finset ℕ} (T : Finset P) (p : T) :
    (((p : T) : P) : ℕ) ∣ subsetModulus T := by
  exact Finset.dvd_prod_of_mem
    (fun q : T ↦ (((q : T) : P) : ℕ)) (mem_univ p)

theorem subsetModulus_pos
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P) :
    0 < subsetModulus T := by
  unfold subsetModulus
  exact Finset.prod_pos fun p _ ↦
    (hprime p.val.val p.val.property).pos

theorem subset_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P) :
    Pairwise (Function.onFun Nat.Coprime
      fun p : T ↦ (((p : T) : P) : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes
    (hprime p.val.val p.val.property)
    (hprime q.val.val q.val.property)).2
  intro hpqval
  exact hpq (Subtype.ext (Subtype.ext hpqval))

/-- Two-coordinate CRT for one subset `T ⊆ P`. -/
noncomputable def subsetPairCRT
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P) :
    (ZMod (subsetModulus T) × ZMod (subsetModulus T)) ≃
      (∀ p : T, ZMod (((p : T) : P) : ℕ) ×
        ZMod (((p : T) : P) : ℕ)) :=
  (Equiv.prodCongr
      (ZMod.prodEquivPi
        (fun p : T ↦ (((p : T) : P) : ℕ))
        (subset_pairwise_coprime hprime T)).toEquiv
      (ZMod.prodEquivPi
        (fun p : T ↦ (((p : T) : P) : ℕ))
        (subset_pairwise_coprime hprime T)).toEquiv).trans
    (piPairEquiv
      (fun p : T ↦ ZMod (((p : T) : P) : ℕ))
      (fun p : T ↦ ZMod (((p : T) : P) : ℕ)))

@[simp] theorem subsetPairCRT_apply
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P)
    (r : ZMod (subsetModulus T) × ZMod (subsetModulus T))
    (p : T) :
    subsetPairCRT hprime T r p =
      (ZMod.castHom (subsetPrime_dvd_subsetModulus T p)
          (ZMod (((p : T) : P) : ℕ)) r.1,
        ZMod.castHom (subsetPrime_dvd_subsetModulus T p)
          (ZMod (((p : T) : P) : ℕ)) r.2) := by
  unfold subsetPairCRT piPairEquiv
  apply Prod.ext
  · exact ZMod.prodEquivPi_apply
      (fun q : T ↦ (((q : T) : P) : ℕ))
      (subset_pairwise_coprime hprime T) r.1 p
  · exact ZMod.prodEquivPi_apply
      (fun q : T ↦ (((q : T) : P) : ℕ))
      (subset_pairwise_coprime hprime T) r.2 p

/-- Product of a dependent family of local functions over `T ⊆ P`. -/
noncomputable def subsetLocalProduct
    {P : Finset ℕ}
    (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (r : ZMod (subsetModulus T) × ZMod (subsetModulus T)) : ℝ :=
  ∏ p : T,
    ell p
      (ZMod.castHom (subsetPrime_dvd_subsetModulus T p)
          (ZMod (((p : T) : P) : ℕ)) r.1,
        ZMod.castHom (subsetPrime_dvd_subsetModulus T p)
          (ZMod (((p : T) : P) : ℕ)) r.2)

theorem subsetLocalProduct_eq_crt
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (r : ZMod (subsetModulus T) × ZMod (subsetModulus T)) :
    subsetLocalProduct T ell r =
      ∏ p : T, ell p (subsetPairCRT hprime T r p) := by
  classical
  apply Finset.prod_congr rfl
  intro p _
  rw [subsetPairCRT_apply]

/-- Exact CRT mass factorization for a subset product. -/
theorem sum_subsetLocalProduct
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P)
    [NeZero (subsetModulus T)]
    [∀ p : T, NeZero ((((p : T) : P) : ℕ))]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ) :
    (∑ r : ZMod (subsetModulus T) × ZMod (subsetModulus T),
        subsetLocalProduct T ell r) =
      ∏ p : T,
        ∑ z : ZMod (((p : T) : P) : ℕ) ×
            ZMod (((p : T) : P) : ℕ), ell p z := by
  classical
  calc
    (∑ r : ZMod (subsetModulus T) × ZMod (subsetModulus T),
        subsetLocalProduct T ell r) =
      ∑ r : ZMod (subsetModulus T) × ZMod (subsetModulus T),
        ∏ p : T, ell p (subsetPairCRT hprime T r p) := by
          apply Finset.sum_congr rfl
          intro r _
          exact subsetLocalProduct_eq_crt hprime T ell r
    _ = ∑ z : (∀ p : T,
          ZMod (((p : T) : P) : ℕ) ×
            ZMod (((p : T) : P) : ℕ)),
        ∏ p : T, ell p (z p) :=
      (subsetPairCRT hprime T).sum_comp
        (fun z ↦ ∏ p : T, ell p (z p))
    _ = _ := (Fintype.prod_sum (fun p : T ↦ ell p)).symm

/-- CRT support of a product injects into the product of its local
supports. -/
theorem card_support_subsetLocalProduct_le
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (T : Finset P)
    [NeZero (subsetModulus T)]
    [∀ p : T, NeZero ((((p : T) : P) : ℕ))]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ) :
    (residueWeightSupport (subsetModulus T)
      (subsetLocalProduct T ell)).card ≤
        ∏ p : T,
          (residueWeightSupport (((p : T) : P) : ℕ)
            (ell p)).card := by
  classical
  let targets : ∀ p : T,
      Finset (ZMod (((p : T) : P) : ℕ) ×
        ZMod (((p : T) : P) : ℕ)) :=
    fun p ↦ residueWeightSupport (((p : T) : P) : ℕ) (ell p)
  have hcard :
      (residueWeightSupport (subsetModulus T)
        (subsetLocalProduct T ell)).card ≤
          (Fintype.piFinset targets).card := by
    refine Finset.card_le_card_of_injOn
      (subsetPairCRT hprime T) ?_ ?_
    · intro r hr
      change subsetPairCRT hprime T r ∈ Fintype.piFinset targets
      rw [Fintype.mem_piFinset]
      intro p
      rw [mem_residueWeightSupport]
      have hprod :
          (∏ q : T, ell q (subsetPairCRT hprime T r q)) ≠ 0 := by
        rw [← subsetLocalProduct_eq_crt hprime T ell r]
        exact mem_residueWeightSupport.mp hr
      exact (Finset.prod_ne_zero_iff.mp hprod) p (mem_univ p)
    · intro r _ s _ hrs
      exact (subsetPairCRT hprime T).injective hrs
  simpa [targets] using hcard

/-- Mean of a local loss over its `p²` residue pairs. -/
noncomputable def localLossMean
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (p : P) : ℝ :=
  (∑ z : ZMod (p : ℕ) × ZMod (p : ℕ), ell p z) /
    (p : ℝ) ^ 2

/-- Product of local losses in a subset `T`, evaluated at a natural
pair. -/
noncomputable def subsetLossAtNat
    {P : Finset ℕ} (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (x : ℕ × ℕ) : ℝ :=
  ∏ p : T, ell p
    ((x.1 : ZMod ((p : P) : ℕ)),
      (x.2 : ZMod ((p : P) : ℕ)))

/-- Sum of one subset-loss product over the three-line box. -/
noncomputable def subsetLossBoxSum
    {P : Finset ℕ} (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (X : ℕ) : ℝ :=
  ∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
    subsetLossAtNat T ell x

theorem subsetLocalProduct_natCast
    {P : Finset ℕ} (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (u v : ℕ) :
    subsetLocalProduct T ell
        ((u : ZMod (subsetModulus T)),
          (v : ZMod (subsetModulus T))) =
      subsetLossAtNat T ell (u, v) := by
  classical
  unfold subsetLocalProduct subsetLossAtNat
  apply Finset.prod_congr rfl
  intro p _
  simp

/-- A subset box sum is a periodic box sum at the subset modulus. -/
theorem subsetLossBoxSum_eq_periodicBoxSum
    {P : Finset ℕ} (T : Finset P)
    [NeZero (subsetModulus T)]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (X : ℕ) :
    subsetLossBoxSum T ell X =
      periodicBoxSum (subsetModulus T) X X 1 (8 * X)
        (subsetLocalProduct T ell) := by
  unfold subsetLossBoxSum periodicBoxSum
  apply Finset.sum_congr
  · ext x
    simp only [mem_product, mem_Ico, mem_Icc]
    omega
  · intro x _
    exact (subsetLocalProduct_natCast T ell x.1 x.2).symm

/-- The support of a subset product is at most
`3^|T| * subsetModulus T` when every local support has size at most
`3p`. -/
theorem card_support_subsetLocalProduct_le_three_pow_mul
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (T : Finset P)
    [NeZero (subsetModulus T)]
    [∀ p : T, NeZero ((((p : T) : P) : ℕ))]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤ 3 * (p : ℕ)) :
    (residueWeightSupport (subsetModulus T)
      (subsetLocalProduct T ell)).card ≤
        3 ^ T.card * subsetModulus T := by
  calc
    (residueWeightSupport (subsetModulus T)
        (subsetLocalProduct T ell)).card ≤
      ∏ p : T,
        (residueWeightSupport (((p : T) : P) : ℕ)
          (ell p)).card :=
      card_support_subsetLocalProduct_le hprime T ell
    _ ≤ ∏ p : T, 3 * (((p : T) : P) : ℕ) := by
      exact Finset.prod_le_prod' fun p _ ↦ hsupport p
    _ = 3 ^ T.card * subsetModulus T := by
      rw [Finset.prod_mul_distrib]
      simp [subsetModulus]

/-- Normalization of a subset CRT main term as `8X²` times the product
of the local means. -/
theorem subset_mainTerm_eq
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (X : ℕ) :
    ((X : ℝ) / subsetModulus T) *
        ((8 * X : ℕ) : ℝ) / subsetModulus T *
        (∏ p : T,
          ∑ z : ZMod (((p : T) : P) : ℕ) ×
              ZMod (((p : T) : P) : ℕ), ell p z) =
      8 * (X : ℝ) ^ 2 *
        ∏ p : T, localLossMean ell p := by
  have hmodulus : (subsetModulus T : ℝ) ≠ 0 := by
    exact_mod_cast (subsetModulus_pos hprime T).ne'
  unfold localLossMean
  rw [Finset.prod_div_distrib, Finset.prod_pow]
  have hcast :
      (∏ p : T, (((p : T) : P) : ℝ)) =
        (subsetModulus T : ℝ) := by
    simp [subsetModulus]
  rw [hcast]
  push_cast
  field_simp

/-- Sharp finite discrepancy for one subset term. -/
theorem abs_subsetLossBoxSum_sub_main_le
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (T : Finset P)
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hell0 : ∀ (p : P) z, 0 ≤ ell p z)
    (hell1 : ∀ (p : P) z, ell p z ≤ 1)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤ 3 * (p : ℕ))
    (X : ℕ) :
    |subsetLossBoxSum T ell X -
        8 * (X : ℝ) ^ 2 *
          ∏ p : T, localLossMean ell p| ≤
      (3 : ℝ) ^ T.card *
        (9 * (X : ℝ) + subsetModulus T) := by
  let hmodulusNeZero : NeZero (subsetModulus T) :=
    ⟨(subsetModulus_pos hprime T).ne'⟩
  let hprimeNeZero : ∀ p : T, NeZero ((((p : T) : P) : ℕ)) :=
    fun p ↦ inferInstance
  have hproduct0 :
      ∀ r : ZMod (subsetModulus T) × ZMod (subsetModulus T),
        0 ≤ subsetLocalProduct T ell r := by
    intro r
    unfold subsetLocalProduct
    exact Finset.prod_nonneg fun p _ ↦ hell0 p _
  have hproduct1 :
      ∀ r : ZMod (subsetModulus T) × ZMod (subsetModulus T),
        subsetLocalProduct T ell r ≤ 1 := by
    intro r
    unfold subsetLocalProduct
    exact Finset.prod_le_one
      (fun p _ ↦ hell0 p _) (fun p _ ↦ hell1 p _)
  have hperiodic :=
    abs_periodicBoxSum_sub_mean_le
      (subsetModulus_pos hprime T) X X 1 (8 * X)
      (subsetLocalProduct T ell) hproduct0 hproduct1
  rw [← subsetLossBoxSum_eq_periodicBoxSum T ell X,
    sum_subsetLocalProduct hprime T ell] at hperiodic
  have hmain :
      ((X : ℝ) / subsetModulus T) *
          (((8 * X : ℕ) : ℝ) / subsetModulus T) *
          (∏ p : T,
            ∑ z : ZMod (((p : T) : P) : ℕ) ×
                ZMod (((p : T) : P) : ℕ), ell p z) =
        8 * (X : ℝ) ^ 2 *
          ∏ p : T, localLossMean ell p := by
    calc
      ((X : ℝ) / subsetModulus T) *
          (((8 * X : ℕ) : ℝ) / subsetModulus T) *
          (∏ p : T,
            ∑ z : ZMod (((p : T) : P) : ℕ) ×
                ZMod (((p : T) : P) : ℕ), ell p z) =
        ((X : ℝ) / subsetModulus T) *
          ((8 * X : ℕ) : ℝ) / subsetModulus T *
          (∏ p : T,
            ∑ z : ZMod (((p : T) : P) : ℕ) ×
                ZMod (((p : T) : P) : ℕ), ell p z) := by ring
      _ = _ := subset_mainTerm_eq hprime T ell X
  rw [hmain] at hperiodic
  have hsupportNat :=
    card_support_subsetLocalProduct_le_three_pow_mul
      hprime T ell hsupport
  have hsupportReal :
      ((residueWeightSupport (subsetModulus T)
        (subsetLocalProduct T ell)).card : ℝ) ≤
          (3 : ℝ) ^ T.card * subsetModulus T := by
    exact_mod_cast hsupportNat
  have hcoef : 0 ≤
      (X : ℝ) / subsetModulus T +
        ((8 * X : ℕ) : ℝ) / subsetModulus T + 1 := by
    positivity
  calc
    |subsetLossBoxSum T ell X -
        8 * (X : ℝ) ^ 2 *
          ∏ p : T, localLossMean ell p| ≤
      ((X : ℝ) / subsetModulus T +
        ((8 * X : ℕ) : ℝ) / subsetModulus T + 1) *
          (residueWeightSupport (subsetModulus T)
            (subsetLocalProduct T ell)).card := hperiodic
    _ ≤ ((X : ℝ) / subsetModulus T +
        ((8 * X : ℕ) : ℝ) / subsetModulus T + 1) *
          ((3 : ℝ) ^ T.card * subsetModulus T) :=
      mul_le_mul_of_nonneg_left hsupportReal hcoef
    _ = (3 : ℝ) ^ T.card *
        (9 * (X : ℝ) + subsetModulus T) := by
      have hmodulus : (subsetModulus T : ℝ) ≠ 0 := by
        exact_mod_cast (subsetModulus_pos hprime T).ne'
      push_cast
      field_simp
      ring

/-- Mean of a local retained weight over its `p²` residue pairs. -/
noncomputable def localWeightMean
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (w : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (p : P) : ℝ :=
  (∑ z : ZMod (p : ℕ) × ZMod (p : ℕ), w p z) /
    (p : ℝ) ^ 2

/-- Evaluation of a dependent local family at a natural pair. -/
noncomputable def localAtNat
    {P : Finset ℕ}
    (f : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (x : ℕ × ℕ) (p : P) : ℝ :=
  f p ((x.1 : ZMod (p : ℕ)), (x.2 : ZMod (p : ℕ)))

/-- Product-weight sum over the exact three-line box. -/
noncomputable def finiteWeightBoxSum
    {P : Finset ℕ}
    (w : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (X : ℕ) : ℝ :=
  ∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
    ∏ p : P, localAtNat w x p

/-- The box sum of a Bonferroni truncation is exactly the signed sum
of its subset box sums. -/
theorem sum_bonferroniTruncation_eq_sum_subsetLossBoxSum
    {P : Finset ℕ}
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (X m : ℕ) :
    (∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
        bonferroniTruncation univ (localAtNat ell x) m) =
      ∑ k ∈ range m,
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (-1 : ℝ) ^ k * subsetLossBoxSum T ell X := by
  unfold bonferroniTruncation elementarySymmetric
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [mul_sum]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [← mul_sum]
  congr 1
  unfold subsetLossBoxSum subsetLossAtNat localAtNat
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.prod_attach T
    (fun p ↦ ell p
      ((x.1 : ZMod (p : ℕ)), (x.2 : ZMod (p : ℕ))))).symm

/-- Complementary local functions have complementary normalized
means. -/
theorem localWeightMean_add_localLossMean
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (w ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hcomplement : ∀ (p : P) z, w p z + ell p z = 1)
    (p : P) :
    localWeightMean w p + localLossMean ell p = 1 := by
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast (hprime p p.property).pos
  have hp0 : (p : ℝ) ^ 2 ≠ 0 := by
    positivity
  unfold localWeightMean localLossMean
  rw [← add_div]
  have hsum :
      (∑ z : ZMod (p : ℕ) × ZMod (p : ℕ), w p z) +
          ∑ z : ZMod (p : ℕ) × ZMod (p : ℕ), ell p z =
        (p : ℝ) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ z : ZMod (p : ℕ) × ZMod (p : ℕ),
          (w p z + ell p z)) = ∑ _z, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro z _
            exact hcomplement p z
      _ = (p : ℝ) ^ 2 := by
        simp [ZMod.card, pow_two]
  rw [hsum, div_self hp0]

/-- A nonnegative local loss bounded by one has normalized mean in
`[0,1]`. -/
theorem localLossMean_nonneg_le_one
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hell0 : ∀ (p : P) z, 0 ≤ ell p z)
    (hell1 : ∀ (p : P) z, ell p z ≤ 1)
    (p : P) :
    0 ≤ localLossMean ell p ∧ localLossMean ell p ≤ 1 := by
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast (hprime p p.property).pos
  have hp2 : 0 < (p : ℝ) ^ 2 := by positivity
  unfold localLossMean
  constructor
  · exact div_nonneg (sum_nonneg fun z _ ↦ hell0 p z) hp2.le
  · rw [div_le_one hp2]
    calc
      (∑ z : ZMod (p : ℕ) × ZMod (p : ℕ), ell p z) ≤
          ∑ _z, (1 : ℝ) :=
        sum_le_sum fun z _ ↦ hell1 p z
      _ = (p : ℝ) ^ 2 := by simp [ZMod.card, pow_two]

/-- Pointwise Bonferroni bound for a complementary retained/loss
family. -/
theorem finiteWeight_le_bonferroni_localLoss
    {P : Finset ℕ}
    (w ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hcomplement : ∀ (p : P) z, w p z + ell p z = 1)
    (hell0 : ∀ (p : P) z, 0 ≤ ell p z)
    (hell1 : ∀ (p : P) z, ell p z ≤ 1)
    (x : ℕ × ℕ) (R : ℕ) :
    (∏ p : P, localAtNat w x p) ≤
      bonferroniTruncation univ (localAtNat ell x) (2 * R + 1) := by
  have hprod :
      (∏ p : P, localAtNat w x p) =
        ∏ p ∈ (univ : Finset P), (1 - localAtNat ell x p) := by
    apply Finset.prod_congr rfl
    intro p _
    unfold localAtNat
    linarith [hcomplement p
      ((x.1 : ZMod (p : ℕ)), (x.2 : ZMod (p : ℕ)))]
  rw [hprod]
  exact bonferroni_even_upper (univ : Finset P)
    (localAtNat ell x)
    (fun p _ ↦ hell0 p _)
    (fun p _ ↦ hell1 p _) R

/-- Subtype products used by the subset CRT agree with the ordinary
subset products in `elementarySymmetric`. -/
theorem sum_subsetMeanProduct_eq_elementarySymmetric
    {P : Finset ℕ} (mu : P → ℝ) (k : ℕ) :
    (∑ T ∈ (univ : Finset P).powersetCard k,
        ∏ p : T, mu p) =
      elementarySymmetric (univ : Finset P) mu k := by
  unfold elementarySymmetric
  apply Finset.sum_congr rfl
  intro T _
  exact Finset.prod_attach T mu

/-- Quantitative finite Bonferroni/CRT truncation bound.

The first term is the expected box area times the product of the local
retained means.  The second is the factorial Bonferroni tail.  Each
subset boundary term is charged by
`3^|T| * (9X + subsetModulus T)`.
-/
theorem finiteWeightBoxSum_le_main_add_tail_add_boundary
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (w ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hcomplement : ∀ (p : P) z, w p z + ell p z = 1)
    (hell0 : ∀ (p : P) z, 0 ≤ ell p z)
    (hell1 : ∀ (p : P) z, ell p z ≤ 1)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤ 3 * (p : ℕ))
    (X R : ℕ) :
    finiteWeightBoxSum w X ≤
      8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
        8 * (X : ℝ) ^ 2 *
          ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ∑ k ∈ range (2 * R + 1),
          ∑ T ∈ (univ : Finset P).powersetCard k,
            (3 : ℝ) ^ T.card *
              (9 * (X : ℝ) + subsetModulus T) := by
  let mu : P → ℝ := fun p ↦ localLossMean ell p
  let box : Finset (ℕ × ℕ) :=
    Ico X (2 * X) ×ˢ Icc 1 (8 * X)
  have hboxBonf :
      finiteWeightBoxSum w X ≤
        ∑ x ∈ box,
          bonferroniTruncation univ (localAtNat ell x)
            (2 * R + 1) := by
    unfold finiteWeightBoxSum
    exact sum_le_sum fun x _ ↦
      finiteWeight_le_bonferroni_localLoss
        w ell hcomplement hell0 hell1 x R
  have hdisc (T : Finset P) :
      |subsetLossBoxSum T ell X -
          8 * (X : ℝ) ^ 2 * ∏ p : T, mu p| ≤
        (3 : ℝ) ^ T.card *
          (9 * (X : ℝ) + subsetModulus T) := by
    exact abs_subsetLossBoxSum_sub_main_le
      hprime T ell hell0 hell1 hsupport X
  have hsigned (k : ℕ) (T : Finset P) :
      (-1 : ℝ) ^ k * subsetLossBoxSum T ell X ≤
        (-1 : ℝ) ^ k *
            (8 * (X : ℝ) ^ 2 * ∏ p : T, mu p) +
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T) := by
    have hdiff :
        (-1 : ℝ) ^ k *
            (subsetLossBoxSum T ell X -
              8 * (X : ℝ) ^ 2 * ∏ p : T, mu p) ≤
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T) := by
      calc
        (-1 : ℝ) ^ k *
            (subsetLossBoxSum T ell X -
              8 * (X : ℝ) ^ 2 * ∏ p : T, mu p) ≤
          |(-1 : ℝ) ^ k *
            (subsetLossBoxSum T ell X -
              8 * (X : ℝ) ^ 2 * ∏ p : T, mu p)| :=
            le_abs_self _
        _ = |subsetLossBoxSum T ell X -
              8 * (X : ℝ) ^ 2 * ∏ p : T, mu p| := by
            rw [abs_mul]
            simp
        _ ≤ _ := hdisc T
    calc
      (-1 : ℝ) ^ k * subsetLossBoxSum T ell X =
          (-1 : ℝ) ^ k *
              (8 * (X : ℝ) ^ 2 * ∏ p : T, mu p) +
            (-1 : ℝ) ^ k *
              (subsetLossBoxSum T ell X -
                8 * (X : ℝ) ^ 2 * ∏ p : T, mu p) := by ring
      _ ≤ _ := add_le_add_right hdiff _
  have htruncated :
      (∑ x ∈ box,
          bonferroniTruncation univ (localAtNat ell x)
            (2 * R + 1)) ≤
        8 * (X : ℝ) ^ 2 *
            bonferroniTruncation univ mu (2 * R + 1) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) := by
    rw [show (∑ x ∈ box,
        bonferroniTruncation univ (localAtNat ell x)
          (2 * R + 1)) =
      ∑ k ∈ range (2 * R + 1),
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (-1 : ℝ) ^ k * subsetLossBoxSum T ell X by
      exact sum_bonferroniTruncation_eq_sum_subsetLossBoxSum
        ell X (2 * R + 1)]
    calc
      (∑ k ∈ range (2 * R + 1),
          ∑ T ∈ (univ : Finset P).powersetCard k,
            (-1 : ℝ) ^ k * subsetLossBoxSum T ell X) ≤
        ∑ k ∈ range (2 * R + 1),
          ∑ T ∈ (univ : Finset P).powersetCard k,
            ((-1 : ℝ) ^ k *
                (8 * (X : ℝ) ^ 2 * ∏ p : T, mu p) +
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T)) :=
          sum_le_sum fun k _ ↦ sum_le_sum fun T _ ↦ hsigned k T
      _ = 8 * (X : ℝ) ^ 2 *
            bonferroniTruncation univ mu (2 * R + 1) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) := by
          simp_rw [sum_add_distrib]
          congr 1
          unfold bonferroniTruncation
          rw [mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          calc
            (∑ T ∈ (univ : Finset P).powersetCard k,
                (-1 : ℝ) ^ k *
                  (8 * (X : ℝ) ^ 2 * ∏ p : T, mu p)) =
              (8 * (X : ℝ) ^ 2 * (-1 : ℝ) ^ k) *
                ∑ T ∈ (univ : Finset P).powersetCard k,
                  ∏ p : T, mu p := by
                    rw [mul_sum]
                    apply Finset.sum_congr rfl
                    intro T _
                    ring
            _ = 8 * (X : ℝ) ^ 2 *
                ((-1 : ℝ) ^ k *
                  elementarySymmetric univ mu k) := by
                    rw [sum_subsetMeanProduct_eq_elementarySymmetric]
                    ring
  have hmu0 : ∀ p ∈ (univ : Finset P), 0 ≤ mu p :=
    fun p _ ↦ (localLossMean_nonneg_le_one
      hprime ell hell0 hell1 p).1
  have hmu1 : ∀ p ∈ (univ : Finset P), mu p ≤ 1 :=
    fun p _ ↦ (localLossMean_nonneg_le_one
      hprime ell hell0 hell1 p).2
  have hscalarError :=
    bonferroni_even_error_le_pow_sum_div_factorial
      (univ : Finset P) mu hmu0 hmu1 R
  have hmeans :
      (∏ p ∈ (univ : Finset P), (1 - mu p)) =
        ∏ p : P, localWeightMean w p := by
    apply Finset.prod_congr rfl
    intro p _
    dsimp [mu]
    linarith [localWeightMean_add_localLossMean
      hprime w ell hcomplement p]
  have hscalar :
      bonferroniTruncation univ mu (2 * R + 1) ≤
        (∏ p : P, localWeightMean w p) +
          (∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ) := by
    rw [← hmeans]
    dsimp [mu] at hscalarError ⊢
    linarith
  calc
    finiteWeightBoxSum w X ≤
        ∑ x ∈ box,
          bonferroniTruncation univ (localAtNat ell x)
            (2 * R + 1) := hboxBonf
    _ ≤ 8 * (X : ℝ) ^ 2 *
            bonferroniTruncation univ mu (2 * R + 1) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) := htruncated
    _ ≤ 8 * (X : ℝ) ^ 2 *
            ((∏ p : P, localWeightMean w p) +
              (∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
                ((2 * R + 1).factorial : ℝ)) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) := by
          gcongr
    _ = _ := by ring

/-- Centered retained local family on the subtype of primes in `P`. -/
noncomputable def centeredRetainedFamily
    {P : Finset ℕ} (qU qV qSum : ℕ → ℝ)
    (p : P) (z : ZMod (p : ℕ) × ZMod (p : ℕ)) : ℝ :=
  centeredLocalWeight (qU p) (qV p) (qSum p) z

/-- Centered loss family complementary to `centeredRetainedFamily`. -/
noncomputable def centeredLossFamily
    {P : Finset ℕ} (qU qV qSum : ℕ → ℝ)
    (p : P) (z : ZMod (p : ℕ) × ZMod (p : ℕ)) : ℝ :=
  1 - centeredRetainedFamily qU qV qSum p z

/-- Cross retained local family on the subtype of primes in `P`. -/
noncomputable def crossRetainedFamily
    {P : Finset ℕ} (qU qW qLinear : ℕ → ℝ)
    (p : P) (z : ZMod (p : ℕ) × ZMod (p : ℕ)) : ℝ :=
  crossLocalWeight (qU p) (qW p) (qLinear p) z

/-- Cross loss family complementary to `crossRetainedFamily`. -/
noncomputable def crossLossFamily
    {P : Finset ℕ} (qU qW qLinear : ℕ → ℝ)
    (p : P) (z : ZMod (p : ℕ) × ZMod (p : ℕ)) : ℝ :=
  1 - crossRetainedFamily qU qW qLinear p z

theorem centeredLossFamily_support_subset_bad
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (qU qV qSum : ℕ → ℝ) (p : P) :
    residueWeightSupport (p : ℕ)
        (centeredLossFamily qU qV qSum p) ⊆
      centeredBadResidues (p : ℕ) := by
  intro z hz
  rw [mem_residueWeightSupport] at hz
  by_contra hbad
  have hU : z.1 ≠ 0 := by
    intro h
    exact hbad (by simp [centeredBadResidues, centeredZeroU, h])
  have hV : z.2 ≠ 0 := by
    intro h
    exact hbad (by simp [centeredBadResidues, centeredZeroV, h])
  have hSum : z.1 + z.2 ≠ 0 := by
    intro h
    exact hbad (by simp [centeredBadResidues, centeredZeroSum, h])
  apply hz
  simp [centeredLossFamily, centeredRetainedFamily,
    centeredLocalWeight, hU, hV, hSum]

theorem centeredLossFamily_support_card_le
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (qU qV qSum : ℕ → ℝ) (p : P) :
    (residueWeightSupport (p : ℕ)
      (centeredLossFamily qU qV qSum p)).card ≤ 3 * (p : ℕ) := by
  calc
    (residueWeightSupport (p : ℕ)
        (centeredLossFamily qU qV qSum p)).card ≤
      (centeredBadResidues (p : ℕ)).card :=
        card_le_card
          (centeredLossFamily_support_subset_bad qU qV qSum p)
    _ = 3 * (p : ℕ) - 2 := card_centeredBadResidues (p : ℕ)
    _ ≤ 3 * (p : ℕ) := Nat.sub_le _ _

theorem crossLossFamily_support_subset_bad
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (qU qW qLinear : ℕ → ℝ) (p : P) :
    residueWeightSupport (p : ℕ)
        (crossLossFamily qU qW qLinear p) ⊆
      crossBadResidues (p : ℕ) := by
  intro z hz
  rw [mem_residueWeightSupport] at hz
  by_contra hbad
  have hU : z.1 ≠ 0 := by
    intro h
    exact hbad (by simp [crossBadResidues, crossZeroU, h])
  have hW : z.2 ≠ 0 := by
    intro h
    exact hbad (by simp [crossBadResidues, crossZeroW, h])
  have hLinear : 2 * z.1 + z.2 ≠ 0 := by
    intro h
    exact hbad (by simp [crossBadResidues, crossZeroLinear, h])
  apply hz
  simp [crossLossFamily, crossRetainedFamily,
    crossLocalWeight, hU, hW, hLinear]

theorem crossLossFamily_support_card_le
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hodd : ∀ p ∈ P, p ≠ 2)
    [∀ p : P, NeZero (p : ℕ)]
    (qU qW qLinear : ℕ → ℝ) (p : P) :
    (residueWeightSupport (p : ℕ)
      (crossLossFamily qU qW qLinear p)).card ≤ 3 * (p : ℕ) := by
  calc
    (residueWeightSupport (p : ℕ)
        (crossLossFamily qU qW qLinear p)).card ≤
      (crossBadResidues (p : ℕ)).card :=
        card_le_card
          (crossLossFamily_support_subset_bad qU qW qLinear p)
    _ = 3 * (p : ℕ) - 2 :=
      card_crossBadResidues (p : ℕ)
        (hprime p p.property) (hodd p p.property)
    _ ≤ 3 * (p : ℕ) := Nat.sub_le _ _

/-- Exact normalized centered local mean used in the main term. -/
theorem localWeightMean_centeredRetainedFamily
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (qU qV qSum : ℕ → ℝ) (p : P) :
    localWeightMean
        (centeredRetainedFamily (P := P) qU qV qSum) p =
      ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
        ((p : ℝ) - 1) * (qU p + qV p + qSum p) +
        qU p * qV p * qSum p) / (p : ℝ) ^ 2 := by
  unfold localWeightMean centeredRetainedFamily
  rw [sum_centeredLocalWeight]

/-- Exact normalized cross local mean used in the main term. -/
theorem localWeightMean_crossRetainedFamily
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hodd : ∀ p ∈ P, p ≠ 2)
    [∀ p : P, NeZero (p : ℕ)]
    (qU qW qLinear : ℕ → ℝ) (p : P) :
    localWeightMean
        (crossRetainedFamily (P := P) qU qW qLinear) p =
      ((p : ℝ) ^ 2 - 3 * (p : ℝ) + 2 +
        ((p : ℝ) - 1) * (qU p + qW p + qLinear p) +
        qU p * qW p * qLinear p) / (p : ℝ) ^ 2 := by
  unfold localWeightMean crossRetainedFamily
  rw [sum_crossLocalWeight (p : ℕ)
    (hprime p p.property) (hodd p p.property)]

/-- Requested centered quantitative truncation theorem. -/
theorem centeredFiniteWeightBoxSum_le_main_add_tail_add_boundary
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (qU qV qSum : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqV0 : ∀ p ∈ P, 0 ≤ qV p) (hqV1 : ∀ p ∈ P, qV p ≤ 1)
    (hqSum0 : ∀ p ∈ P, 0 ≤ qSum p)
    (hqSum1 : ∀ p ∈ P, qSum p ≤ 1)
    (X R : ℕ) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := P) qU qV qSum) X ≤
      8 * (X : ℝ) ^ 2 *
          (∏ p : P,
            localWeightMean
              (centeredRetainedFamily (P := P) qU qV qSum) p) +
        8 * (X : ℝ) ^ 2 *
          ((∑ p : P,
              localLossMean
                (centeredLossFamily (P := P) qU qV qSum) p) ^
                (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ∑ k ∈ range (2 * R + 1),
          ∑ T ∈ (univ : Finset P).powersetCard k,
            (3 : ℝ) ^ T.card *
              (9 * (X : ℝ) + subsetModulus T) := by
  let w := centeredRetainedFamily (P := P) qU qV qSum
  let ell := centeredLossFamily (P := P) qU qV qSum
  have hlocal (p : P) (z : ZMod (p : ℕ) × ZMod (p : ℕ)) :
      0 ≤ w p z ∧ w p z ≤ 1 :=
    centeredLocalWeight_nonneg_le_one
      (qU p) (qV p) (qSum p)
      (hqU0 p p.property) (hqU1 p p.property)
      (hqV0 p p.property) (hqV1 p p.property)
      (hqSum0 p p.property) (hqSum1 p p.property) z
  exact finiteWeightBoxSum_le_main_add_tail_add_boundary
    hprime w ell
    (fun p z ↦ by simp [w, ell, centeredLossFamily])
    (fun p z ↦ sub_nonneg.mpr (hlocal p z).2)
    (fun p z ↦ sub_le_self _ (hlocal p z).1)
    (fun p ↦ centeredLossFamily_support_card_le qU qV qSum p)
    X R

/-- Requested cross quantitative truncation theorem. -/
theorem crossFiniteWeightBoxSum_le_main_add_tail_add_boundary
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hodd : ∀ p ∈ P, p ≠ 2)
    [∀ p : P, NeZero (p : ℕ)]
    (qU qW qLinear : ℕ → ℝ)
    (hqU0 : ∀ p ∈ P, 0 ≤ qU p) (hqU1 : ∀ p ∈ P, qU p ≤ 1)
    (hqW0 : ∀ p ∈ P, 0 ≤ qW p) (hqW1 : ∀ p ∈ P, qW p ≤ 1)
    (hqLinear0 : ∀ p ∈ P, 0 ≤ qLinear p)
    (hqLinear1 : ∀ p ∈ P, qLinear p ≤ 1)
    (X R : ℕ) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := P) qU qW qLinear) X ≤
      8 * (X : ℝ) ^ 2 *
          (∏ p : P,
            localWeightMean
              (crossRetainedFamily (P := P) qU qW qLinear) p) +
        8 * (X : ℝ) ^ 2 *
          ((∑ p : P,
              localLossMean
                (crossLossFamily (P := P) qU qW qLinear) p) ^
                (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ∑ k ∈ range (2 * R + 1),
          ∑ T ∈ (univ : Finset P).powersetCard k,
            (3 : ℝ) ^ T.card *
              (9 * (X : ℝ) + subsetModulus T) := by
  let w := crossRetainedFamily (P := P) qU qW qLinear
  let ell := crossLossFamily (P := P) qU qW qLinear
  have hlocal (p : P) (z : ZMod (p : ℕ) × ZMod (p : ℕ)) :
      0 ≤ w p z ∧ w p z ≤ 1 :=
    crossLocalWeight_nonneg_le_one
      (qU p) (qW p) (qLinear p)
      (hqU0 p p.property) (hqU1 p p.property)
      (hqW0 p p.property) (hqW1 p p.property)
      (hqLinear0 p p.property) (hqLinear1 p p.property) z
  exact finiteWeightBoxSum_le_main_add_tail_add_boundary
    hprime w ell
    (fun p z ↦ by simp [w, ell, crossLossFamily])
    (fun p z ↦ sub_nonneg.mpr (hlocal p z).2)
    (fun p z ↦ sub_le_self _ (hlocal p z).1)
    (fun p ↦ crossLossFamily_support_card_le
      hprime hodd qU qW qLinear p)
    X R

end Erdos327.Analytic
