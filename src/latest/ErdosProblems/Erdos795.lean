/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 795.
https://www.erdosproblems.com/forum/thread/795

Informal authors:
- Paul Erdős
- Rushil Raghavan

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos795.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 795.
https://www.erdosproblems.com/795

Informal authors:
- Paul Erdős
- Rushil Raghavan

Formal author:
- OpenAI Codex

Primary reference:
- R. Raghavan, "Sharp bounds for sets with distinct subset products",
  arXiv:2501.02695v2 (2026).
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter Finset Nat Real Asymptotics
open scoped BigOperators Topology

namespace Erdos795

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The interval `[1, N]` in which Problem 795 is posed. -/
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The product of the members of a finite set.  In particular, the empty
subset has product one. -/
def subsetProduct (S : Finset ℕ) : ℕ := ∏ n ∈ S, n

/-- A finite set has distinct subset products when the product map is
injective on its powerset. -/
def DistinctSubsetProducts (A : Finset ℕ) : Prop :=
  Set.InjOn subsetProduct (A.powerset : Set (Finset ℕ))

lemma distinctSubsetProducts_iff (A : Finset ℕ) :
    DistinctSubsetProducts A ↔
      ∀ ⦃S T : Finset ℕ⦄, S ⊆ A → T ⊆ A →
        subsetProduct S = subsetProduct T → S = T := by
  rw [DistinctSubsetProducts]
  constructor
  · intro h S T hS hT hprod
    exact h (by simpa using hS) (by simpa using hT) hprod
  · intro h S hS T hT hprod
    exact h (by simpa using hS) (by simpa using hT) hprod

lemma DistinctSubsetProducts.mono {A B : Finset ℕ}
    (hA : DistinctSubsetProducts A) (hBA : B ⊆ A) :
    DistinctSubsetProducts B := by
  rw [distinctSubsetProducts_iff] at hA ⊢
  intro S T hS hT hprod
  exact hA (hS.trans hBA) (hT.trans hBA) hprod

/-- The extremal function in Erdős Problem 795. -/
def g (N : ℕ) : ℕ :=
  ((interval N).powerset.filter DistinctSubsetProducts).sup Finset.card

lemma card_le_g {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ interval N)
    (hA : DistinctSubsetProducts A) : A.card ≤ g N := by
  exact Finset.le_sup (s := (interval N).powerset.filter DistinctSubsetProducts)
    (f := Finset.card) (by simp [hAN, hA])

lemma empty_distinctSubsetProducts : DistinctSubsetProducts (∅ : Finset ℕ) := by
  rw [distinctSubsetProducts_iff]
  simp

lemma admissible_nonempty (N : ℕ) :
    ((interval N).powerset.filter DistinctSubsetProducts).Nonempty := by
  exact ⟨∅, by simp [empty_distinctSubsetProducts]⟩

lemma exists_extremal (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ interval N ∧ DistinctSubsetProducts A ∧ A.card = g N := by
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup
    ((interval N).powerset.filter DistinctSubsetProducts)
    (admissible_nonempty N) Finset.card
  refine ⟨A, ?_, ?_, hmax.symm⟩
  · simpa using (Finset.mem_filter.mp hA).1
  · exact (Finset.mem_filter.mp hA).2

/-- The primes at most `N`. -/
def primesUpTo (N : ℕ) : Finset ℕ :=
  (interval N).filter Nat.Prime

@[simp] lemma mem_primesUpTo {N p : ℕ} :
    p ∈ primesUpTo N ↔ 1 ≤ p ∧ p ≤ N ∧ p.Prime := by
  simp [primesUpTo, interval, and_assoc]

lemma card_primesUpTo (N : ℕ) :
    (primesUpTo N).card = Nat.primeCounting N := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
  rfl

/-- Squares of primes whose square is at most `N`. -/
def primeSquaresUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo (Nat.sqrt N)).image (fun p ↦ p ^ 2)

/-- Erdős's basic construction: all primes and all prime squares in `[1,N]`. -/
def primeAndSquareSet (N : ℕ) : Finset ℕ :=
  primesUpTo N ∪ primeSquaresUpTo N

lemma primeSquaresUpTo_card (N : ℕ) :
    (primeSquaresUpTo N).card = Nat.primeCounting (Nat.sqrt N) := by
  rw [primeSquaresUpTo, Finset.card_image_of_injective]
  · exact card_primesUpTo _
  · exact Nat.pow_left_injective (by norm_num)

lemma primes_primeSquares_disjoint (N : ℕ) :
    Disjoint (primesUpTo N) (primeSquaresUpTo N) := by
  rw [Finset.disjoint_left]
  intro x hxP hxS
  rw [mem_primesUpTo] at hxP
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxS
  exact Nat.Prime.not_prime_pow (x := p) (by norm_num) hxP.2.2

lemma primeAndSquareSet_card (N : ℕ) :
    (primeAndSquareSet N).card =
      Nat.primeCounting N + Nat.primeCounting (Nat.sqrt N) := by
  rw [primeAndSquareSet, Finset.card_union_of_disjoint
    (primes_primeSquares_disjoint N), card_primesUpTo, primeSquaresUpTo_card]

lemma primeAndSquareSet_subset_interval (N : ℕ) :
    primeAndSquareSet N ⊆ interval N := by
  intro x hx
  rw [primeAndSquareSet, Finset.mem_union] at hx
  cases hx with
  | inl hx => exact (Finset.mem_filter.mp hx).1
  | inr hx =>
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [mem_primesUpTo] at hp
      rw [interval, Finset.mem_Icc]
      refine ⟨Nat.one_le_pow _ _ hp.1, ?_⟩
      exact (Nat.le_sqrt').1 hp.2.1

private lemma bit_two_injective {a b c d : ℕ}
    (ha : a ≤ 1) (_hb : b ≤ 1) (hc : c ≤ 1) (_hd : d ≤ 1)
    (h : a + 2 * b = c + 2 * d) : a = c ∧ b = d := by
  omega

lemma subsetProduct_ne_zero {S : Finset ℕ} (hS : ∀ n ∈ S, n ≠ 0) :
    subsetProduct S ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr hS

/-! The following coordinate calculation is the arithmetic heart of the
prime/prime-square lower construction. -/

private lemma factorization_member_primeAndSquareSet
    {N p n : ℕ} (hp : p.Prime) (hn : n ∈ primeAndSquareSet N) :
    n.factorization p =
      (if n = p then 1 else 0) + 2 * (if n = p ^ 2 then 1 else 0) := by
  rw [primeAndSquareSet, Finset.mem_union] at hn
  cases hn with
  | inl hnprime =>
      have hnP := (mem_primesUpTo.mp hnprime).2.2
      rw [hnP.factorization]
      simp only [Finsupp.single_apply]
      have hn_not_square : n ≠ p ^ 2 := by
        intro h
        subst n
        exact Nat.Prime.not_prime_pow (x := p) (by norm_num) hnP
      simp [hn_not_square, eq_comm]
  | inr hnsquare =>
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hnsquare
      have hqP := (mem_primesUpTo.mp hq).2.2
      rw [hqP.factorization_pow]
      have hsq_not_prime : q ^ 2 ≠ p := by
        intro h
        have : (q ^ 2).Prime := h ▸ hp
        exact Nat.Prime.not_prime_pow (x := q) (by norm_num) this
      have hsquares : q ^ 2 = p ^ 2 ↔ q = p :=
        (Nat.pow_left_injective (by norm_num)).eq_iff
      simp [Finsupp.single_apply, hsq_not_prime, hsquares, eq_comm]

lemma factorization_subsetProduct_primeAndSquareSet
    {N p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : S ⊆ primeAndSquareSet N) :
    (subsetProduct S).factorization p =
      (if p ∈ S then 1 else 0) + 2 * (if p ^ 2 ∈ S then 1 else 0) := by
  have hnonzero : ∀ n ∈ S, n ≠ 0 := by
    intro n hn
    have hnI := primeAndSquareSet_subset_interval N (hS hn)
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hnI).1
  rw [subsetProduct, Nat.factorization_prod hnonzero, Finsupp.finsetSum_apply]
  calc
    ∑ n ∈ S, n.factorization p =
        ∑ n ∈ S, ((if n = p then 1 else 0) +
          2 * (if n = p ^ 2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact factorization_member_primeAndSquareSet hp (hS hn)
    _ = (if p ∈ S then 1 else 0) +
          2 * (if p ^ 2 ∈ S then 1 else 0) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, eq_comm]

theorem primeAndSquareSet_distinctSubsetProducts (N : ℕ) :
    DistinctSubsetProducts (primeAndSquareSet N) := by
  rw [distinctSubsetProducts_iff]
  intro S T hS hT hprod
  apply Finset.ext
  intro x
  have hxA_of_S (hxS : x ∈ S) : x ∈ primeAndSquareSet N := hS hxS
  have hxA_of_T (hxT : x ∈ T) : x ∈ primeAndSquareSet N := hT hxT
  by_cases hxP : x.Prime
  · have hfac := congrArg (fun n : ℕ ↦ n.factorization x) hprod
    rw [factorization_subsetProduct_primeAndSquareSet hxP hS,
      factorization_subsetProduct_primeAndSquareSet hxP hT] at hfac
    have hbits := bit_two_injective
      (show (if x ∈ S then 1 else 0) ≤ 1 by split_ifs <;> omega)
      (show (if x ^ 2 ∈ S then 1 else 0) ≤ 1 by split_ifs <;> omega)
      (show (if x ∈ T then 1 else 0) ≤ 1 by split_ifs <;> omega)
      (show (if x ^ 2 ∈ T then 1 else 0) ≤ 1 by split_ifs <;> omega) hfac
    by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp_all
  · constructor
    · intro hxS
      have hxA := hxA_of_S hxS
      rw [primeAndSquareSet, Finset.mem_union] at hxA
      cases hxA with
      | inl hxp => exact (hxP (mem_primesUpTo.mp hxp).2.2).elim
      | inr hxsq =>
          obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hxsq
          have hpP := (mem_primesUpTo.mp hp).2.2
          subst x
          have hfac := congrArg (fun n : ℕ ↦ n.factorization p) hprod
          rw [factorization_subsetProduct_primeAndSquareSet hpP hS,
            factorization_subsetProduct_primeAndSquareSet hpP hT] at hfac
          have hbits := bit_two_injective
            (show (if p ∈ S then 1 else 0) ≤ 1 by split_ifs <;> omega)
            (show (if p ^ 2 ∈ S then 1 else 0) ≤ 1 by split_ifs <;> omega)
            (show (if p ∈ T then 1 else 0) ≤ 1 by split_ifs <;> omega)
            (show (if p ^ 2 ∈ T then 1 else 0) ≤ 1 by split_ifs <;> omega) hfac
          simpa [hxS] using hbits.2
    · intro hxT
      have hxA := hxA_of_T hxT
      rw [primeAndSquareSet, Finset.mem_union] at hxA
      cases hxA with
      | inl hxp => exact (hxP (mem_primesUpTo.mp hxp).2.2).elim
      | inr hxsq =>
          obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hxsq
          have hpP := (mem_primesUpTo.mp hp).2.2
          subst x
          have hfac := congrArg (fun n : ℕ ↦ n.factorization p) hprod
          rw [factorization_subsetProduct_primeAndSquareSet hpP hS,
            factorization_subsetProduct_primeAndSquareSet hpP hT] at hfac
          have hbits := bit_two_injective
            (show (if p ∈ S then 1 else 0) ≤ 1 by split_ifs <;> omega)
            (show (if p ^ 2 ∈ S then 1 else 0) ≤ 1 by split_ifs <;> omega)
            (show (if p ∈ T then 1 else 0) ≤ 1 by split_ifs <;> omega)
            (show (if p ^ 2 ∈ T then 1 else 0) ≤ 1 by split_ifs <;> omega) hfac
          simpa [hxT] using hbits.2.symm

theorem baseline_le_g (N : ℕ) :
    Nat.primeCounting N + Nat.primeCounting (Nat.sqrt N) ≤ g N := by
  rw [← primeAndSquareSet_card]
  exact card_le_g (primeAndSquareSet_subset_interval N)
    (primeAndSquareSet_distinctSubsetProducts N)

/-! ## The three prime ranges

The proof of the upper bound uses the integral cutoffs
`Nat.nthRoot 3 N` and `Nat.sqrt N`.  Using `Nat.nthRoot`, rather than a
real cube root followed by a floor, keeps all of the finite combinatorics
free of coercions and rounding side conditions. -/

/-- The integral cube-root cutoff. -/
def cubeRoot (N : ℕ) : ℕ := Nat.nthRoot 3 N

/-- Primes at most the integral cube root of `N`. -/
def smallPrimes (N : ℕ) : Finset ℕ := primesUpTo (cubeRoot N)

/-- Primes strictly above the cube-root cutoff and at most `sqrt N`. -/
def mediumPrimes (N : ℕ) : Finset ℕ :=
  primesUpTo (Nat.sqrt N) \ smallPrimes N

/-- Primes strictly above `sqrt N` and at most `N`. -/
def largePrimes (N : ℕ) : Finset ℕ :=
  primesUpTo N \ primesUpTo (Nat.sqrt N)

/-- All primes above the cube-root cutoff and at most `N`. -/
def highPrimes (N : ℕ) : Finset ℕ :=
  mediumPrimes N ∪ largePrimes N

lemma cubeRoot_pow_le (N : ℕ) : cubeRoot N ^ 3 ≤ N := by
  exact Nat.pow_nthRoot_le (by simp [cubeRoot])

lemma lt_succ_cubeRoot_pow (N : ℕ) : N < (cubeRoot N + 1) ^ 3 := by
  exact Nat.lt_pow_nthRoot_add_one (by norm_num) N

lemma cubeRoot_lt_iff {N p : ℕ} : cubeRoot N < p ↔ N < p ^ 3 := by
  exact Nat.nthRoot_lt_iff (by norm_num)

lemma cubeRoot_le_sqrt (N : ℕ) : cubeRoot N ≤ Nat.sqrt N := by
  by_cases hN : N = 0
  · subst N
    simp [cubeRoot]
  have hroot : cubeRoot N ^ 3 ≤ N := cubeRoot_pow_le N
  rw [Nat.le_sqrt']
  by_cases hr : cubeRoot N = 0
  · simp [hr]
  have hr1 : 1 ≤ cubeRoot N := Nat.one_le_iff_ne_zero.mpr hr
  calc
    cubeRoot N ^ 2 ≤ cubeRoot N ^ 3 := by
      exact pow_le_pow_right' hr1 (by omega)
    _ ≤ N := hroot

lemma primesUpTo_mono {M N : ℕ} (hMN : M ≤ N) :
    primesUpTo M ⊆ primesUpTo N := by
  intro p hp
  rw [mem_primesUpTo] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans hMN, hp.2.2⟩

lemma smallPrimes_subset_sqrt (N : ℕ) :
    smallPrimes N ⊆ primesUpTo (Nat.sqrt N) :=
  primesUpTo_mono (cubeRoot_le_sqrt N)

lemma sqrt_le_self (N : ℕ) : Nat.sqrt N ≤ N := Nat.sqrt_le_self N

lemma primesUpTo_sqrt_subset (N : ℕ) :
    primesUpTo (Nat.sqrt N) ⊆ primesUpTo N :=
  primesUpTo_mono (sqrt_le_self N)

@[simp] lemma mem_smallPrimes {N p : ℕ} :
    p ∈ smallPrimes N ↔ 1 ≤ p ∧ p ≤ cubeRoot N ∧ p.Prime := by
  simp [smallPrimes]

@[simp] lemma mem_mediumPrimes {N p : ℕ} :
    p ∈ mediumPrimes N ↔
      1 ≤ p ∧ cubeRoot N < p ∧ p ≤ Nat.sqrt N ∧ p.Prime := by
  simp only [mediumPrimes, Finset.mem_sdiff, mem_primesUpTo, mem_smallPrimes]
  aesop

@[simp] lemma mem_largePrimes {N p : ℕ} :
    p ∈ largePrimes N ↔
      1 ≤ p ∧ Nat.sqrt N < p ∧ p ≤ N ∧ p.Prime := by
  simp only [largePrimes, Finset.mem_sdiff, mem_primesUpTo]
  aesop

lemma mediumPrimes_disjoint_largePrimes (N : ℕ) :
    Disjoint (mediumPrimes N) (largePrimes N) := by
  rw [Finset.disjoint_left]
  intro p hpM hpL
  have hm := mem_mediumPrimes.mp hpM
  have hl := mem_largePrimes.mp hpL
  omega

lemma highPrimes_eq (N : ℕ) :
    highPrimes N = primesUpTo N \ smallPrimes N := by
  rw [highPrimes, mediumPrimes, largePrimes]
  ext p
  simp only [Finset.mem_union, Finset.mem_sdiff, mem_primesUpTo, mem_smallPrimes]
  constructor
  · rintro (⟨⟨hp1, hpsqrt, hpP⟩, hnotSmall⟩ | ⟨⟨hp1, hpN, hpP⟩, hnotsqrt⟩)
    · exact ⟨⟨hp1, hpsqrt.trans (sqrt_le_self N), hpP⟩, hnotSmall⟩
    · refine ⟨⟨hp1, hpN, hpP⟩, ?_⟩
      intro hsmall
      exact hnotsqrt ⟨hsmall.1, hsmall.2.1.trans (cubeRoot_le_sqrt N), hsmall.2.2⟩
  · rintro ⟨⟨hp1, hpN, hpP⟩, hnotSmall⟩
    by_cases hpsqrt : p ≤ Nat.sqrt N
    · exact Or.inl ⟨⟨hp1, hpsqrt, hpP⟩, hnotSmall⟩
    · exact Or.inr ⟨⟨hp1, hpN, hpP⟩, by
        rintro ⟨_, h, _⟩
        exact hpsqrt h⟩

lemma card_smallPrimes (N : ℕ) :
    (smallPrimes N).card = Nat.primeCounting (cubeRoot N) :=
  card_primesUpTo _

lemma card_mediumPrimes (N : ℕ) :
    (mediumPrimes N).card =
      Nat.primeCounting (Nat.sqrt N) - Nat.primeCounting (cubeRoot N) := by
  rw [mediumPrimes, Finset.card_sdiff_of_subset (smallPrimes_subset_sqrt N),
    card_primesUpTo, card_smallPrimes]

lemma card_largePrimes (N : ℕ) :
    (largePrimes N).card =
      Nat.primeCounting N - Nat.primeCounting (Nat.sqrt N) := by
  rw [largePrimes, Finset.card_sdiff_of_subset (primesUpTo_sqrt_subset N),
    card_primesUpTo, card_primesUpTo]

lemma card_highPrimes (N : ℕ) :
    (highPrimes N).card =
      Nat.primeCounting N - Nat.primeCounting (cubeRoot N) := by
  rw [highPrimes_eq, Finset.card_sdiff_of_subset
    ((smallPrimes_subset_sqrt N).trans (primesUpTo_sqrt_subset N)),
    card_primesUpTo, card_smallPrimes]

/-- The valuation vector on the small primes. -/
def smallValuation (N a : ℕ) : smallPrimes N → ℕ :=
  fun p ↦ a.factorization p

/-- The valuation vector on primes above the cube-root cutoff. -/
def highValuation (N a : ℕ) : highPrimes N → ℕ :=
  fun p ↦ a.factorization p

/-- The part of the factorization of `a` supported on high primes. -/
def highFactorization (N a : ℕ) : ℕ →₀ ℕ :=
  a.factorization.filter (fun p ↦ p ∈ highPrimes N)

/-- The total number of high prime factors, counted with multiplicity. -/
def highMultiplicity (N a : ℕ) : ℕ :=
  (highFactorization N a).sum (fun _ e ↦ e)

/-- The divisor of `a` made up of all its high prime factors. -/
def highPart (N a : ℕ) : ℕ :=
  (highFactorization N a).prod (fun p e ↦ p ^ e)

@[simp] lemma highFactorization_apply (N a p : ℕ) :
    highFactorization N a p = if p ∈ highPrimes N then a.factorization p else 0 :=
  rfl

lemma highFactorization_le_factorization (N a : ℕ) :
    highFactorization N a ≤ a.factorization := by
  intro p
  simp only [highFactorization_apply]
  split_ifs <;> simp

lemma highPart_dvd (N a : ℕ) : highPart N a ∣ a := by
  exact Nat.prod_pow_dvd_of_le_factorization (highFactorization_le_factorization N a)

lemma highPart_le {N a : ℕ} (ha : 0 < a) : highPart N a ≤ a :=
  Nat.le_of_dvd ha (highPart_dvd N a)

private lemma pow_sum_le_prod_pow {s : Finset ℕ} {e : ℕ → ℕ} {c : ℕ}
    (hc : ∀ p ∈ s, c ≤ p) :
    c ^ (∑ p ∈ s, e p) ≤ ∏ p ∈ s, p ^ e p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.sum_insert hp, Finset.prod_insert hp, pow_add]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (hc p (by simp)) (e p))
        (ih (fun q hq ↦ hc q (by simp [hq])))

lemma pow_highMultiplicity_le_highPart (N a : ℕ) :
    (cubeRoot N + 1) ^ highMultiplicity N a ≤ highPart N a := by
  let f := highFactorization N a
  change (cubeRoot N + 1) ^ f.sum (fun _ e ↦ e) ≤
    f.prod (fun p e ↦ p ^ e)
  rw [Finsupp.sum, Finsupp.prod]
  apply pow_sum_le_prod_pow
  intro p hp
  have hp' : p ∈ highPrimes N := by
    change p ∈ (highFactorization N a).support at hp
    rw [highFactorization, Finsupp.support_filter] at hp
    exact (Finset.mem_filter.mp hp).2
  rw [highPrimes_eq] at hp'
  have hnotSmall := (Finset.mem_sdiff.mp hp').2
  have hpPrime := (mem_primesUpTo.mp (Finset.mem_sdiff.mp hp').1).2.2
  have hcut : cubeRoot N < p := by
    by_contra h
    exact hnotSmall (mem_smallPrimes.mpr
      ⟨hpPrime.one_le, Nat.le_of_not_gt h, hpPrime⟩)
  omega

/-- A number at most `N` has at most two prime factors above `N^(1/3)`,
with multiplicity. -/
lemma highMultiplicity_le_two {N a : ℕ} (ha0 : 0 < a) (haN : a ≤ N) :
    highMultiplicity N a ≤ 2 := by
  by_contra h
  have hthree : 3 ≤ highMultiplicity N a := by omega
  have hpow : (cubeRoot N + 1) ^ 3 ≤
      (cubeRoot N + 1) ^ highMultiplicity N a := by
    exact pow_le_pow_right' (by omega) hthree
  have hpart : highPart N a ≤ a := highPart_le ha0
  have hN : (cubeRoot N + 1) ^ 3 ≤ N :=
    hpow.trans ((pow_highMultiplicity_le_highPart N a).trans (hpart.trans haN))
  exact (Nat.not_lt_of_ge hN) (lt_succ_cubeRoot_pow N)

lemma highFactorization_support_card_le_multiplicity (N a : ℕ) :
    (highFactorization N a).support.card ≤ highMultiplicity N a := by
  let f := highFactorization N a
  change f.support.card ≤ f.sum (fun _ e ↦ e)
  rw [Finsupp.sum]
  calc
    f.support.card = ∑ p ∈ f.support, 1 := by simp
    _ ≤ ∑ p ∈ f.support, f p := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)

lemma highFactorization_support_card_le_two {N a : ℕ}
    (ha0 : 0 < a) (haN : a ≤ N) :
    (highFactorization N a).support.card ≤ 2 :=
  (highFactorization_support_card_le_multiplicity N a).trans
    (highMultiplicity_le_two ha0 haN)

lemma highFactorization_support_subset (N a : ℕ) :
    (highFactorization N a).support ⊆ highPrimes N := by
  intro p hp
  rw [highFactorization, Finsupp.support_filter] at hp
  exact (Finset.mem_filter.mp hp).2

lemma highFactorization_eq_zero_iff (N a : ℕ) :
    highFactorization N a = 0 ↔ ∀ p ∈ highPrimes N, a.factorization p = 0 := by
  constructor
  · intro h p hp
    have := DFunLike.congr_fun h p
    simpa [highFactorization_apply, hp] using this
  · intro h
    ext p
    by_cases hp : p ∈ highPrimes N
    · simp [highFactorization_apply, hp, h p hp]
    · simp [highFactorization_apply, hp]

lemma highMultiplicity_eq_zero_iff (N a : ℕ) :
    highMultiplicity N a = 0 ↔ highFactorization N a = 0 := by
  let f := highFactorization N a
  change f.sum (fun _ e ↦ e) = 0 ↔ f = 0
  rw [Finsupp.sum]
  constructor
  · intro h
    rw [Finset.sum_eq_zero_iff] at h
    exact Finsupp.support_eq_empty.mp (Finset.eq_empty_iff_forall_notMem.mpr fun p hp ↦
      (Finsupp.mem_support_iff.mp hp) (h p hp))
  · intro hf
    simp [hf]

lemma highMultiplicity_pos_iff (N a : ℕ) :
    0 < highMultiplicity N a ↔ highFactorization N a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, highMultiplicity_eq_zero_iff]

lemma highFactorization_apply_eq_highValuation
    {N a : ℕ} (p : highPrimes N) :
    highFactorization N a p = highValuation N a p := by
  simp [highFactorization_apply, highValuation, p.property]

lemma highFactorization_injective_iff {N : ℕ} {A : Finset ℕ} :
    Set.InjOn (highFactorization N) A ↔ Set.InjOn (highValuation N) A := by
  constructor
  · intro h a ha b hb hab
    apply h ha hb
    ext p
    by_cases hp : p ∈ highPrimes N
    · let q : highPrimes N := ⟨p, hp⟩
      simpa [highFactorization_apply, highValuation, hp] using congrFun hab q
    · simp [highFactorization_apply, hp]
  · intro h a ha b hb hab
    apply h ha hb
    funext p
    simpa [highValuation, highFactorization_apply, p.property] using
      congrArg (fun f : ℕ →₀ ℕ ↦ f (p : ℕ)) hab

/-! ## A finite code for the small valuation vector -/

lemma interval_card (N : ℕ) : (interval N).card = N := by
  simp [interval]

lemma factorization_subsetProduct {S : Finset ℕ}
    (hS0 : ∀ n ∈ S, n ≠ 0) (p : ℕ) :
    (subsetProduct S).factorization p = ∑ n ∈ S, n.factorization p := by
  rw [subsetProduct, Nat.factorization_prod hS0, Finsupp.finsetSum_apply]

lemma factorization_subsetProduct_le_square {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ interval N) (p : ℕ) :
    (subsetProduct S).factorization p ≤ N * N := by
  have hS0 : ∀ n ∈ S, n ≠ 0 := by
    intro n hn
    exact Nat.ne_of_gt (Finset.mem_Icc.mp (hS hn)).1
  rw [factorization_subsetProduct hS0]
  calc
    ∑ n ∈ S, n.factorization p ≤ ∑ _n ∈ S, N := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Nat.factorization_lt p (hS0 n hn)).le.trans
        (Finset.mem_Icc.mp (hS hn)).2
    _ = S.card * N := by simp
    _ ≤ N * N := by
      exact Nat.mul_le_mul_right N ((Finset.card_le_card hS).trans_eq (interval_card N))

/-- The finite type used to store all small-prime coordinates of a subset
product.  The intentionally crude `N²` coordinate bound is more than enough
for the final little-`o` estimate. -/
abbrev SmallCode (N : ℕ) := smallPrimes N → Fin (N * N + 1)

def smallCode (N : ℕ) (S : Finset ℕ) (hS : S ⊆ interval N) : SmallCode N :=
  fun p ↦ ⟨(subsetProduct S).factorization p,
    Nat.lt_succ_iff.mpr (factorization_subsetProduct_le_square hS p)⟩

lemma smallCode_apply (N : ℕ) (S : Finset ℕ) (hS : S ⊆ interval N)
    (p : smallPrimes N) :
    (smallCode N S hS p : ℕ) = (subsetProduct S).factorization p :=
  rfl

lemma card_smallCode (N : ℕ) :
    Fintype.card (SmallCode N) = (N * N + 1) ^ (smallPrimes N).card := by
  change Fintype.card (smallPrimes N → Fin (N * N + 1)) = _
  rw [Fintype.card_fun]
  simp [Fintype.card_coe]

private lemma factorization_subsetProduct_eq_zero_of_gt
    {N p : ℕ} {S : Finset ℕ} (hS : S ⊆ interval N)
    (hp : N < p) : (subsetProduct S).factorization p = 0 := by
  have hS0 : ∀ n ∈ S, n ≠ 0 := by
    intro n hn
    exact Nat.ne_of_gt (Finset.mem_Icc.mp (hS hn)).1
  rw [factorization_subsetProduct hS0]
  apply Finset.sum_eq_zero
  intro n hn
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hpn
  have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (hS0 n hn)) hpn
  exact (Nat.not_lt_of_ge (hple.trans (Finset.mem_Icc.mp (hS hn)).2)) hp

/-- Small codes together with the complete high factorization determine a
subset product. -/
lemma subsetProduct_eq_of_codes {N : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ interval N) (hT : T ⊆ interval N)
    (hsmall : smallCode N S hS = smallCode N T hT)
    (hhigh : highFactorization N (subsetProduct S) =
      highFactorization N (subsetProduct T)) :
    subsetProduct S = subsetProduct T := by
  have hS0 : subsetProduct S ≠ 0 := subsetProduct_ne_zero fun n hn ↦
    Nat.ne_of_gt (Finset.mem_Icc.mp (hS hn)).1
  have hT0 : subsetProduct T ≠ 0 := subsetProduct_ne_zero fun n hn ↦
    Nat.ne_of_gt (Finset.mem_Icc.mp (hT hn)).1
  apply Nat.factorization_inj hS0 hT0
  ext p
  by_cases hpP : p.Prime
  · by_cases hpN : p ≤ N
    · by_cases hpsmall : p ≤ cubeRoot N
      · let q : smallPrimes N := ⟨p, mem_smallPrimes.mpr
          ⟨hpP.one_le, hpsmall, hpP⟩⟩
        exact congrArg (fun f : SmallCode N ↦ (f q : ℕ)) hsmall
      · have hphigh : p ∈ highPrimes N := by
          rw [highPrimes_eq, Finset.mem_sdiff]
          exact ⟨mem_primesUpTo.mpr ⟨hpP.one_le, hpN, hpP⟩,
            fun h ↦ hpsmall (mem_smallPrimes.mp h).2.1⟩
        simpa [highFactorization_apply, hphigh] using
          congrArg (fun f : ℕ →₀ ℕ ↦ f p) hhigh
    · have hpgt : N < p := Nat.lt_of_not_ge hpN
      rw [factorization_subsetProduct_eq_zero_of_gt hS hpgt,
        factorization_subsetProduct_eq_zero_of_gt hT hpgt]
  · simp [Nat.factorization_eq_zero_of_not_prime, hpP]

/-! ## Pairing the nontrivial high-valuation fibres

The compression argument needs no estimate for central binomial
coefficients.  Pair equal points inside every fibre and choose one point
from each pair.  The choices all have the same high valuation, while DSP
forces their small codes to be different. -/

structure FibrePairing {α β : Type*} [DecidableEq α]
    (A : Finset α) (f : α → β) where
  pairs : Finset (Finset α)
  pair_subset : ∀ p ∈ pairs, p ⊆ A
  pair_card : ∀ p ∈ pairs, p.card = 2
  pair_constant : ∀ p ∈ pairs, ∀ x ∈ p, ∀ y ∈ p, f x = f y
  pairwiseDisjoint : (pairs : Set (Finset α)).PairwiseDisjoint id
  remainder_injective : Set.InjOn f (A \ pairs.biUnion id)

private theorem exists_fibrePairing {α β : Type*} [DecidableEq α]
    (A : Finset α) (f : α → β) : Nonempty (FibrePairing A f) := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
      by_cases hfinj : Set.InjOn f A
      · exact ⟨⟨∅, by simp, by simp, by simp, by simp, by simpa using hfinj⟩⟩
      · simp only [Set.InjOn] at hfinj
        push_neg at hfinj
        obtain ⟨a, ha, b, hb, hab, hf⟩ := hfinj
        let p : Finset α := {a, b}
        let A' : Finset α := A \ p
        have haA' : a ∉ A' := by simp [A', p]
        have ha' : a ∈ A := by simpa using ha
        have hb' : b ∈ A := by simpa using hb
        have hpA : p ⊆ A := by
          intro x hx
          simp only [p, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ha'
          · exact hb'
        have hpnonempty : p.Nonempty := ⟨a, by simp [p]⟩
        obtain ⟨P⟩ := ih A' (Finset.sdiff_ssubset hpA hpnonempty)
        have hpcard : p.card = 2 := by simp [p, hf]
        have hpnot : p ∉ P.pairs := by
          intro hp
          have hsub := P.pair_subset p hp
          exact haA' (hsub (by simp [p]))
        refine ⟨⟨insert p P.pairs, ?_, ?_, ?_, ?_, ?_⟩⟩
        · intro q hq
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact hpA
          · exact (P.pair_subset q hq).trans Finset.sdiff_subset
        · intro q hq
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact hpcard
          · exact P.pair_card q hq
        · intro q hq x hx y hy
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · simp only [p, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            <;> simp_all
          · exact P.pair_constant q hq x hx y hy
        · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert_of_notMem hpnot]
          refine ⟨P.pairwiseDisjoint, ?_⟩
          intro q hq
          rw [Finset.disjoint_left]
          intro x hxp hxq
          have hxA' := P.pair_subset q hq hxq
          exact (Finset.mem_sdiff.mp hxA').2 hxp
        · intro x hx y hy hxy
          apply P.remainder_injective
          · change x ∈ A \ p ∧ x ∉ P.pairs.biUnion id
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_sdiff]
              refine ⟨hx.1, ?_⟩
              intro hxp
              apply hx.2
              exact Finset.mem_biUnion.mpr
                ⟨p, Finset.mem_insert_self _ _, hxp⟩
            · intro hxU
              apply hx.2
              obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hxU
              exact Finset.mem_biUnion.mpr
                ⟨q, Finset.mem_insert_of_mem hq, hxq⟩
          · change y ∈ A \ p ∧ y ∉ P.pairs.biUnion id
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_sdiff]
              refine ⟨hy.1, ?_⟩
              intro hyp
              apply hy.2
              exact Finset.mem_biUnion.mpr
                ⟨p, Finset.mem_insert_self _ _, hyp⟩
            · intro hyU
              apply hy.2
              obtain ⟨q, hq, hyq⟩ := Finset.mem_biUnion.mp hyU
              exact Finset.mem_biUnion.mpr
                ⟨q, Finset.mem_insert_of_mem hq, hyq⟩
          · exact hxy

namespace FibrePairing

variable {α β : Type*} [DecidableEq α] {A : Finset α} {f : α → β}

/-- A simultaneous choice of one point from every paired fibre. -/
abbrev Choice (P : FibrePairing A f) :=
  (p : {p // p ∈ P.pairs}) → {x // x ∈ (p : Finset α)}

/-- The set selected by a simultaneous choice. -/
def chosenSet (P : FibrePairing A f) (c : P.Choice) : Finset α :=
  P.pairs.attach.image fun p ↦ (c p : α)

lemma chosenSet_subset (P : FibrePairing A f) (c : P.Choice) :
    P.chosenSet c ⊆ A := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact P.pair_subset p p.property (c p).property

lemma choice_point_injective (P : FibrePairing A f) (c : P.Choice) :
    Function.Injective (fun p : {p // p ∈ P.pairs} ↦ (c p : α)) := by
  intro p q hpq
  apply Subtype.ext
  by_contra hne
  have hd := P.pairwiseDisjoint p.property q.property hne
  change (c p : α) = (c q : α) at hpq
  have hpqmem : (c p : α) ∈ (q : Finset α) := by
    rw [hpq]
    exact (c q).property
  exact (Finset.disjoint_left.mp hd (c p).property
    hpqmem)

lemma chosenSet_card (P : FibrePairing A f) (c : P.Choice) :
    (P.chosenSet c).card = P.pairs.card := by
  rw [chosenSet, Finset.card_image_of_injective]
  · simp
  · exact P.choice_point_injective c

lemma chosenSet_injective (P : FibrePairing A f) :
    Function.Injective P.chosenSet := by
  intro c d hcd
  funext p
  apply Subtype.ext
  have hc : (c p : α) ∈ P.chosenSet c := by
    rw [chosenSet]
    exact Finset.mem_image.mpr ⟨p, by simp, rfl⟩
  rw [hcd, chosenSet] at hc
  obtain ⟨q, _hq, hq⟩ := Finset.mem_image.mp hc
  have hpq : (p : Finset α) = (q : Finset α) := by
    by_contra hne
    have hd := P.pairwiseDisjoint p.property q.property hne
    exact Finset.disjoint_left.mp hd (c p).property
      (hq ▸ (d q).property)
  have hpq' : p = q := Subtype.ext hpq
  subst q
  exact hq.symm

lemma card_choice (P : FibrePairing A f) :
    Fintype.card P.Choice = 2 ^ P.pairs.card := by
  have hcard (p : {p // p ∈ P.pairs}) :
      Fintype.card {x // x ∈ (p : Finset α)} = 2 := by
    simpa using P.pair_card p p.property
  simp [Fintype.card_pi, hcard]

lemma support_subset (P : FibrePairing A f) :
    P.pairs.biUnion id ⊆ A := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
  exact P.pair_subset p hp hxp

lemma card_support (P : FibrePairing A f) :
    (P.pairs.biUnion id).card = 2 * P.pairs.card := by
  rw [Finset.card_biUnion P.pairwiseDisjoint]
  calc
    ∑ p ∈ P.pairs, p.card = ∑ _p ∈ P.pairs, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact P.pair_card p hp
    _ = 2 * P.pairs.card := by simp [Nat.mul_comm]

lemma card_remainder_add (P : FibrePairing A f) :
    (A \ P.pairs.biUnion id).card + 2 * P.pairs.card = A.card := by
  rw [← P.card_support]
  exact Finset.card_sdiff_add_card_eq_card P.support_subset

end FibrePairing

lemma highFactorization_subsetProduct {N : ℕ} {S : Finset ℕ}
    (hS0 : ∀ n ∈ S, n ≠ 0) :
    highFactorization N (subsetProduct S) =
      ∑ n ∈ S, highFactorization N n := by
  ext p
  by_cases hp : p ∈ highPrimes N
  · simp only [highFactorization_apply, hp, if_true, Finsupp.finsetSum_apply]
    exact factorization_subsetProduct hS0 p
  · simp [highFactorization_apply, hp]

lemma FibrePairing.highFactorization_chosenSet_eq
    {N : ℕ} {A : Finset ℕ}
    (P : FibrePairing A (highFactorization N))
    (c d : P.Choice) (hA0 : ∀ n ∈ A, n ≠ 0) :
    highFactorization N (subsetProduct (P.chosenSet c)) =
      highFactorization N (subsetProduct (P.chosenSet d)) := by
  rw [highFactorization_subsetProduct
      (fun n hn ↦ hA0 n (P.chosenSet_subset c hn)),
    highFactorization_subsetProduct
      (fun n hn ↦ hA0 n (P.chosenSet_subset d hn))]
  rw [FibrePairing.chosenSet, FibrePairing.chosenSet,
    Finset.sum_image (P.choice_point_injective c).injOn,
    Finset.sum_image (P.choice_point_injective d).injOn]
  apply Finset.sum_congr rfl
  intro p hp
  exact P.pair_constant p p.property (c p) (c p).property (d p) (d p).property

/-- Exact finite fibre-compression statement.  The discarded part has twice
the number of fibre pairs, and the DSP hypothesis injects all binary choices
into the small-code space. -/
theorem exists_highFactorization_injective_subset
    {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ interval N)
    (hA : DistinctSubsetProducts A) :
    ∃ B : Finset ℕ, ∃ k : ℕ,
      B ⊆ A ∧ Set.InjOn (highFactorization N) B ∧
      B.card + 2 * k = A.card ∧
      2 ^ k ≤ (N * N + 1) ^ (smallPrimes N).card := by
  classical
  obtain ⟨P⟩ := exists_fibrePairing A (highFactorization N)
  let B := A \ P.pairs.biUnion id
  have hBinj : Set.InjOn (highFactorization N) B := by
    simpa [B] using P.remainder_injective
  have hBcard : B.card + 2 * P.pairs.card = A.card := by
    simpa [B] using P.card_remainder_add
  refine ⟨B, P.pairs.card, Finset.sdiff_subset, hBinj, hBcard, ?_⟩
  rw [← card_smallCode N, ← P.card_choice]
  apply Fintype.card_le_of_injective
    (fun c : P.Choice ↦ smallCode N (P.chosenSet c)
      ((P.chosenSet_subset c).trans hAN))
  intro c d hcode
  apply P.chosenSet_injective
  rw [distinctSubsetProducts_iff] at hA
  apply hA (P.chosenSet_subset c) (P.chosenSet_subset d)
  apply subsetProduct_eq_of_codes
    ((P.chosenSet_subset c).trans hAN)
    ((P.chosenSet_subset d).trans hAN) hcode
  exact P.highFactorization_chosenSet_eq c d fun n hn ↦
    Nat.ne_of_gt (Finset.mem_Icc.mp (hAN hn)).1

/-- Fibre compression with the possible zero high-vector removed. -/
theorem exists_highFactorization_injective_nonzero_subset
    {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ interval N)
    (hA : DistinctSubsetProducts A) :
    ∃ B : Finset ℕ, ∃ k : ℕ,
      B ⊆ A ∧ Set.InjOn (highFactorization N) B ∧
      (∀ a ∈ B, highFactorization N a ≠ 0) ∧
      A.card ≤ B.card + 2 * k + 1 ∧
      2 ^ k ≤ (N * N + 1) ^ (smallPrimes N).card := by
  classical
  obtain ⟨C, k, hCA, hCinj, hCcard, hk⟩ :=
    exists_highFactorization_injective_subset hAN hA
  let B := C.filter fun a ↦ highFactorization N a ≠ 0
  have hBC : B ⊆ C := Finset.filter_subset _ _
  have hBinj : Set.InjOn (highFactorization N) B := hCinj.mono hBC
  have hBzero : ∀ a ∈ B, highFactorization N a ≠ 0 := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  let Z := C.filter fun a ↦ highFactorization N a = 0
  have hZle : Z.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    apply hCinj (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  have hsplit : B.card + Z.card = C.card := by
    simpa [B, Z] using
      (Finset.card_filter_add_card_filter_not
        (s := C) (fun a ↦ highFactorization N a ≠ 0))
  refine ⟨B, k, hBC.trans hCA, hBinj, hBzero, ?_, hk⟩
  omega

/-! ## Shape of a nonzero high factorization -/

/-- The exceptional type represented by an omitted square-prime vertex. -/
def IsSquareType (N a : ℕ) : Prop :=
  highMultiplicity N a = 2 ∧ (highFactorization N a).support.card = 1

lemma highFactorization_apply_le_multiplicity (N a p : ℕ) :
    highFactorization N a p ≤ highMultiplicity N a := by
  simpa [highMultiplicity] using
    (Finsupp.single_eval_le_sum (f := highFactorization N a)
      (g := id) rfl (fun _ ↦ Nat.zero_le _) p)

lemma highFactorization_apply_le_one_of_not_squareType
    {N a : ℕ} (ha0 : 0 < a) (haN : a ≤ N)
    (hnot : ¬ IsSquareType N a) (p : ℕ) :
    highFactorization N a p ≤ 1 := by
  by_cases hp0 : highFactorization N a p = 0
  · rw [hp0]
    omega
  have hp : p ∈ (highFactorization N a).support :=
    Finsupp.mem_support_iff.mpr hp0
  by_contra hp1
  have hp2 : 2 ≤ highFactorization N a p := by omega
  have hmultle := highMultiplicity_le_two ha0 haN
  have hple := highFactorization_apply_le_multiplicity N a p
  have hmult : highMultiplicity N a = 2 := by omega
  have hsupp : (highFactorization N a).support.card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨p, ?_⟩
    ext q
    constructor
    · intro hq
      rw [Finset.mem_singleton]
      by_contra hqp
      have hq1 : 1 ≤ highFactorization N a q :=
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq)
      have hpqsub : {p, q} ⊆ (highFactorization N a).support := by
        intro r hr
        rw [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact hp
        · exact hq
      have hsum : highFactorization N a p + highFactorization N a q ≤
          ∑ r ∈ (highFactorization N a).support,
            highFactorization N a r := by
        calc
          highFactorization N a p + highFactorization N a q =
              ∑ r ∈ ({p, q} : Finset ℕ), highFactorization N a r := by
                rw [Finset.sum_insert (by simpa using (Ne.symm hqp)),
                  Finset.sum_singleton]
          _ ≤ _ := Finset.sum_le_sum_of_subset hpqsub
      rw [highMultiplicity, Finsupp.sum] at hmult
      omega
    · intro hq
      have : q = p := Finset.mem_singleton.mp hq
      subst q
      exact hp
  exact hnot ⟨hmult, hsupp⟩

lemma highSupport_card_eq_one_or_two {N a : ℕ}
    (ha0 : 0 < a) (haN : a ≤ N)
    (hnonzero : highFactorization N a ≠ 0) :
    (highFactorization N a).support.card = 1 ∨
      (highFactorization N a).support.card = 2 := by
  have hpos : 0 < (highFactorization N a).support.card := by
    rw [Finset.card_pos, Finsupp.support_nonempty_iff]
    exact hnonzero
  have hle := highFactorization_support_card_le_two ha0 haN
  omega

lemma highFactorization_eq_indicator_support_of_not_squareType
    {N a : ℕ} (ha0 : 0 < a) (haN : a ≤ N)
    (hnot : ¬ IsSquareType N a) :
    highFactorization N a =
      ∑ p ∈ (highFactorization N a).support, Finsupp.single p 1 := by
  ext p
  by_cases hp : p ∈ (highFactorization N a).support
  · have hp1 : highFactorization N a p = 1 := by
      have hpos := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hle := highFactorization_apply_le_one_of_not_squareType ha0 haN hnot p
      omega
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hp, hp1]
  · have hp0 : highFactorization N a p = 0 :=
      by_contra fun h ↦ hp (Finsupp.mem_support_iff.mpr h)
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hp, hp0]

lemma one_not_mem_highFactorization_support (N a : ℕ) :
    1 ∉ (highFactorization N a).support := by
  intro h
  have hhigh := highFactorization_support_subset N a h
  rw [highPrimes_eq, Finset.mem_sdiff] at hhigh
  have hprime := (mem_primesUpTo.mp hhigh.1).2.2
  exact (Nat.not_prime_one hprime)

/-- The unordered endpoint set of a non-square element.  The number `1` is
the auxiliary graph vertex and never lies in a high-prime support. -/
def elementEdgeSet (N a : ℕ) : Finset ℕ :=
  if (highFactorization N a).support.card = 1 then
    insert 1 (highFactorization N a).support
  else (highFactorization N a).support

lemma elementEdgeSet_card {N a : ℕ}
    (ha0 : 0 < a) (haN : a ≤ N)
    (hnonzero : highFactorization N a ≠ 0)
    (hnot : ¬ IsSquareType N a) :
    (elementEdgeSet N a).card = 2 := by
  rcases highSupport_card_eq_one_or_two ha0 haN hnonzero with hcard | hcard
  · simp [elementEdgeSet, hcard, one_not_mem_highFactorization_support]
  · simp [elementEdgeSet, hcard]

lemma elementEdgeSet_erase_one (N a : ℕ) :
    (elementEdgeSet N a).erase 1 = (highFactorization N a).support := by
  by_cases hcard : (highFactorization N a).support.card = 1
  · simp [elementEdgeSet, hcard, one_not_mem_highFactorization_support]
  · simp [elementEdgeSet, hcard, one_not_mem_highFactorization_support]

private lemma exists_sym2_toFinset_eq {s : Finset ℕ} (hs : s.card = 2) :
    ∃ e : Sym2 ℕ, e.toFinset = s := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  exact ⟨s(x, y), Sym2.toFinset_mk_eq⟩

/-- The unordered graph edge attached to an element.  It is used only after
`elementEdgeSet_card` has established that the endpoint set has size two. -/
noncomputable def elementEdge (N a : ℕ) : Sym2 ℕ :=
  if h : (elementEdgeSet N a).card = 2 then
    Classical.choose (exists_sym2_toFinset_eq h)
  else s(0, 0)

lemma elementEdge_toFinset {N a : ℕ}
    (h : (elementEdgeSet N a).card = 2) :
    (elementEdge N a).toFinset = elementEdgeSet N a := by
  simp only [elementEdge, dif_pos h]
  exact Classical.choose_spec (exists_sym2_toFinset_eq h)

lemma sym2_toFinset_injective :
    Function.Injective (Sym2.toFinset : Sym2 ℕ → Finset ℕ) := by
  intro e e' h
  apply SetLike.coe_injective
  ext x
  constructor
  · intro hx
    have hx' : x ∈ e.toFinset := Sym2.mem_toFinset.mpr hx
    rw [h] at hx'
    exact Sym2.mem_toFinset.mp hx'
  · intro hx
    have hx' : x ∈ e'.toFinset := Sym2.mem_toFinset.mpr hx
    rw [← h] at hx'
    exact Sym2.mem_toFinset.mp hx'

/-- Elements represented by graph edges rather than omitted square-prime
vertices. -/
def edgeElements (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a ↦ ¬ IsSquareType N a

/-- Elements represented by omitted square-prime vertices. -/
def squareElements (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (IsSquareType N)

lemma card_edgeElements_add_squareElements (N : ℕ) (A : Finset ℕ) :
    (edgeElements N A).card + (squareElements N A).card = A.card := by
  rw [edgeElements, squareElements, add_comm]
  exact Finset.card_filter_add_card_filter_not (s := A) (IsSquareType N)

lemma elementEdge_injOn {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Set.InjOn (elementEdge N) (edgeElements N A) := by
  intro a ha b hb hab
  have haA := (Finset.mem_filter.mp ha).1
  have hbA := (Finset.mem_filter.mp hb).1
  have hanot := (Finset.mem_filter.mp ha).2
  have hbnot := (Finset.mem_filter.mp hb).2
  have haI := Finset.mem_Icc.mp (hAN haA)
  have hbI := Finset.mem_Icc.mp (hAN hbA)
  have hacard := elementEdgeSet_card haI.1 haI.2 (hnonzero a haA) hanot
  have hbcard := elementEdgeSet_card hbI.1 hbI.2 (hnonzero b hbA) hbnot
  have hedge : elementEdgeSet N a = elementEdgeSet N b := by
    rw [← elementEdge_toFinset hacard, ← elementEdge_toFinset hbcard, hab]
  have hsupp : (highFactorization N a).support =
      (highFactorization N b).support := by
    have := congrArg (fun s : Finset ℕ ↦ s.erase 1) hedge
    simpa [elementEdgeSet_erase_one] using this
  apply hinj haA hbA
  rw [highFactorization_eq_indicator_support_of_not_squareType
      haI.1 haI.2 hanot,
    highFactorization_eq_indicator_support_of_not_squareType
      hbI.1 hbI.2 hbnot,
    hsupp]

/-- The finite edge family attached to a compressed DSP set. -/
def productEdgeFinset (N : ℕ) (A : Finset ℕ) : Finset (Sym2 ℕ) :=
  (edgeElements N A).image (elementEdge N)

/-- Raghavan's prime-factorization graph. -/
def productGraph (N : ℕ) (A : Finset ℕ) : SimpleGraph ℕ :=
  SimpleGraph.fromEdgeSet (productEdgeFinset N A : Set (Sym2 ℕ))

noncomputable instance productGraph.fintypeEdgeSet (N : ℕ) (A : Finset ℕ) :
    Fintype (productGraph N A).edgeSet := by
  apply Set.Finite.fintype
  rw [productGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact (productEdgeFinset N A).finite_toSet.sdiff

lemma productEdgeFinset_card {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (productEdgeFinset N A).card = (edgeElements N A).card := by
  exact Finset.card_image_of_injOn (elementEdge_injOn hAN hinj hnonzero)

lemma productEdgeFinset_disjoint_diag {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Disjoint (productEdgeFinset N A : Set (Sym2 ℕ)) Sym2.diagSet := by
  rw [Set.disjoint_left]
  intro e he hediag
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have haA := (Finset.mem_filter.mp ha).1
  have hanot := (Finset.mem_filter.mp ha).2
  have haI := Finset.mem_Icc.mp (hAN haA)
  have hcard := elementEdgeSet_card haI.1 haI.2 (hnonzero a haA) hanot
  have hedgecard : (elementEdge N a).toFinset.card = 2 := by
    rw [elementEdge_toFinset hcard, hcard]
  have hdiag : (elementEdge N a).IsDiag := by
    simpa only [Sym2.mem_diagSet] using hediag
  have := Sym2.card_toFinset_of_isDiag (elementEdge N a) hdiag
  omega

lemma productGraph_edgeSet {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (productGraph N A).edgeSet =
      (productEdgeFinset N A : Set (Sym2 ℕ)) := by
  rw [productGraph, SimpleGraph.edgeSet_fromEdgeSet,
    (productEdgeFinset_disjoint_diag hAN hnonzero).sdiff_eq_left]

lemma productGraph_edgeFinset {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (productGraph N A).edgeFinset = productEdgeFinset N A := by
  apply Finset.coe_injective
  simpa [productGraph_edgeSet hAN hnonzero]

lemma productGraph_card_edges_add_squares {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (productGraph N A).edgeFinset.card + (squareElements N A).card = A.card := by
  rw [productGraph_edgeFinset hAN hnonzero,
    productEdgeFinset_card hAN hinj hnonzero]
  exact card_edgeElements_add_squareElements N A

/-! ## Square-prime vertices and the large-prime restriction -/

/-- The unique high prime supporting a square-type element. -/
noncomputable def squarePrime (N a : ℕ) : ℕ :=
  if h : (highFactorization N a).support.Nonempty then
    (highFactorization N a).support.min' h
  else 0

lemma squarePrime_mem_support {N a : ℕ} (ha : IsSquareType N a) :
    squarePrime N a ∈ (highFactorization N a).support := by
  have hcardpos : 0 < (highFactorization N a).support.card := by
    rw [ha.2]
    exact Nat.zero_lt_one
  have hne : (highFactorization N a).support.Nonempty :=
    Finset.card_pos.mp hcardpos
  simp only [squarePrime, dif_pos hne]
  exact Finset.min'_mem _ _

lemma highFactorization_eq_single_squarePrime {N a : ℕ}
    (ha : IsSquareType N a) :
    highFactorization N a = Finsupp.single (squarePrime N a) 2 := by
  let p := squarePrime N a
  have hp : p ∈ (highFactorization N a).support := squarePrime_mem_support ha
  have hsupp : (highFactorization N a).support = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    exact (Finset.card_le_one.mp ha.2.le) q hq p hp
  have hvalue : highFactorization N a p = 2 := by
    have hmult := ha.1
    rw [highMultiplicity, Finsupp.sum, hsupp, Finset.sum_singleton] at hmult
    exact hmult
  exact (Finsupp.support_eq_singleton.mp hsupp).2.trans
    (congrArg (Finsupp.single p) hvalue)

lemma squarePrime_mem_mediumPrimes {N a : ℕ}
    (haI : a ∈ interval N) (ha : IsSquareType N a) :
    squarePrime N a ∈ mediumPrimes N := by
  let p := squarePrime N a
  have hpSupp : p ∈ (highFactorization N a).support := squarePrime_mem_support ha
  have hpHigh : p ∈ highPrimes N := highFactorization_support_subset N a hpSupp
  have hpRange := hpHigh
  rw [highPrimes] at hpRange
  rcases Finset.mem_union.mp hpRange with hpMed | hpLarge
  · exact hpMed
  · exfalso
    have haBounds := Finset.mem_Icc.mp haI
    have hpData := mem_largePrimes.mp hpLarge
    have hfactor := highFactorization_eq_single_squarePrime ha
    have hpval := congrArg (fun f : ℕ →₀ ℕ ↦ f p) hfactor
    have hfac : a.factorization p = 2 := by
      simpa [highFactorization_apply, hpHigh, p] using hpval
    have hdvd : p ^ 2 ∣ a :=
      (hpData.2.2.2.pow_dvd_iff_le_factorization
        (Nat.ne_of_gt haBounds.1)).mpr (by omega)
    have hle : p ^ 2 ≤ a := Nat.le_of_dvd haBounds.1 hdvd
    have hgt : N < p ^ 2 := Nat.sqrt_lt'.mp hpData.2.1
    omega

def squarePrimeSet (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (squareElements N A).image (squarePrime N)

/-- The square-type element corresponding to a vertex of `squarePrimeSet`.
It is only used under a membership hypothesis. -/
noncomputable def squareElementLabel (N : ℕ) (A : Finset ℕ) (p : ℕ) : ℕ :=
  if h : p ∈ squarePrimeSet N A then
    Classical.choose (Finset.mem_image.mp h)
  else 0

lemma squareElementLabel_mem {N : ℕ} {A : Finset ℕ} {p : ℕ}
    (hp : p ∈ squarePrimeSet N A) :
    squareElementLabel N A p ∈ squareElements N A := by
  simp only [squareElementLabel, dif_pos hp]
  exact (Classical.choose_spec (Finset.mem_image.mp hp)).1

lemma squarePrime_squareElementLabel {N : ℕ} {A : Finset ℕ} {p : ℕ}
    (hp : p ∈ squarePrimeSet N A) :
    squarePrime N (squareElementLabel N A p) = p := by
  simp only [squareElementLabel, dif_pos hp]
  exact (Classical.choose_spec (Finset.mem_image.mp hp)).2

lemma highFactorization_squareElementLabel {N : ℕ} {A : Finset ℕ} {p : ℕ}
    (hp : p ∈ squarePrimeSet N A) :
    highFactorization N (squareElementLabel N A p) =
      Finsupp.single p 2 := by
  have ha := squareElementLabel_mem hp
  rw [highFactorization_eq_single_squarePrime (Finset.mem_filter.mp ha).2,
    squarePrime_squareElementLabel hp]

lemma squarePrime_injOn {N : ℕ} {A : Finset ℕ}
    (hinj : Set.InjOn (highFactorization N) A) :
    Set.InjOn (squarePrime N) (squareElements N A) := by
  intro a ha b hb hab
  have haA := (Finset.mem_filter.mp ha).1
  have hbA := (Finset.mem_filter.mp hb).1
  have haSq := (Finset.mem_filter.mp ha).2
  have hbSq := (Finset.mem_filter.mp hb).2
  apply hinj haA hbA
  rw [highFactorization_eq_single_squarePrime haSq,
    highFactorization_eq_single_squarePrime hbSq, hab]

lemma squarePrimeSet_card {N : ℕ} {A : Finset ℕ}
    (hinj : Set.InjOn (highFactorization N) A) :
    (squarePrimeSet N A).card = (squareElements N A).card := by
  exact Finset.card_image_of_injOn (squarePrime_injOn hinj)

lemma squarePrimeSet_subset_medium {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N) :
    squarePrimeSet N A ⊆ mediumPrimes N := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  exact squarePrime_mem_mediumPrimes (hAN (Finset.mem_filter.mp ha).1)
    (Finset.mem_filter.mp ha).2

lemma squareElements_card_le_medium {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A) :
    (squareElements N A).card ≤ (mediumPrimes N).card := by
  rw [← squarePrimeSet_card hinj]
  exact Finset.card_le_card (squarePrimeSet_subset_medium hAN)

lemma two_large_primes_not_both_in_support {N a p q : ℕ}
    (haI : a ∈ interval N) (hp : p ∈ largePrimes N)
    (hq : q ∈ largePrimes N) (hpq : p ≠ q) :
    ¬ (p ∈ (highFactorization N a).support ∧
      q ∈ (highFactorization N a).support) := by
  rintro ⟨hps, hqs⟩
  have haBounds := Finset.mem_Icc.mp haI
  have hpData := mem_largePrimes.mp hp
  have hqData := mem_largePrimes.mp hq
  have hpHigh : p ∈ highPrimes N := by
    exact Finset.mem_union_right _ hp
  have hqHigh : q ∈ highPrimes N := by
    exact Finset.mem_union_right _ hq
  have hpfac : a.factorization p ≠ 0 := by
    have := Finsupp.mem_support_iff.mp hps
    simpa [highFactorization_apply, hpHigh] using this
  have hqfac : a.factorization q ≠ 0 := by
    have := Finsupp.mem_support_iff.mp hqs
    simpa [highFactorization_apply, hqHigh] using this
  have hpdiv : p ∣ a := Nat.dvd_of_factorization_pos hpfac
  have hqdiv : q ∣ a := Nat.dvd_of_factorization_pos hqfac
  have hpqdiv : p * q ∣ a :=
    hpData.2.2.2.dvd_mul_of_dvd_ne hpq hqData.2.2.2 hpdiv hqdiv
  have hprodle : p * q ≤ a := Nat.le_of_dvd haBounds.1 hpqdiv
  have hpLower : Nat.sqrt N + 1 ≤ p := by omega
  have hqLower : Nat.sqrt N + 1 ≤ q := by omega
  have hNprod : N < p * q :=
    (Nat.lt_succ_sqrt N).trans_le (Nat.mul_le_mul hpLower hqLower)
  omega

lemma productGraph_no_adj_large_large {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {p q : ℕ} (hp : p ∈ largePrimes N) (hq : q ∈ largePrimes N) :
    ¬ (productGraph N A).Adj p q := by
  intro hadj
  have hadj' := hadj
  rw [productGraph, SimpleGraph.fromEdgeSet_adj] at hadj'
  obtain ⟨a, ha, hedge⟩ := Finset.mem_image.mp hadj'.1
  have haA := (Finset.mem_filter.mp ha).1
  have hanot := (Finset.mem_filter.mp ha).2
  have haBounds := Finset.mem_Icc.mp (hAN haA)
  have hacard := elementEdgeSet_card haBounds.1 haBounds.2
    (hnonzero a haA) hanot
  have hset : elementEdgeSet N a = {p, q} := by
    rw [← elementEdge_toFinset hacard, hedge, Sym2.toFinset_mk_eq]
  have hpPrime := (mem_largePrimes.mp hp).2.2.2
  have hqPrime := (mem_largePrimes.mp hq).2.2.2
  have hps : p ∈ (highFactorization N a).support := by
    rw [← elementEdgeSet_erase_one]
    exact Finset.mem_erase.mpr ⟨hpPrime.ne_one, hset.symm ▸ (by simp)⟩
  have hqs : q ∈ (highFactorization N a).support := by
    rw [← elementEdgeSet_erase_one]
    exact Finset.mem_erase.mpr ⟨hqPrime.ne_one, hset.symm ▸ (by simp)⟩
  exact two_large_primes_not_both_in_support (hAN haA) hp hq hadj'.2
    ⟨hps, hqs⟩

/-! ## Alternating incidence on an even closed walk -/

namespace SimpleGraph.Walk

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The endpoint-incidence vector of an unordered edge. -/
def edgeIncidence (e : Sym2 V) : V →₀ ℕ :=
  e.toFinset.sum fun v ↦ Finsupp.single v 1

mutual
  /-- Incidences of the edges in even positions of an edge list. -/
  def evenIncidenceList : List (Sym2 V) → V →₀ ℕ
    | [] => 0
    | e :: es => edgeIncidence e + oddIncidenceList es

  /-- Incidences of the edges in odd positions of an edge list. -/
  def oddIncidenceList : List (Sym2 V) → V →₀ ℕ
    | [] => 0
    | _ :: es => evenIncidenceList es
end

/-- Incidences of the edges in even positions of a walk. -/
def evenIncidence {u v : V} (w : G.Walk u v) : V →₀ ℕ :=
  evenIncidenceList w.edges

/-- Incidences of the edges in odd positions of a walk. -/
def oddIncidence {u v : V} (w : G.Walk u v) : V →₀ ℕ :=
  oddIncidenceList w.edges

lemma edgeIncidence_mk {u v : V} (h : u ≠ v) :
    edgeIncidence s(u, v) = Finsupp.single u 1 + Finsupp.single v 1 := by
  simp [edgeIncidence, Sym2.toFinset_mk_eq, h]

/-- Telescoping for alternating endpoint incidences. -/
lemma alternatingIncidence_balance {u v : V} (w : G.Walk u v) :
    (Even w.length →
      evenIncidence w + Finsupp.single v 1 =
        oddIncidence w + Finsupp.single u 1) ∧
    (Odd w.length →
      evenIncidence w =
        oddIncidence w + Finsupp.single u 1 + Finsupp.single v 1) := by
  induction w with
  | nil =>
      constructor
      · intro _
        simp [evenIncidence, oddIncidence, evenIncidenceList, oddIncidenceList]
      · intro hodd
        simpa using hodd
  | @cons u v z huv p ih =>
      constructor
      · intro heven
        have hpodd : Odd p.length := by
          simpa [SimpleGraph.Walk.length_cons, Nat.even_add_one,
            Nat.not_even_iff_odd] using heven
        have hih := ih.2 hpodd
        simp only [evenIncidence, oddIncidence, SimpleGraph.Walk.edges_cons,
          evenIncidenceList, oddIncidenceList, edgeIncidence_mk huv.ne]
        calc
          (Finsupp.single u 1 + Finsupp.single v 1 + oddIncidence p) +
                Finsupp.single z 1 =
              (oddIncidence p + Finsupp.single v 1 + Finsupp.single z 1) +
                Finsupp.single u 1 := by ac_rfl
          _ = evenIncidence p + Finsupp.single u 1 := by rw [← hih]
      · intro hodd
        have hpeven : Even p.length := by
          simpa [SimpleGraph.Walk.length_cons, Nat.odd_add_one,
            Nat.not_odd_iff_even] using hodd
        have hih := ih.1 hpeven
        simp only [evenIncidence, oddIncidence, SimpleGraph.Walk.edges_cons,
          evenIncidenceList, oddIncidenceList, edgeIncidence_mk huv.ne]
        calc
          Finsupp.single u 1 + Finsupp.single v 1 + oddIncidence p =
              (oddIncidence p + Finsupp.single v 1) + Finsupp.single u 1 := by
                ac_rfl
          _ = (evenIncidence p + Finsupp.single z 1) +
                Finsupp.single u 1 := by rw [← hih]
          _ = evenIncidence p + Finsupp.single u 1 +
                Finsupp.single z 1 := by ac_rfl

lemma evenIncidence_eq_oddIncidence_of_closed
    {u : V} {w : G.Walk u u} (heven : Even w.length) :
    evenIncidence w = oddIncidence w := by
  have h := (alternatingIncidence_balance w).1 heven
  exact add_right_cancel h

end SimpleGraph.Walk

/-! ## Recovering multiplicative labels from graph edges -/

/-- The unique retained element labelling an edge of `productGraph`. -/
noncomputable def edgeLabel (N : ℕ) (A : Finset ℕ) (e : Sym2 ℕ) : ℕ :=
  if h : e ∈ productEdgeFinset N A then
    Classical.choose (Finset.mem_image.mp h)
  else 0

lemma edgeLabel_mem {N : ℕ} {A : Finset ℕ} {e : Sym2 ℕ}
    (he : e ∈ productEdgeFinset N A) :
    edgeLabel N A e ∈ edgeElements N A := by
  simp only [edgeLabel, dif_pos he]
  exact (Classical.choose_spec (Finset.mem_image.mp he)).1

lemma elementEdge_edgeLabel {N : ℕ} {A : Finset ℕ} {e : Sym2 ℕ}
    (he : e ∈ productEdgeFinset N A) :
    elementEdge N (edgeLabel N A e) = e := by
  simp only [edgeLabel, dif_pos he]
  exact (Classical.choose_spec (Finset.mem_image.mp he)).2

lemma edgeLabel_injOn (N : ℕ) (A : Finset ℕ) :
    Set.InjOn (edgeLabel N A) (productEdgeFinset N A) := by
  intro e he e' he' h
  rw [← elementEdge_edgeLabel he, ← elementEdge_edgeLabel he', h]

/-- Delete the auxiliary coordinate `1` from an incidence vector. -/
def withoutAux (f : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  f.filter fun p ↦ p ≠ 1

lemma withoutAux_add (f g : ℕ →₀ ℕ) :
    withoutAux (f + g) = withoutAux f + withoutAux g := by
  ext p
  by_cases hp : p ≠ 1 <;> simp [withoutAux, hp]

lemma withoutAux_edgeIncidence_elementEdge {N a : ℕ}
    (ha0 : 0 < a) (haN : a ≤ N)
    (hnonzero : highFactorization N a ≠ 0)
    (hnot : ¬ IsSquareType N a) :
    withoutAux (SimpleGraph.Walk.edgeIncidence (elementEdge N a)) =
      highFactorization N a := by
  have hcard := elementEdgeSet_card ha0 haN hnonzero hnot
  ext p
  by_cases hp1 : p = 1
  · subst p
    have hone : highFactorization N a 1 = 0 := by
      by_contra h
      exact one_not_mem_highFactorization_support N a
        (Finsupp.mem_support_iff.mpr h)
    simp [withoutAux, hone]
  · have hmem : p ∈ elementEdgeSet N a ↔
        p ∈ (highFactorization N a).support := by
      constructor
      · intro hp
        have : p ∈ (elementEdgeSet N a).erase 1 :=
          Finset.mem_erase.mpr ⟨hp1, hp⟩
        simpa [elementEdgeSet_erase_one] using this
      · intro hp
        have : p ∈ (elementEdgeSet N a).erase 1 := by
          simpa [elementEdgeSet_erase_one] using hp
        exact Finset.mem_of_mem_erase this
    by_cases hps : p ∈ (highFactorization N a).support
    · have hpvalue : highFactorization N a p = 1 := by
        have hpos := Nat.one_le_iff_ne_zero.mpr
          (Finsupp.mem_support_iff.mp hps)
        have hle := highFactorization_apply_le_one_of_not_squareType
          ha0 haN hnot p
        omega
      simp [withoutAux, hp1, SimpleGraph.Walk.edgeIncidence,
        Finsupp.finsetSum_apply, Finsupp.single_apply,
        elementEdge_toFinset hcard, hmem.mpr hps, hpvalue]
    · have hpvalue : highFactorization N a p = 0 := by
        by_contra h
        exact hps (Finsupp.mem_support_iff.mpr h)
      simp [withoutAux, hp1, SimpleGraph.Walk.edgeIncidence,
        Finsupp.finsetSum_apply, Finsupp.single_apply,
        elementEdge_toFinset hcard, hmem, hps, hpvalue]

lemma withoutAux_edgeIncidence_edgeLabel
    {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {e : Sym2 ℕ} (he : e ∈ productEdgeFinset N A) :
    withoutAux (SimpleGraph.Walk.edgeIncidence e) =
      highFactorization N (edgeLabel N A e) := by
  have ha := edgeLabel_mem he
  have haA := (Finset.mem_filter.mp ha).1
  have hnot := (Finset.mem_filter.mp ha).2
  have haI := Finset.mem_Icc.mp (hAN haA)
  calc
    withoutAux (SimpleGraph.Walk.edgeIncidence e) =
        withoutAux (SimpleGraph.Walk.edgeIncidence
          (elementEdge N (edgeLabel N A e))) := by
            rw [elementEdge_edgeLabel he]
    _ = highFactorization N (edgeLabel N A e) :=
      withoutAux_edgeIncidence_elementEdge haI.1 haI.2
        (hnonzero _ haA) hnot

/-! ## Alternating edge sets of a trail -/

mutual
  def evenTerms {α : Type*} : List α → List α
    | [] => []
    | x :: xs => x :: oddTerms xs

  def oddTerms {α : Type*} : List α → List α
    | [] => []
    | _ :: xs => evenTerms xs
end

mutual
  lemma evenTerms_sublist {α : Type*} (l : List α) :
      List.Sublist (evenTerms l) l := by
    cases l with
    | nil => simp [evenTerms]
    | cons x xs =>
        exact List.Sublist.cons_cons x (oddTerms_sublist xs)

  lemma oddTerms_sublist {α : Type*} (l : List α) :
      List.Sublist (oddTerms l) l := by
    cases l with
    | nil => simp [oddTerms]
    | cons x xs =>
        exact (evenTerms_sublist xs).cons _
end

lemma evenTerms_nodup {α : Type*} {l : List α} (h : l.Nodup) :
    (evenTerms l).Nodup := (evenTerms_sublist l).nodup h

lemma oddTerms_nodup {α : Type*} {l : List α} (h : l.Nodup) :
    (oddTerms l).Nodup := (oddTerms_sublist l).nodup h

lemma evenTerms_disjoint_oddTerms {α : Type*} {l : List α} (h : l.Nodup) :
    List.Disjoint (evenTerms l) (oddTerms l) := by
  induction l with
  | nil => simp [evenTerms, oddTerms]
  | cons x xs ih =>
      rw [List.nodup_cons] at h
      have hdis := ih h.2
      simp only [evenTerms, oddTerms, List.disjoint_cons_left]
      exact ⟨fun hx ↦ h.1 ((evenTerms_sublist xs).subset hx), hdis.symm⟩

lemma length_evenTerms_add_length_oddTerms {α : Type*} (l : List α) :
    (evenTerms l).length + (oddTerms l).length = l.length := by
  induction l with
  | nil => simp [evenTerms, oddTerms]
  | cons x xs ih =>
      simp only [evenTerms, oddTerms, List.length_cons]
      omega

lemma evenTerms_nonempty_of_ne_nil {α : Type*} {l : List α}
    (hl : l ≠ []) : ∃ x, x ∈ evenTerms l := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons x xs => exact ⟨x, by simp [evenTerms]⟩

lemma oddTerms_nonempty_of_two_le_length {α : Type*} {l : List α}
    (hl : 2 ≤ l.length) : ∃ x, x ∈ oddTerms l := by
  cases l with
  | nil => simp at hl
  | cons x xs =>
      cases xs with
      | nil => simp at hl
      | cons y ys => exact ⟨y, by simp [oddTerms, evenTerms]⟩

mutual
  lemma evenIncidenceList_eq_sum_evenTerms
      {V : Type*} [DecidableEq V] (l : List (Sym2 V)) :
      SimpleGraph.Walk.evenIncidenceList l =
        ((evenTerms l).map SimpleGraph.Walk.edgeIncidence).sum := by
    cases l with
    | nil => simp [SimpleGraph.Walk.evenIncidenceList, evenTerms]
    | cons e es =>
        simp [SimpleGraph.Walk.evenIncidenceList, evenTerms,
          oddIncidenceList_eq_sum_oddTerms es]

  lemma oddIncidenceList_eq_sum_oddTerms
      {V : Type*} [DecidableEq V] (l : List (Sym2 V)) :
      SimpleGraph.Walk.oddIncidenceList l =
        ((oddTerms l).map SimpleGraph.Walk.edgeIncidence).sum := by
    cases l with
    | nil => simp [SimpleGraph.Walk.oddIncidenceList, oddTerms]
    | cons e es =>
        simp [SimpleGraph.Walk.oddIncidenceList, oddTerms,
          evenIncidenceList_eq_sum_evenTerms es]
end

namespace SimpleGraph.Walk.IsTrail

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  {u v : V} {w : G.Walk u v}

def evenEdgesFinset (h : w.IsTrail) : Finset (Sym2 V) :=
  ⟨evenTerms w.edges, evenTerms_nodup h.edges_nodup⟩

def oddEdgesFinset (h : w.IsTrail) : Finset (Sym2 V) :=
  ⟨oddTerms w.edges, oddTerms_nodup h.edges_nodup⟩

lemma evenEdgesFinset_disjoint_oddEdgesFinset (h : w.IsTrail) :
    Disjoint (evenEdgesFinset h) (oddEdgesFinset h) := by
  rw [Finset.disjoint_left]
  intro e he ho
  exact (evenTerms_disjoint_oddTerms h.edges_nodup) he ho

lemma evenIncidence_eq_sum (h : w.IsTrail) :
    SimpleGraph.Walk.evenIncidence w =
      ∑ e ∈ evenEdgesFinset h, SimpleGraph.Walk.edgeIncidence e := by
  change SimpleGraph.Walk.evenIncidenceList w.edges =
    ((evenTerms w.edges).map SimpleGraph.Walk.edgeIncidence).sum
  exact evenIncidenceList_eq_sum_evenTerms w.edges

lemma oddIncidence_eq_sum (h : w.IsTrail) :
    SimpleGraph.Walk.oddIncidence w =
      ∑ e ∈ oddEdgesFinset h, SimpleGraph.Walk.edgeIncidence e := by
  change SimpleGraph.Walk.oddIncidenceList w.edges =
    ((oddTerms w.edges).map SimpleGraph.Walk.edgeIncidence).sum
  exact oddIncidenceList_eq_sum_oddTerms w.edges

end SimpleGraph.Walk.IsTrail

lemma withoutAux_finset_sum {s : Finset (Sym2 ℕ)}
    (f : Sym2 ℕ → ℕ →₀ ℕ) :
    withoutAux (∑ e ∈ s, f e) = ∑ e ∈ s, withoutAux (f e) := by
  induction s using Finset.induction_on with
  | empty =>
      ext p
      change (if p ≠ 1 then (0 : ℕ) else 0) = 0
      split <;> rfl
  | @insert e s he ih =>
      simp [Finset.sum_insert he, withoutAux_add, ih]

/-! ## Multiplicative relations furnished by even circuits -/

/-- The edges in even positions of a circuit, translated back to the
elements of the compressed set that label them. -/
noncomputable def evenLabelSet {N : ℕ} {A : Finset ℕ} {u v : ℕ}
    (w : (productGraph N A).Walk u v) (h : w.IsTrail) : Finset ℕ :=
  (SimpleGraph.Walk.IsTrail.evenEdgesFinset h).image (edgeLabel N A)

/-- The edges in odd positions of a circuit, translated back to the
elements of the compressed set that label them. -/
noncomputable def oddLabelSet {N : ℕ} {A : Finset ℕ} {u v : ℕ}
    (w : (productGraph N A).Walk u v) (h : w.IsTrail) : Finset ℕ :=
  (SimpleGraph.Walk.IsTrail.oddEdgesFinset h).image (edgeLabel N A)

/-- Every edge occurring in a walk in `productGraph` belongs to the finite
edge family used to define that graph. -/
lemma walk_edge_mem_productEdgeFinset {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) {e : Sym2 ℕ}
    (he : e ∈ w.edges) : e ∈ productEdgeFinset N A := by
  have he' : e ∈ (productGraph N A).edgeSet := w.edges_subset_edgeSet he
  rwa [productGraph_edgeSet hAN hnonzero] at he'

lemma evenLabelSet_subset {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail) :
    evenLabelSet w h ⊆ A := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  have hew : e ∈ w.edges :=
    (evenTerms_sublist w.edges).subset he
  exact (Finset.mem_filter.mp
    (edgeLabel_mem (walk_edge_mem_productEdgeFinset hAN hnonzero w hew))).1

lemma oddLabelSet_subset {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail) :
    oddLabelSet w h ⊆ A := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  have hew : e ∈ w.edges :=
    (oddTerms_sublist w.edges).subset he
  exact (Finset.mem_filter.mp
    (edgeLabel_mem (walk_edge_mem_productEdgeFinset hAN hnonzero w hew))).1

lemma labelSet_disjoint {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail) :
    Disjoint (evenLabelSet w h) (oddLabelSet w h) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨f, hf, hef⟩ := Finset.mem_image.mp hb
  have hew : e ∈ w.edges := (evenTerms_sublist w.edges).subset he
  have hfw : f ∈ w.edges := (oddTerms_sublist w.edges).subset hf
  have heP := walk_edge_mem_productEdgeFinset hAN hnonzero w hew
  have hfP := walk_edge_mem_productEdgeFinset hAN hnonzero w hfw
  have hfe : f = e := edgeLabel_injOn N A hfP heP hef
  subst f
  exact (Finset.disjoint_left.mp
    (SimpleGraph.Walk.IsTrail.evenEdgesFinset_disjoint_oddEdgesFinset h)) he hf

lemma evenLabelSet_nonempty_of_isCircuit {N : ℕ} {A : Finset ℕ}
    {u : ℕ} {w : (productGraph N A).Walk u u} (h : w.IsCircuit) :
    (evenLabelSet w h.isTrail).Nonempty := by
  have hwne : w.edges ≠ [] := by
    intro hw
    have hlen := h.three_le_length
    rw [← w.length_edges, hw] at hlen
    simp at hlen
  obtain ⟨e, he⟩ := evenTerms_nonempty_of_ne_nil hwne
  exact ⟨edgeLabel N A e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩

lemma oddLabelSet_nonempty_of_isCircuit {N : ℕ} {A : Finset ℕ}
    {u : ℕ} {w : (productGraph N A).Walk u u} (h : w.IsCircuit) :
    (oddLabelSet w h.isTrail).Nonempty := by
  have htwo : 2 ≤ w.edges.length := by
    rw [w.length_edges]
    exact le_trans (by omega) h.three_le_length
  obtain ⟨e, he⟩ := oddTerms_nonempty_of_two_le_length htwo
  exact ⟨edgeLabel N A e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩

lemma evenLabelSet_card_add_oddLabelSet_card {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail) :
    (evenLabelSet w h).card + (oddLabelSet w h).card = w.length := by
  have heP : (SimpleGraph.Walk.IsTrail.evenEdgesFinset h : Set (Sym2 ℕ)) ⊆
      productEdgeFinset N A := by
    intro e he
    exact walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((evenTerms_sublist w.edges).subset he)
  have hoP : (SimpleGraph.Walk.IsTrail.oddEdgesFinset h : Set (Sym2 ℕ)) ⊆
      productEdgeFinset N A := by
    intro e he
    exact walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((oddTerms_sublist w.edges).subset he)
  rw [evenLabelSet, oddLabelSet,
    (Finset.card_image_iff.mpr ((edgeLabel_injOn N A).mono heP)),
    (Finset.card_image_iff.mpr ((edgeLabel_injOn N A).mono hoP))]
  change (evenTerms w.edges).length + (oddTerms w.edges).length = w.length
  rw [length_evenTerms_add_length_oddTerms, w.length_edges]

lemma highFactorization_sum_evenLabelSet_eq_withoutAux
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail) :
    (∑ a ∈ evenLabelSet w h, highFactorization N a) =
      withoutAux (SimpleGraph.Walk.evenIncidence w) := by
  let E := SimpleGraph.Walk.IsTrail.evenEdgesFinset h
  have heP : (E : Set (Sym2 ℕ)) ⊆ productEdgeFinset N A := by
    intro e he
    exact walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((evenTerms_sublist w.edges).subset he)
  rw [evenLabelSet, Finset.sum_image ((edgeLabel_injOn N A).mono heP)]
  calc
    (∑ e ∈ E, highFactorization N (edgeLabel N A e)) =
        ∑ e ∈ E, withoutAux (SimpleGraph.Walk.edgeIncidence e) := by
          apply Finset.sum_congr rfl
          intro e he
          exact (withoutAux_edgeIncidence_edgeLabel hAN hnonzero (heP he)).symm
    _ = withoutAux (∑ e ∈ E, SimpleGraph.Walk.edgeIncidence e) :=
      (withoutAux_finset_sum _).symm
    _ = withoutAux (SimpleGraph.Walk.evenIncidence w) := by
      rw [SimpleGraph.Walk.IsTrail.evenIncidence_eq_sum h]

lemma highFactorization_sum_oddLabelSet_eq_withoutAux
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail) :
    (∑ a ∈ oddLabelSet w h, highFactorization N a) =
      withoutAux (SimpleGraph.Walk.oddIncidence w) := by
  let O := SimpleGraph.Walk.IsTrail.oddEdgesFinset h
  have hoP : (O : Set (Sym2 ℕ)) ⊆ productEdgeFinset N A := by
    intro e he
    exact walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((oddTerms_sublist w.edges).subset he)
  rw [oddLabelSet, Finset.sum_image ((edgeLabel_injOn N A).mono hoP)]
  calc
    (∑ e ∈ O, highFactorization N (edgeLabel N A e)) =
        ∑ e ∈ O, withoutAux (SimpleGraph.Walk.edgeIncidence e) := by
          apply Finset.sum_congr rfl
          intro e he
          exact (withoutAux_edgeIncidence_edgeLabel hAN hnonzero (hoP he)).symm
    _ = withoutAux (∑ e ∈ O, SimpleGraph.Walk.edgeIncidence e) :=
      (withoutAux_finset_sum _).symm
    _ = withoutAux (SimpleGraph.Walk.oddIncidence w) := by
      rw [SimpleGraph.Walk.IsTrail.oddIncidence_eq_sum h]

lemma withoutAux_single_one {p : ℕ} (hp : p ≠ 1) :
    withoutAux (Finsupp.single p 1) = Finsupp.single p 1 := by
  ext q
  by_cases hq1 : q = 1
  · subst q
    simp [withoutAux, hp]
  · by_cases hqp : q = p
    · subst q
      simp [withoutAux, hp]
    · simp [withoutAux, hq1, hqp, Finsupp.single_apply]

lemma highFactorization_sum_evenLabelSet_eq_oddLabelSet_of_even
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u : ℕ} {w : (productGraph N A).Walk u u}
    (h : w.IsTrail) (heven : Even w.length) :
    (∑ a ∈ evenLabelSet w h, highFactorization N a) =
      ∑ a ∈ oddLabelSet w h, highFactorization N a := by
  let E := SimpleGraph.Walk.IsTrail.evenEdgesFinset h
  let O := SimpleGraph.Walk.IsTrail.oddEdgesFinset h
  have heP : (E : Set (Sym2 ℕ)) ⊆ productEdgeFinset N A := by
    intro e he
    exact walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((evenTerms_sublist w.edges).subset he)
  have hoP : (O : Set (Sym2 ℕ)) ⊆ productEdgeFinset N A := by
    intro e he
    exact walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((oddTerms_sublist w.edges).subset he)
  have hsumE : (∑ e ∈ E, highFactorization N (edgeLabel N A e)) =
      withoutAux (SimpleGraph.Walk.evenIncidence w) := by
    calc
      (∑ e ∈ E, highFactorization N (edgeLabel N A e)) =
          ∑ e ∈ E, withoutAux (SimpleGraph.Walk.edgeIncidence e) := by
            apply Finset.sum_congr rfl
            intro e he
            exact (withoutAux_edgeIncidence_edgeLabel hAN hnonzero (heP he)).symm
      _ = withoutAux (∑ e ∈ E, SimpleGraph.Walk.edgeIncidence e) :=
        (withoutAux_finset_sum _).symm
      _ = withoutAux (SimpleGraph.Walk.evenIncidence w) := by
        rw [SimpleGraph.Walk.IsTrail.evenIncidence_eq_sum h]
  have hsumO : (∑ e ∈ O, highFactorization N (edgeLabel N A e)) =
      withoutAux (SimpleGraph.Walk.oddIncidence w) := by
    calc
      (∑ e ∈ O, highFactorization N (edgeLabel N A e)) =
          ∑ e ∈ O, withoutAux (SimpleGraph.Walk.edgeIncidence e) := by
            apply Finset.sum_congr rfl
            intro e he
            exact (withoutAux_edgeIncidence_edgeLabel hAN hnonzero (hoP he)).symm
      _ = withoutAux (∑ e ∈ O, SimpleGraph.Walk.edgeIncidence e) :=
        (withoutAux_finset_sum _).symm
      _ = withoutAux (SimpleGraph.Walk.oddIncidence w) := by
        rw [SimpleGraph.Walk.IsTrail.oddIncidence_eq_sum h]
  rw [evenLabelSet, oddLabelSet,
    Finset.sum_image ((edgeLabel_injOn N A).mono heP),
    Finset.sum_image ((edgeLabel_injOn N A).mono hoP)]
  rw [hsumE, hsumO, SimpleGraph.Walk.evenIncidence_eq_oddIncidence_of_closed heven]

/-- An even circuit in the factorization graph gives two disjoint nonempty
subsets of the compressed set whose products have the same high-prime
factorization.  Their total cardinality is exactly the circuit length. -/
theorem highValuation_prod_alternate_evenCircuit
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u : ℕ} {w : (productGraph N A).Walk u u}
    (hw : w.IsCircuit) (heven : Even w.length) :
    ∃ S T : Finset ℕ,
      S ⊆ A ∧ T ⊆ A ∧ Disjoint S T ∧ S.Nonempty ∧ T.Nonempty ∧
      highFactorization N (subsetProduct S) =
        highFactorization N (subsetProduct T) ∧
      S.card + T.card = w.length := by
  let S := evenLabelSet w hw.isTrail
  let T := oddLabelSet w hw.isTrail
  have hS := evenLabelSet_subset hAN hnonzero w hw.isTrail
  have hT := oddLabelSet_subset hAN hnonzero w hw.isTrail
  refine ⟨S, T, hS, hT, labelSet_disjoint hAN hnonzero w hw.isTrail,
    evenLabelSet_nonempty_of_isCircuit hw,
    oddLabelSet_nonempty_of_isCircuit hw, ?_,
    evenLabelSet_card_add_oddLabelSet_card hAN hnonzero w hw.isTrail⟩
  rw [highFactorization_subsetProduct
      (fun a ha ↦ by
        have haI := Finset.mem_Icc.mp (hAN (hS ha))
        omega),
    highFactorization_subsetProduct
      (fun a ha ↦ by
        have haI := Finset.mem_Icc.mp (hAN (hT ha))
        omega)]
  exact highFactorization_sum_evenLabelSet_eq_oddLabelSet_of_even
    hAN hnonzero hw.isTrail heven

/-- An odd circuit based at a square-prime vertex yields a corrected
alternating relation: the square-type element supplies the two missing
incidences at the base vertex. -/
theorem highValuation_prod_alternate_oddCycle_square
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {p : ℕ} (hp : p ∈ squarePrimeSet N A)
    {w : (productGraph N A).Walk p p}
    (hw : w.IsCircuit) (hodd : Odd w.length) :
    ∃ S T : Finset ℕ,
      S = evenLabelSet w hw.isTrail ∧
      T = insert (squareElementLabel N A p) (oddLabelSet w hw.isTrail) ∧
      S ⊆ A ∧ T ⊆ A ∧ Disjoint S T ∧ S.Nonempty ∧ T.Nonempty ∧
      highFactorization N (subsetProduct S) =
        highFactorization N (subsetProduct T) ∧
      S.card + T.card = w.length + 1 := by
  let a := squareElementLabel N A p
  let S := evenLabelSet w hw.isTrail
  let O := oddLabelSet w hw.isTrail
  let T := insert a O
  have haSq : a ∈ squareElements N A := squareElementLabel_mem hp
  have haA : a ∈ A := (Finset.mem_filter.mp haSq).1
  have hS : S ⊆ A := evenLabelSet_subset hAN hnonzero w hw.isTrail
  have hO : O ⊆ A := oddLabelSet_subset hAN hnonzero w hw.isTrail
  have hT : T ⊆ A := Finset.insert_subset haA hO
  have haNotS : a ∉ S := by
    intro haS
    obtain ⟨e, he, hea⟩ := Finset.mem_image.mp haS
    have hel := edgeLabel_mem (walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((evenTerms_sublist w.edges).subset he))
    have hnot := (Finset.mem_filter.mp hel).2
    exact hnot (hea ▸ (Finset.mem_filter.mp haSq).2)
  have haNotO : a ∉ O := by
    intro haO
    obtain ⟨e, he, hea⟩ := Finset.mem_image.mp haO
    have hel := edgeLabel_mem (walk_edge_mem_productEdgeFinset hAN hnonzero w
      ((oddTerms_sublist w.edges).subset he))
    have hnot := (Finset.mem_filter.mp hel).2
    exact hnot (hea ▸ (Finset.mem_filter.mp haSq).2)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rcases Finset.mem_insert.mp hxT with rfl | hxO
    · exact haNotS hxS
    · exact (Finset.disjoint_left.mp
        (labelSet_disjoint hAN hnonzero w hw.isTrail)) hxS hxO
  have hpMed := squarePrimeSet_subset_medium hAN hp
  have hpPrime : p.Prime := (mem_mediumPrimes.mp hpMed).2.2.2
  have hp1 : p ≠ 1 := hpPrime.ne_one
  have hsum : (∑ x ∈ S, highFactorization N x) =
      ∑ x ∈ T, highFactorization N x := by
    have hbalance := (SimpleGraph.Walk.alternatingIncidence_balance w).2 hodd
    have hwithout := congrArg withoutAux hbalance
    rw [withoutAux_add, withoutAux_add,
      withoutAux_single_one hp1] at hwithout
    have htwo : Finsupp.single p 1 + Finsupp.single p 1 =
        Finsupp.single p 2 := by
      ext q
      by_cases hq : q = p <;> simp [Finsupp.single_apply, hq]
    rw [highFactorization_sum_evenLabelSet_eq_withoutAux hAN hnonzero,
      Finset.sum_insert haNotO,
      highFactorization_squareElementLabel hp,
      highFactorization_sum_oddLabelSet_eq_withoutAux hAN hnonzero]
    rw [hwithout]
    calc
      withoutAux (SimpleGraph.Walk.oddIncidence w) +
            Finsupp.single p 1 + Finsupp.single p 1 =
          withoutAux (SimpleGraph.Walk.oddIncidence w) +
            (Finsupp.single p 1 + Finsupp.single p 1) := by ac_rfl
      _ = withoutAux (SimpleGraph.Walk.oddIncidence w) +
            Finsupp.single p 2 := by rw [htwo]
      _ = Finsupp.single p 2 +
            withoutAux (SimpleGraph.Walk.oddIncidence w) := by ac_rfl
  refine ⟨S, T, rfl, rfl, hS, hT, hST,
    evenLabelSet_nonempty_of_isCircuit hw,
    ⟨a, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
  · rw [highFactorization_subsetProduct
        (fun x hx ↦ by
          have hxI := Finset.mem_Icc.mp (hAN (hS hx))
          omega),
      highFactorization_subsetProduct
        (fun x hx ↦ by
          have hxI := Finset.mem_Icc.mp (hAN (hT hx))
          omega)]
    exact hsum
  · change S.card + (insert a O).card = w.length + 1
    rw [Finset.card_insert_of_notMem haNotO]
    have hcard := evenLabelSet_card_add_oddLabelSet_card
      hAN hnonzero w hw.isTrail
    change S.card + O.card = w.length at hcard
    omega

lemma oddSquareCanonical_spec
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {p : ℕ} (hp : p ∈ squarePrimeSet N A)
    {w : (productGraph N A).Walk p p}
    (hw : w.IsCircuit) (hodd : Odd w.length) :
    let S := evenLabelSet w hw.isTrail
    let T := insert (squareElementLabel N A p) (oddLabelSet w hw.isTrail)
    S ⊆ A ∧ T ⊆ A ∧ Disjoint S T ∧ S.Nonempty ∧ T.Nonempty ∧
      highFactorization N (subsetProduct S) =
        highFactorization N (subsetProduct T) ∧
      S.card + T.card = w.length + 1 := by
  obtain ⟨S, T, hS, hT, hSA, hTA, hdis, hSne, hTne, hprod, hcard⟩ :=
    highValuation_prod_alternate_oddCycle_square
      hAN hinj hnonzero hp hw hodd
  subst S
  subst T
  exact ⟨hSA, hTA, hdis, hSne, hTne, hprod, hcard⟩

/-! ## Binary choice spaces from disjoint multiplicative relations -/

/-- A finite family of disjoint two-sided additive relations.  In the
application, `f a` is the high-prime factorization of `a`; choosing either
side of every relation therefore leaves the total high factorization
unchanged. -/
structure RelationPacking {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (A : Finset α) (f : α → β) where
  pairs : Finset (Finset α × Finset α)
  left_subset : ∀ p ∈ pairs, p.1 ⊆ A
  right_subset : ∀ p ∈ pairs, p.2 ⊆ A
  left_nonempty : ∀ p ∈ pairs, p.1.Nonempty
  right_nonempty : ∀ p ∈ pairs, p.2.Nonempty
  within_disjoint : ∀ p ∈ pairs, Disjoint p.1 p.2
  support_pairwise : (pairs : Set (Finset α × Finset α)).PairwiseDisjoint
    (fun p ↦ p.1 ∪ p.2)
  relation : ∀ p ∈ pairs, (∑ a ∈ p.1, f a) = ∑ a ∈ p.2, f a

namespace RelationPacking

variable {α β : Type*} [DecidableEq α] [AddCommMonoid β]
  {A : Finset α} {f : α → β}

abbrev Choice (P : RelationPacking A f) := P.pairs → Bool

def part (P : RelationPacking A f) (p : Finset α × Finset α)
    (b : Bool) : Finset α :=
  if b then p.2 else p.1

lemma part_subset_support (P : RelationPacking A f)
    (p : Finset α × Finset α) (b : Bool) :
    P.part p b ⊆ p.1 ∪ p.2 := by
  cases b <;> simp [part]

lemma part_subset (P : RelationPacking A f) (p : P.pairs) (b : Bool) :
    P.part p b ⊆ A := by
  cases b with
  | false => simpa [part] using P.left_subset p p.property
  | true => simpa [part] using P.right_subset p p.property

lemma part_nonempty (P : RelationPacking A f) (p : P.pairs) (b : Bool) :
    (P.part p b).Nonempty := by
  cases b with
  | false => simpa [part] using P.left_nonempty p p.property
  | true => simpa [part] using P.right_nonempty p p.property

lemma part_injective (P : RelationPacking A f) (p : P.pairs) :
    Function.Injective (P.part p) := by
  intro b c hbc
  cases b with
  | false =>
      cases c with
      | false => rfl
      | true =>
          exfalso
          obtain ⟨x, hx⟩ := P.left_nonempty p p.property
          have hLR : (p : Finset α × Finset α).1 =
              (p : Finset α × Finset α).2 := by
            simpa [part] using hbc
          have hx' : x ∈ (p : Finset α × Finset α).2 := by
            rw [← hLR]
            exact hx
          exact (Finset.disjoint_left.mp (P.within_disjoint p p.property)) hx hx'
  | true =>
      cases c with
      | true => rfl
      | false =>
          exfalso
          obtain ⟨x, hx⟩ := P.right_nonempty p p.property
          have hRL : (p : Finset α × Finset α).2 =
              (p : Finset α × Finset α).1 := by
            simpa [part] using hbc
          have hx' : x ∈ (p : Finset α × Finset α).1 := by
            rw [← hRL]
            exact hx
          exact (Finset.disjoint_left.mp (P.within_disjoint p p.property)) hx' hx

def chosenSet (P : RelationPacking A f) (c : P.Choice) : Finset α :=
  P.pairs.attach.biUnion fun p ↦ P.part p (c p)

lemma chosenSet_subset (P : RelationPacking A f) (c : P.Choice) :
    P.chosenSet c ⊆ A := by
  rw [chosenSet, Finset.biUnion_subset_iff_forall_subset]
  intro p hp
  exact P.part_subset p (c p)

lemma chosenParts_pairwiseDisjoint (P : RelationPacking A f) (c : P.Choice) :
    (P.pairs.attach : Set P.pairs).PairwiseDisjoint
      (fun p ↦ P.part p (c p)) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro p hp q hq hinter
  apply Subtype.ext
  apply (Finset.pairwiseDisjoint_iff.mp P.support_pairwise)
    p.property q.property
  obtain ⟨x, hx⟩ := hinter
  obtain ⟨hxp, hxq⟩ := Finset.mem_inter.mp hx
  exact ⟨x, Finset.mem_inter.mpr ⟨
    P.part_subset_support p (c p) hxp,
    P.part_subset_support q (c q) hxq⟩⟩

lemma part_eq_of_chosenSet_eq (P : RelationPacking A f)
    {c d : P.Choice} (hcd : P.chosenSet c = P.chosenSet d)
    (p : P.pairs) : P.part p (c p) = P.part p (d p) := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hxall : x ∈ P.chosenSet c := by
      rw [chosenSet, Finset.mem_biUnion]
      exact ⟨p, Finset.mem_attach _ _, hx⟩
    rw [hcd, chosenSet, Finset.mem_biUnion] at hxall
    obtain ⟨q, hq, hxq⟩ := hxall
    have hpq : p = q := by
      apply Subtype.ext
      apply (Finset.pairwiseDisjoint_iff.mp P.support_pairwise)
        p.property q.property
      exact ⟨x, Finset.mem_inter.mpr ⟨
        P.part_subset_support p (c p) hx,
        P.part_subset_support q (d q) hxq⟩⟩
    simpa [hpq] using hxq
  · intro x hx
    have hxall : x ∈ P.chosenSet d := by
      rw [chosenSet, Finset.mem_biUnion]
      exact ⟨p, Finset.mem_attach _ _, hx⟩
    rw [← hcd, chosenSet, Finset.mem_biUnion] at hxall
    obtain ⟨q, hq, hxq⟩ := hxall
    have hpq : p = q := by
      apply Subtype.ext
      apply (Finset.pairwiseDisjoint_iff.mp P.support_pairwise)
        p.property q.property
      exact ⟨x, Finset.mem_inter.mpr ⟨
        P.part_subset_support p (d p) hx,
        P.part_subset_support q (c q) hxq⟩⟩
    simpa [hpq] using hxq

lemma chosenSet_injective (P : RelationPacking A f) :
    Function.Injective P.chosenSet := by
  intro c d hcd
  funext p
  exact P.part_injective p (P.part_eq_of_chosenSet_eq hcd p)

lemma sum_chosenSet_eq (P : RelationPacking A f) (c d : P.Choice) :
    (∑ a ∈ P.chosenSet c, f a) = ∑ a ∈ P.chosenSet d, f a := by
  rw [chosenSet, chosenSet,
    Finset.sum_biUnion (P.chosenParts_pairwiseDisjoint c),
    Finset.sum_biUnion (P.chosenParts_pairwiseDisjoint d)]
  apply Finset.sum_congr rfl
  intro p hp
  cases hc : c p <;> cases hd : d p
  · simp [part, hc, hd]
  · simpa [part, hc, hd] using P.relation p p.property
  · simpa [part, hc, hd] using (P.relation p p.property).symm
  · simp [part, hc, hd]

lemma card_choice (P : RelationPacking A f) :
    Fintype.card P.Choice = 2 ^ P.pairs.card := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

end RelationPacking

/-- Binary choices among pairwise disjoint high-factorization relations
inject into the finite small-code space under the DSP hypothesis. -/
theorem relationPacking_card_bound {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A)
    (P : RelationPacking A (highFactorization N)) :
    2 ^ P.pairs.card ≤ (N * N + 1) ^ (smallPrimes N).card := by
  let code : P.Choice → SmallCode N := fun c ↦
    smallCode N (P.chosenSet c) ((P.chosenSet_subset c).trans hAN)
  rw [distinctSubsetProducts_iff] at hA
  have hcode : Function.Injective code := by
    intro c d hcd
    apply P.chosenSet_injective
    apply hA (by simpa using P.chosenSet_subset c)
      (by simpa using P.chosenSet_subset d)
    apply subsetProduct_eq_of_codes (N := N)
      ((P.chosenSet_subset c).trans hAN)
      ((P.chosenSet_subset d).trans hAN)
    · simpa [code] using hcd
    · rw [highFactorization_subsetProduct
          (fun a ha ↦ by
            have haI := Finset.mem_Icc.mp (hAN (P.chosenSet_subset c ha))
            omega),
        highFactorization_subsetProduct
          (fun a ha ↦ by
            have haI := Finset.mem_Icc.mp (hAN (P.chosenSet_subset d ha))
            omega)]
      exact P.sum_chosenSet_eq c d
  rw [← P.card_choice, ← card_smallCode N]
  exact Fintype.card_le_of_injective code hcode

/-- Indexed form of `relationPacking_card_bound`.  It is convenient when
the relations are indexed by circuits rather than literally stored as
pairs of finsets. -/
theorem indexedRelationPacking_card_bound
    {ι : Type*} [DecidableEq ι] {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A)
    (I : Finset ι) (left right : ι → Finset ℕ)
    (hleft : ∀ i ∈ I, left i ⊆ A)
    (hright : ∀ i ∈ I, right i ⊆ A)
    (hleftne : ∀ i ∈ I, (left i).Nonempty)
    (hrightne : ∀ i ∈ I, (right i).Nonempty)
    (hdis : ∀ i ∈ I, Disjoint (left i) (right i))
    (hpair : (I : Set ι).PairwiseDisjoint
      (fun i ↦ left i ∪ right i))
    (hrel : ∀ i ∈ I,
      (∑ a ∈ left i, highFactorization N a) =
        ∑ a ∈ right i, highFactorization N a) :
    2 ^ I.card ≤ (N * N + 1) ^ (smallPrimes N).card := by
  let rel : ι → Finset ℕ × Finset ℕ := fun i ↦ (left i, right i)
  have hrelInj : Set.InjOn rel I := by
    intro i hi j hj hij
    by_contra hij'
    obtain ⟨x, hx⟩ := hleftne i hi
    have hleftEq : left i = left j := congrArg Prod.fst hij
    have hinter : ((left i ∪ right i) ∩
        (left j ∪ right j)).Nonempty := by
      refine ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, ?_⟩⟩
      exact Finset.mem_union_left _ (hleftEq ▸ hx)
    exact hij' ((Finset.pairwiseDisjoint_iff.mp hpair) hi hj hinter)
  let P : RelationPacking A (highFactorization N) := {
    pairs := I.image rel
    left_subset := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hleft i hi
    right_subset := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hright i hi
    left_nonempty := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hleftne i hi
    right_nonempty := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hrightne i hi
    within_disjoint := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hdis i hi
    support_pairwise := by
      rw [Finset.pairwiseDisjoint_iff]
      intro p hp q hq hinter
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      have hij := (Finset.pairwiseDisjoint_iff.mp hpair) hi hj hinter
      subst j
      rfl
    relation := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hrel i hi }
  have hbound := relationPacking_card_bound hAN hA P
  have hcard : P.pairs.card = I.card := by
    exact Finset.card_image_iff.mpr hrelInj
  simpa [hcard] using hbound

/-! ## Maximal finite families of edge-disjoint objects -/

/-- Finite families whose members are pairwise disjoint. -/
def IsDisjointFamily {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) : Prop :=
  (P : Set (Finset α)).PairwiseDisjoint id

/-- Every finite family of nonempty finite sets has a pairwise-disjoint
subfamily meeting every member of the original family.  Choosing a
maximum-cardinality packing makes the proof completely finite. -/
theorem exists_maximalDisjointFamily {α : Type*} [DecidableEq α]
    (C : Finset (Finset α)) (hne : ∀ s ∈ C, s.Nonempty) :
    ∃ P : Finset (Finset α),
      P ⊆ C ∧ IsDisjointFamily P ∧
      ∀ s ∈ C, ∃ t ∈ P, (s ∩ t).Nonempty := by
  let D := C.powerset.filter IsDisjointFamily
  have hD : D.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [D, IsDisjointFamily]
  obtain ⟨P, hPD, hmax⟩ := Finset.exists_mem_eq_sup D hD Finset.card
  have hPsub : P ⊆ C := by
    simpa using (Finset.mem_filter.mp hPD).1
  have hPdis : IsDisjointFamily P := (Finset.mem_filter.mp hPD).2
  refine ⟨P, hPsub, hPdis, ?_⟩
  intro s hs
  by_contra hhit
  have hno : ∀ t ∈ P, ¬(s ∩ t).Nonempty := by
    intro t ht hinter
    exact hhit ⟨t, ht, hinter⟩
  have hsP : s ∉ P := by
    intro hsP
    obtain ⟨x, hx⟩ := hne s hs
    exact hno s hsP ⟨x, Finset.mem_inter.mpr ⟨hx, hx⟩⟩
  have hinsDis : IsDisjointFamily (insert s P) := by
    rw [IsDisjointFamily, Finset.pairwiseDisjoint_iff]
    intro i hi j hj hinter
    have hi' : i = s ∨ i ∈ P := Finset.mem_insert.mp hi
    have hj' : j = s ∨ j ∈ P := Finset.mem_insert.mp hj
    rcases hi' with rfl | hi'
    · rcases hj' with rfl | hj'
      · rfl
      · exact (hno j hj' hinter).elim
    · rcases hj' with rfl | hj'
      · exact (hno i hi' (by simpa [Finset.inter_comm] using hinter)).elim
      · exact (Finset.pairwiseDisjoint_iff.mp hPdis) hi' hj' hinter
  have hinsD : insert s P ∈ D := by
    change insert s P ∈ C.powerset.filter IsDisjointFamily
    rw [Finset.mem_filter]
    exact ⟨by simpa using Finset.insert_subset hs hPsub, hinsDis⟩
  have hle := Finset.le_sup (s := D) (f := Finset.card) hinsD
  rw [hmax, Finset.card_insert_of_notMem hsP] at hle
  omega

/-! ## Finite packings of short even circuits -/

/-- Data witnessing that a given finite edge set is the edge set of a
short even circuit. -/
structure ShortEvenCircuitWitness (G : SimpleGraph ℕ) (L : ℕ)
    (s : Finset (Sym2 ℕ)) where
  base : ℕ
  walk : G.Walk base base
  isCircuit : walk.IsCircuit
  even : Even walk.length
  length_le : walk.length ≤ L
  edges_eq : isCircuit.isTrail.edgesFinset = s

/-- All edge sets of even circuits of length at most `L` in the product
graph.  This is finite because every such set lies in the finite edge set
of the graph. -/
def shortEvenCircuitEdgeSets (N : ℕ) (A : Finset ℕ) (L : ℕ) :
    Finset (Finset (Sym2 ℕ)) :=
  (productGraph N A).edgeFinset.powerset.filter fun s ↦
    Nonempty (ShortEvenCircuitWitness (productGraph N A) L s)

lemma mem_shortEvenCircuitEdgeSets {N L : ℕ} {A : Finset ℕ}
    {s : Finset (Sym2 ℕ)} :
    s ∈ shortEvenCircuitEdgeSets N A L ↔
      s ⊆ (productGraph N A).edgeFinset ∧
      Nonempty (ShortEvenCircuitWitness (productGraph N A) L s) := by
  simp [shortEvenCircuitEdgeSets]

lemma shortEvenCircuitEdgeSet_nonempty {N L : ℕ} {A : Finset ℕ}
    {s : Finset (Sym2 ℕ)} (hs : s ∈ shortEvenCircuitEdgeSets N A L) :
    s.Nonempty := by
  obtain ⟨W⟩ := (mem_shortEvenCircuitEdgeSets.mp hs).2
  have hne : W.walk.edges ≠ [] := by
    intro hnil
    have hthree := W.isCircuit.three_le_length
    rw [← W.walk.length_edges, hnil] at hthree
    simp at hthree
  obtain ⟨e, he⟩ := W.walk.edges.exists_mem_of_ne_nil hne
  refine ⟨e, ?_⟩
  rw [← W.edges_eq]
  exact he

lemma shortEvenCircuitEdgeSet_card_le {N L : ℕ} {A : Finset ℕ}
    {s : Finset (Sym2 ℕ)} (hs : s ∈ shortEvenCircuitEdgeSets N A L) :
    s.card ≤ L := by
  obtain ⟨W⟩ := (mem_shortEvenCircuitEdgeSets.mp hs).2
  rw [← W.edges_eq]
  change W.walk.edges.length ≤ L
  rw [W.walk.length_edges]
  exact W.length_le

lemma exists_edge_of_mem_labelSet_union {N : ℕ} {A : Finset ℕ}
    {u v : ℕ} (w : (productGraph N A).Walk u v) (h : w.IsTrail)
    {a : ℕ} (ha : a ∈ evenLabelSet w h ∪ oddLabelSet w h) :
    ∃ e ∈ h.edgesFinset, edgeLabel N A e = a := by
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨e, he, hea⟩ := Finset.mem_image.mp ha
    exact ⟨e, (evenTerms_sublist w.edges).subset he, hea⟩
  · obtain ⟨e, he, hea⟩ := Finset.mem_image.mp ha
    exact ⟨e, (oddTerms_sublist w.edges).subset he, hea⟩

/-- Every edge-disjoint family of short even circuits is bounded by the
small-code choice space. -/
theorem shortEvenCircuitPacking_card_bound
    {N L : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (P : Finset (Finset (Sym2 ℕ)))
    (hPC : P ⊆ shortEvenCircuitEdgeSets N A L)
    (hPdis : IsDisjointFamily P) :
    2 ^ P.card ≤ (N * N + 1) ^ (smallPrimes N).card := by
  let witness (p : P) :
      ShortEvenCircuitWitness (productGraph N A) L p :=
    Classical.choice (mem_shortEvenCircuitEdgeSets.mp (hPC p.property)).2
  let left (p : P) : Finset ℕ :=
    evenLabelSet (witness p).walk (witness p).isCircuit.isTrail
  let right (p : P) : Finset ℕ :=
    oddLabelSet (witness p).walk (witness p).isCircuit.isTrail
  have hleft : ∀ p ∈ P.attach, left p ⊆ A := by
    intro p hp
    exact evenLabelSet_subset hAN hnonzero _ _
  have hright : ∀ p ∈ P.attach, right p ⊆ A := by
    intro p hp
    exact oddLabelSet_subset hAN hnonzero _ _
  have hleftne : ∀ p ∈ P.attach, (left p).Nonempty := by
    intro p hp
    exact evenLabelSet_nonempty_of_isCircuit (witness p).isCircuit
  have hrightne : ∀ p ∈ P.attach, (right p).Nonempty := by
    intro p hp
    exact oddLabelSet_nonempty_of_isCircuit (witness p).isCircuit
  have hwithin : ∀ p ∈ P.attach, Disjoint (left p) (right p) := by
    intro p hp
    exact labelSet_disjoint hAN hnonzero _ _
  have hpair : (P.attach : Set P).PairwiseDisjoint
      (fun p ↦ left p ∪ right p) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro p hp q hq hinter
    apply Subtype.ext
    apply (Finset.pairwiseDisjoint_iff.mp hPdis) p.property q.property
    obtain ⟨a, ha⟩ := hinter
    obtain ⟨hap, haq⟩ := Finset.mem_inter.mp ha
    obtain ⟨e, he, hea⟩ := exists_edge_of_mem_labelSet_union
      (witness p).walk (witness p).isCircuit.isTrail hap
    obtain ⟨f, hf, hfa⟩ := exists_edge_of_mem_labelSet_union
      (witness q).walk (witness q).isCircuit.isTrail haq
    have heP : e ∈ productEdgeFinset N A :=
      walk_edge_mem_productEdgeFinset hAN hnonzero (witness p).walk he
    have hfP : f ∈ productEdgeFinset N A :=
      walk_edge_mem_productEdgeFinset hAN hnonzero (witness q).walk hf
    have hef : e = f := edgeLabel_injOn N A heP hfP (hea.trans hfa.symm)
    refine ⟨e, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [← (witness p).edges_eq]
      exact he
    · rw [← (witness q).edges_eq, hef]
      exact hf
  have hrel : ∀ p ∈ P.attach,
      (∑ a ∈ left p, highFactorization N a) =
        ∑ a ∈ right p, highFactorization N a := by
    intro p hp
    exact highFactorization_sum_evenLabelSet_eq_oddLabelSet_of_even
      hAN hnonzero (witness p).isCircuit.isTrail (witness p).even
  have hbound := indexedRelationPacking_card_bound hAN hA P.attach left right
    hleft hright hleftne hrightne hwithin hpair hrel
  simpa using hbound

/-- Delete a quantitatively controlled set of edges so that no short even
circuit remains.  The number of selected circuits satisfies the exact
power-of-two small-code bound. -/
theorem exists_deleteEdges_no_short_evenCircuit
    {N L : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    ∃ D : Finset (Sym2 ℕ), ∃ k : ℕ,
      D ⊆ (productGraph N A).edgeFinset ∧
      D.card ≤ L * k ∧
      2 ^ k ≤ (N * N + 1) ^ (smallPrimes N).card ∧
      ∀ u : ℕ, ∀ w : ((productGraph N A).deleteEdges D).Walk u u,
        w.IsCircuit → Even w.length → w.length ≤ L → False := by
  let C := shortEvenCircuitEdgeSets N A L
  obtain ⟨P, hPC, hPdis, hhit⟩ :=
    exists_maximalDisjointFamily C fun s hs ↦
      shortEvenCircuitEdgeSet_nonempty hs
  let D : Finset (Sym2 ℕ) := P.biUnion id
  refine ⟨D, P.card, ?_, ?_,
    shortEvenCircuitPacking_card_bound hAN hA hinj hnonzero P hPC hPdis,
    ?_⟩
  · intro e he
    obtain ⟨s, hsP, hes⟩ := Finset.mem_biUnion.mp he
    have hsC := hPC hsP
    exact (mem_shortEvenCircuitEdgeSets.mp hsC).1 hes
  · change (P.biUnion id).card ≤ L * P.card
    rw [Finset.card_biUnion hPdis]
    calc
      (∑ s ∈ P, s.card) ≤ ∑ _s ∈ P, L := by
        apply Finset.sum_le_sum
        intro s hs
        exact shortEvenCircuitEdgeSet_card_le (hPC hs)
      _ = L * P.card := by simp [Nat.mul_comm]
  · intro u w hw heven hlen
    have hedgeG : ∀ e ∈ w.edges, e ∈ (productGraph N A).edgeSet := by
      intro e he
      have hedel : e ∈ ((productGraph N A).deleteEdges D).edgeSet :=
        w.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at hedel
      exact hedel.1
    let wG : (productGraph N A).Walk u u :=
      w.transfer (productGraph N A) hedgeG
    have hwG : wG.IsCircuit := by
      rw [SimpleGraph.Walk.isCircuit_def, SimpleGraph.Walk.isTrail_def]
      constructor
      · simpa [wG, SimpleGraph.Walk.edges_transfer] using hw.isTrail.edges_nodup
      · intro hwGnil
        have hlen0 : wG.length = 0 := by simp [hwGnil]
        have : w.length = 0 := by
          simpa [wG, SimpleGraph.Walk.length_transfer] using hlen0
        exact hw.not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp this)
    let s : Finset (Sym2 ℕ) := hwG.isTrail.edgesFinset
    have hsC : s ∈ C := by
      apply mem_shortEvenCircuitEdgeSets.mpr
      constructor
      · intro e he
        have heG : e ∈ (productGraph N A).edgeSet :=
          wG.edges_subset_edgeSet he
        simpa using heG
      · exact ⟨{
          base := u
          walk := wG
          isCircuit := hwG
          even := by simpa [wG, SimpleGraph.Walk.length_transfer] using heven
          length_le := by simpa [wG, SimpleGraph.Walk.length_transfer] using hlen
          edges_eq := rfl }⟩
    obtain ⟨t, htP, hst⟩ := hhit s hsC
    obtain ⟨e, he⟩ := hst
    obtain ⟨hes, het⟩ := Finset.mem_inter.mp he
    have heD : e ∈ D := by
      change e ∈ P.biUnion id
      rw [Finset.mem_biUnion]
      exact ⟨t, htP, het⟩
    have hewG : e ∈ wG.edges := hes
    have hew : e ∈ w.edges := by
      simpa [wG, SimpleGraph.Walk.edges_transfer] using hewG
    have hedel : e ∈ ((productGraph N A).deleteEdges D).edgeSet :=
      w.edges_subset_edgeSet hew
    rw [SimpleGraph.edgeSet_deleteEdges] at hedel
    exact hedel.2 heD

/-! ## Short odd circuits meeting square-prime vertices -/

lemma isCircuit_transfer {G H : SimpleGraph ℕ} {u : ℕ}
    {w : H.Walk u u} (hw : w.IsCircuit)
    (hedge : ∀ e ∈ w.edges, e ∈ G.edgeSet) :
    (w.transfer G hedge).IsCircuit := by
  rw [SimpleGraph.Walk.isCircuit_def, SimpleGraph.Walk.isTrail_def]
  constructor
  · simpa [SimpleGraph.Walk.edges_transfer] using hw.isTrail.edges_nodup
  · intro hnil
    have hzero : (w.transfer G hedge).length = 0 := by simp [hnil]
    have : w.length = 0 := by
      simpa [SimpleGraph.Walk.length_transfer] using hzero
    exact hw.not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp this)

/-- A short odd circuit in a residual graph, based at a square-prime
vertex. -/
structure ShortSquareOddCircuitWitness (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) (L : ℕ) (s : Finset (Sym2 ℕ)) where
  base : ℕ
  base_square : base ∈ squarePrimeSet N A
  walk : ((productGraph N A).deleteEdges D).Walk base base
  isCircuit : walk.IsCircuit
  odd : Odd walk.length
  length_le : walk.length ≤ L
  edges_eq : isCircuit.isTrail.edgesFinset = s

noncomputable instance residualProductGraph.fintypeEdgeSet
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    Fintype ((productGraph N A).deleteEdges D).edgeSet := by
  apply Set.Finite.fintype
  rw [SimpleGraph.edgeSet_deleteEdges]
  exact (Set.toFinite (productGraph N A).edgeSet).diff

def shortSquareOddCircuitEdgeSets (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) (L : ℕ) : Finset (Finset (Sym2 ℕ)) :=
  ((productGraph N A).deleteEdges D).edgeFinset.powerset.filter fun s ↦
    Nonempty (ShortSquareOddCircuitWitness N A D L s)

lemma mem_shortSquareOddCircuitEdgeSets
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    {s : Finset (Sym2 ℕ)} :
    s ∈ shortSquareOddCircuitEdgeSets N A D L ↔
      s ⊆ ((productGraph N A).deleteEdges D).edgeFinset ∧
      Nonempty (ShortSquareOddCircuitWitness N A D L s) := by
  simp [shortSquareOddCircuitEdgeSets]

lemma shortSquareOddCircuitEdgeSet_nonempty
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    {s : Finset (Sym2 ℕ)}
    (hs : s ∈ shortSquareOddCircuitEdgeSets N A D L) :
    s.Nonempty := by
  obtain ⟨W⟩ := (mem_shortSquareOddCircuitEdgeSets.mp hs).2
  have hne : W.walk.edges ≠ [] := by
    intro hnil
    have hthree := W.isCircuit.three_le_length
    rw [← W.walk.length_edges, hnil] at hthree
    simp at hthree
  obtain ⟨e, he⟩ := W.walk.edges.exists_mem_of_ne_nil hne
  refine ⟨e, ?_⟩
  rw [← W.edges_eq]
  exact he

lemma shortSquareOddCircuitEdgeSet_card_le
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    {s : Finset (Sym2 ℕ)}
    (hs : s ∈ shortSquareOddCircuitEdgeSets N A D L) :
    s.card ≤ L := by
  obtain ⟨W⟩ := (mem_shortSquareOddCircuitEdgeSets.mp hs).2
  rw [← W.edges_eq]
  change W.walk.edges.length ≤ L
  rw [W.walk.length_edges]
  exact W.length_le

/-- Under a short-even-circuit prohibition, an edge-disjoint family of
short odd circuits meeting square-prime vertices again injects its binary
choice space into the small-code space. -/
theorem shortSquareOddCircuitPacking_card_bound
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoeven : ∀ u : ℕ,
      ∀ w : ((productGraph N A).deleteEdges D).Walk u u,
        w.IsCircuit → Even w.length → w.length ≤ 2 * L → False)
    (P : Finset (Finset (Sym2 ℕ)))
    (hPC : P ⊆ shortSquareOddCircuitEdgeSets N A D L)
    (hPdis : IsDisjointFamily P) :
    2 ^ P.card ≤ (N * N + 1) ^ (smallPrimes N).card := by
  let witness (p : P) : ShortSquareOddCircuitWitness N A D L p :=
    Classical.choice (mem_shortSquareOddCircuitEdgeSets.mp (hPC p.property)).2
  have hedge (p : P) : ∀ e ∈ (witness p).walk.edges,
      e ∈ (productGraph N A).edgeSet := by
    intro e he
    have he' : e ∈ ((productGraph N A).deleteEdges D).edgeSet :=
      (witness p).walk.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges] at he'
    exact he'.1
  let walkG (p : P) : (productGraph N A).Walk (witness p).base (witness p).base :=
    (witness p).walk.transfer (productGraph N A) (hedge p)
  have hwalkGCircuit (p : P) : (walkG p).IsCircuit :=
    isCircuit_transfer (witness p).isCircuit (hedge p)
  have hwalkGOdd (p : P) : Odd (walkG p).length := by
    simpa [walkG, SimpleGraph.Walk.length_transfer] using (witness p).odd
  have hbaseInj : Set.InjOn (fun p : P ↦ (witness p).base) P.attach := by
    intro p hp q hq hpq
    apply Subtype.ext
    by_contra hpq'
    have hfinDis : Disjoint (p : Finset (Sym2 ℕ)) q := by
      rw [Finset.disjoint_left]
      intro e hep heq
      have hpqEq := (Finset.pairwiseDisjoint_iff.mp hPdis)
        p.property q.property
        ⟨e, Finset.mem_inter.mpr ⟨hep, heq⟩⟩
      exact hpq' hpqEq
    let wq := (witness q).walk.copy hpq.symm hpq.symm
    have hlistDis : List.Disjoint (witness p).walk.edges
        wq.edges := by
      rw [List.disjoint_left]
      intro e hep heq
      apply (Finset.disjoint_left.mp hfinDis)
      · rw [← (witness p).edges_eq]
        exact hep
      · rw [← (witness q).edges_eq]
        have heq' : e ∈ (witness q).walk.edges := by
          simpa [wq] using heq
        exact heq'
    let c := (witness p).walk.append wq
    have hwqCircuit : wq.IsCircuit := by
      simpa [wq] using (witness q).isCircuit
    have hcTrail : c.IsTrail := by
      rw [SimpleGraph.Walk.isTrail_append]
      exact ⟨(witness p).isCircuit.isTrail,
        hwqCircuit.isTrail, hlistDis⟩
    have hc : c.IsCircuit := by
      refine ⟨hcTrail, ?_⟩
      intro hcNil
      have hpThree := (witness p).isCircuit.three_le_length
      have hpos : 0 < c.length := by
        simp only [c, SimpleGraph.Walk.length_append]
        omega
      exact (Nat.ne_of_gt hpos) (by simp [hcNil])
    have hceven : Even c.length := by
      simpa [c, SimpleGraph.Walk.length_append] using
        (witness p).odd.add_odd
          (show Odd wq.length by simpa [wq] using (witness q).odd)
    have hclen : c.length ≤ 2 * L := by
      have hpLe := (witness p).length_le
      have hqLe : wq.length ≤ L := by
        simpa [wq] using (witness q).length_le
      simp only [c, SimpleGraph.Walk.length_append]
      omega
    exact hnoeven (witness p).base c hc hceven hclen
  let left (p : P) : Finset ℕ :=
    evenLabelSet (walkG p) (hwalkGCircuit p).isTrail
  let right (p : P) : Finset ℕ :=
    insert (squareElementLabel N A (witness p).base)
      (oddLabelSet (walkG p) (hwalkGCircuit p).isTrail)
  have hspec (p : P) := oddSquareCanonical_spec hAN hinj hnonzero
    (witness p).base_square (hwalkGCircuit p) (hwalkGOdd p)
  have hleft : ∀ p ∈ P.attach, left p ⊆ A := by
    intro p hp
    exact (hspec p).1
  have hright : ∀ p ∈ P.attach, right p ⊆ A := by
    intro p hp
    exact (hspec p).2.1
  have hleftne : ∀ p ∈ P.attach, (left p).Nonempty := by
    intro p hp
    exact (hspec p).2.2.2.1
  have hrightne : ∀ p ∈ P.attach, (right p).Nonempty := by
    intro p hp
    exact (hspec p).2.2.2.2.1
  have hwithin : ∀ p ∈ P.attach, Disjoint (left p) (right p) := by
    intro p hp
    exact (hspec p).2.2.1
  have hsquareInj : Set.InjOn
      (fun p : P ↦ squareElementLabel N A (witness p).base) P.attach := by
    intro p hp q hq hpq
    apply hbaseInj hp hq
    have h := congrArg (squarePrime N) hpq
    simpa [squarePrime_squareElementLabel (witness p).base_square,
      squarePrime_squareElementLabel (witness q).base_square] using h
  have hsupportCases (p : P) {x : ℕ} (hx : x ∈ left p ∪ right p) :
      x = squareElementLabel N A (witness p).base ∨
        ∃ e ∈ (p : Finset (Sym2 ℕ)), edgeLabel N A e = x := by
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx
      right
      refine ⟨e, ?_, hex⟩
      rw [← (witness p).edges_eq]
      have : e ∈ (walkG p).edges :=
        (evenTerms_sublist (walkG p).edges).subset he
      have he' : e ∈ (witness p).walk.edges := by
        simpa [walkG, SimpleGraph.Walk.edges_transfer] using this
      exact he'
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inl rfl
      · obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx
        right
        refine ⟨e, ?_, hex⟩
        rw [← (witness p).edges_eq]
        have : e ∈ (walkG p).edges :=
          (oddTerms_sublist (walkG p).edges).subset he
        have he' : e ∈ (witness p).walk.edges := by
          simpa [walkG, SimpleGraph.Walk.edges_transfer] using this
        exact he'
  have hedgeIndex (p : P) {e : Sym2 ℕ} (he : e ∈ (p : Finset (Sym2 ℕ))) :
      e ∈ productEdgeFinset N A := by
    have heFin := (mem_shortSquareOddCircuitEdgeSets.mp (hPC p.property)).1 he
    have heSet : e ∈ ((productGraph N A).deleteEdges D).edgeSet := by
      simpa using heFin
    rw [SimpleGraph.edgeSet_deleteEdges] at heSet
    have heProd := heSet.1
    rw [productGraph_edgeSet hAN hnonzero] at heProd
    exact heProd
  have hpair : (P.attach : Set P).PairwiseDisjoint
      (fun p ↦ left p ∪ right p) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro p hp q hq hinter
    obtain ⟨x, hx⟩ := hinter
    obtain ⟨hxp, hxq⟩ := Finset.mem_inter.mp hx
    rcases hsupportCases p hxp with hxs | ⟨e, hep, hex⟩
    · rcases hsupportCases q hxq with hxs' | ⟨f, hfq, hfx⟩
      · exact hsquareInj hp hq (hxs.symm.trans hxs')
      · exfalso
        have haSq := squareElementLabel_mem (witness p).base_square
        have hfP : f ∈ productEdgeFinset N A := hedgeIndex q hfq
        have hfl := edgeLabel_mem hfP
        exact (Finset.mem_filter.mp hfl).2
          ((hfx.trans hxs) ▸ (Finset.mem_filter.mp haSq).2)
    · rcases hsupportCases q hxq with hxs' | ⟨f, hfq, hfx⟩
      · exfalso
        have haSq := squareElementLabel_mem (witness q).base_square
        have heP : e ∈ productEdgeFinset N A := hedgeIndex p hep
        have hel := edgeLabel_mem heP
        exact (Finset.mem_filter.mp hel).2
          ((hex.trans hxs') ▸ (Finset.mem_filter.mp haSq).2)
      · apply Subtype.ext
        apply (Finset.pairwiseDisjoint_iff.mp hPdis) p.property q.property
        have heP : e ∈ productEdgeFinset N A := hedgeIndex p hep
        have hfP : f ∈ productEdgeFinset N A := hedgeIndex q hfq
        have hef := edgeLabel_injOn N A heP hfP (hex.trans hfx.symm)
        subst f
        exact ⟨e, Finset.mem_inter.mpr ⟨hep, hfq⟩⟩
  have hrel : ∀ p ∈ P.attach,
      (∑ a ∈ left p, highFactorization N a) =
        ∑ a ∈ right p, highFactorization N a := by
    intro p hp
    have hprod := (hspec p).2.2.2.2.2.1
    rw [highFactorization_subsetProduct
        (fun a ha ↦ by
          have haI := Finset.mem_Icc.mp (hAN (hleft p hp ha))
          omega),
      highFactorization_subsetProduct
        (fun a ha ↦ by
          have haI := Finset.mem_Icc.mp (hAN (hright p hp ha))
          omega)] at hprod
    exact hprod
  have hbound := indexedRelationPacking_card_bound hAN hA P.attach left right
    hleft hright hleftne hrightne hwithin hpair hrel
  simpa using hbound

/-- After the short even circuits have been excluded, delete a controlled
family of edges so that no short odd circuit based at a square-prime vertex
remains. -/
theorem exists_deleteEdges_no_short_squareCircuit
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoeven : ∀ u : ℕ,
      ∀ w : ((productGraph N A).deleteEdges D).Walk u u,
        w.IsCircuit → Even w.length → w.length ≤ 2 * L → False) :
    ∃ E : Finset (Sym2 ℕ), ∃ k : ℕ,
      E ⊆ ((productGraph N A).deleteEdges D).edgeFinset ∧
      E.card ≤ L * k ∧
      2 ^ k ≤ (N * N + 1) ^ (smallPrimes N).card ∧
      ∀ p ∈ squarePrimeSet N A,
        ∀ w : (((productGraph N A).deleteEdges D).deleteEdges E).Walk p p,
          w.IsCircuit → Odd w.length → w.length ≤ L → False := by
  let C := shortSquareOddCircuitEdgeSets N A D L
  obtain ⟨P, hPC, hPdis, hhit⟩ :=
    exists_maximalDisjointFamily C fun s hs ↦
      shortSquareOddCircuitEdgeSet_nonempty hs
  let E : Finset (Sym2 ℕ) := P.biUnion id
  refine ⟨E, P.card, ?_, ?_,
    shortSquareOddCircuitPacking_card_bound
      hAN hA hinj hnonzero hnoeven P hPC hPdis, ?_⟩
  · intro e he
    obtain ⟨s, hsP, hes⟩ := Finset.mem_biUnion.mp he
    exact (mem_shortSquareOddCircuitEdgeSets.mp (hPC hsP)).1 hes
  · change (P.biUnion id).card ≤ L * P.card
    rw [Finset.card_biUnion hPdis]
    calc
      (∑ s ∈ P, s.card) ≤ ∑ _s ∈ P, L := by
        apply Finset.sum_le_sum
        intro s hs
        exact shortSquareOddCircuitEdgeSet_card_le (hPC hs)
      _ = L * P.card := by simp [Nat.mul_comm]
  · intro p hp w hw hodd hlen
    let H := (productGraph N A).deleteEdges D
    have hedgeH : ∀ e ∈ w.edges, e ∈ H.edgeSet := by
      intro e he
      have he' : e ∈ (H.deleteEdges E).edgeSet := w.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at he'
      exact he'.1
    let wH : H.Walk p p := w.transfer H hedgeH
    have hwH : wH.IsCircuit := isCircuit_transfer hw hedgeH
    let s : Finset (Sym2 ℕ) := hwH.isTrail.edgesFinset
    have hsC : s ∈ C := by
      apply mem_shortSquareOddCircuitEdgeSets.mpr
      constructor
      · intro e he
        have heH : e ∈ H.edgeSet := wH.edges_subset_edgeSet he
        simpa [H] using heH
      · exact ⟨{
          base := p
          base_square := hp
          walk := wH
          isCircuit := hwH
          odd := by
            change Odd (w.transfer H hedgeH).length
            rw [SimpleGraph.Walk.length_transfer]
            exact hodd
          length_le := by
            change (w.transfer H hedgeH).length ≤ L
            rw [SimpleGraph.Walk.length_transfer]
            exact hlen
          edges_eq := rfl }⟩
    obtain ⟨t, htP, hst⟩ := hhit s hsC
    obtain ⟨e, he⟩ := hst
    obtain ⟨hes, het⟩ := Finset.mem_inter.mp he
    have heE : e ∈ E := by
      change e ∈ P.biUnion id
      rw [Finset.mem_biUnion]
      exact ⟨t, htP, het⟩
    have hewH : e ∈ wH.edges := hes
    have hew : e ∈ w.edges := by
      simpa [wH, SimpleGraph.Walk.edges_transfer] using hewH
    have he' : e ∈ (H.deleteEdges E).edgeSet := w.edges_subset_edgeSet hew
    rw [SimpleGraph.edgeSet_deleteEdges] at he'
    exact he'.2 heE

/-! ## The remaining short odd cycles -/

/-- Two edge-disjoint short odd cycles cannot meet when short even circuits
are absent: rotate both cycles to a common vertex and concatenate them. -/
theorem oddCycles_support_disjoint_of_no_short_even
    {G : SimpleGraph ℕ} {L : ℕ}
    (hnoeven : ∀ u : ℕ, ∀ w : G.Walk u u,
      w.IsCircuit → Even w.length → w.length ≤ 2 * L → False)
    {u v : ℕ} {c : G.Walk u u} {d : G.Walk v v}
    (hc : c.IsCycle) (hd : d.IsCycle)
    (hcodd : Odd c.length) (hdodd : Odd d.length)
    (hclen : c.length ≤ L) (hdlen : d.length ≤ L)
    (hedges : c.edges.Disjoint d.edges) :
    c.support.Disjoint d.support := by
  rw [List.disjoint_left]
  intro x hxc hxd
  let c' := c.rotate x hxc
  let d' := d.rotate x hxd
  have hc' : c'.IsCycle := hc.rotate hxc
  have hd' : d'.IsCycle := hd.rotate hxd
  have hedges' : c'.edges.Disjoint d'.edges := by
    have pc : c'.edges.Perm c.edges := (c.rotate_edges x hxc).perm
    have pd : d'.edges.Perm d.edges := (d.rotate_edges x hxd).perm
    exact (pc.disjoint_left.trans pd.disjoint_right).mpr hedges
  let w := c'.append d'
  have hwTrail : w.IsTrail := by
    rw [SimpleGraph.Walk.isTrail_append]
    exact ⟨hc'.isCircuit.isTrail, hd'.isCircuit.isTrail, hedges'⟩
  have hw : w.IsCircuit := by
    refine ⟨hwTrail, ?_⟩
    intro hnil
    have hcThree := hc.three_le_length
    have hpos : 0 < w.length := by
      simp only [w, SimpleGraph.Walk.length_append,
        c', d', SimpleGraph.Walk.length_rotate]
      omega
    exact (Nat.ne_of_gt hpos) (by simp [hnil])
  have hweven : Even w.length := by
    simpa [w, c', d'] using hcodd.add_odd hdodd
  have hwlen : w.length ≤ 2 * L := by
    simp only [w, SimpleGraph.Walk.length_append,
      c', d', SimpleGraph.Walk.length_rotate]
    omega
  exact hnoeven x w hw hweven hwlen

/-! ## Exact logarithmic bounds for the packing counts -/

lemma exponent_le_card_mul_log {k r s : ℕ}
    (h : 2 ^ k ≤ r ^ s) :
    k ≤ s * (Nat.log 2 r + 1) := by
  have hr : r ≤ 2 ^ (Nat.log 2 r + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num) r).le
  have hrs : r ^ s ≤ (2 ^ (Nat.log 2 r + 1)) ^ s :=
    Nat.pow_le_pow_left hr s
  have htwo : 2 ^ k ≤ 2 ^ (s * (Nat.log 2 r + 1)) := by
    calc
      2 ^ k ≤ r ^ s := h
      _ ≤ (2 ^ (Nat.log 2 r + 1)) ^ s := hrs
      _ = 2 ^ (s * (Nat.log 2 r + 1)) := by
        rw [← Nat.pow_mul]
        simp [Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp htwo

lemma packingCount_le_smallPrimeError {N k : ℕ}
    (h : 2 ^ k ≤ (N * N + 1) ^ (smallPrimes N).card) :
    k ≤ (smallPrimes N).card * (Nat.log 2 (N * N + 1) + 1) :=
  exponent_le_card_mul_log h

/-- The exact finite entropy term controlling fibre pairs and disjoint
circuit packings. -/
def smallPrimeError (N : ℕ) : ℕ :=
  (smallPrimes N).card * (Nat.log 2 (N * N + 1) + 1)

/-- The binary logarithmic scale used in all finite estimates. -/
def binaryScale (N : ℕ) : ℕ := Nat.log2 (N + 1) + 1

/-- A polylogarithmic Moore depth.  Its cube dominates the logarithmic
factor in the Moore inequality, while the cost of deleting cycles remains
`N^(1/3)` times a fixed power of a logarithm. -/
def cycleCutoff (N : ℕ) : ℕ := binaryScale N ^ 3

/-- The cycle-length threshold corresponding to `cycleCutoff`. -/
def shortCycleCutoff (N : ℕ) : ℕ := 2 * (cycleCutoff N + 1)

lemma packingCount_le_smallPrimeError' {N k : ℕ}
    (h : 2 ^ k ≤ (N * N + 1) ^ (smallPrimes N).card) :
    k ≤ smallPrimeError N :=
  packingCount_le_smallPrimeError h

lemma card_smallPrimes_le_cubeRoot (N : ℕ) :
    (smallPrimes N).card ≤ cubeRoot N := by
  calc
    (smallPrimes N).card ≤ (interval (cubeRoot N)).card := by
      exact Finset.card_le_card (by
        intro p hp
        exact (Finset.mem_filter.mp hp).1)
    _ = cubeRoot N := interval_card _

lemma binaryScale_pos (N : ℕ) : 0 < binaryScale N := by
  simp [binaryScale]

lemma binaryScale_le_cycleCutoff (N : ℕ) :
    binaryScale N ≤ cycleCutoff N := by
  exact Nat.le_pow (by norm_num : 0 < 3)

/-! ## Path counting for the finite Moore bound -/

/-- A path of prescribed length starting at a fixed root, with its endpoint
included as data. -/
structure RootedPath {V : Type*} (G : SimpleGraph V) (root : V) (n : ℕ) where
  endpoint : V
  walk : G.Walk root endpoint
  isPath : walk.IsPath
  length_eq : walk.length = n

noncomputable instance RootedPath.fintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) (root : V) (n : ℕ) :
    Fintype (RootedPath G root n) := by
  let e : RootedPath G root n ≃
      Σ v : V, {w : G.Walk root v // w.IsPath ∧ w.length = n} := {
    toFun := fun p ↦ ⟨p.endpoint, p.walk, p.isPath, p.length_eq⟩
    invFun := fun p ↦ ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
    left_inv := by intro p; cases p; rfl
    right_inv := by intro p; rcases p with ⟨v, w, hw⟩; rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Below half the girth, distinct rooted paths have distinct endpoints. -/
theorem RootedPath.endpoint_injective_of_no_short_cycle
    {V : Type*} [Fintype V] {G : SimpleGraph V} {root : V} {n : ℕ}
    (hno : ∀ u : V, ∀ c : G.Walk u u,
      c.IsCycle → c.length ≤ 2 * n → False) :
    Function.Injective (fun p : RootedPath G root n ↦ p.endpoint) := by
  intro p q hpq
  cases p with
  | mk pe pw pp plen =>
    cases q with
    | mk qe qw qp qlen =>
      dsimp at hpq
      subst qe
      have hpw : pw = qw := by
        by_contra hne
        obtain ⟨u, hu₁, hu₂, c, hc, hclen⟩ :=
          pp.exists_isCycle_length_le_add_of_ne qp hne
        apply hno u c hc
        omega
      subst qw
      rfl

lemma RootedPath.card_le_vertices_of_no_short_cycle
    {V : Type*} [Fintype V] {G : SimpleGraph V} {root : V} {n : ℕ}
    (hno : ∀ u : V, ∀ c : G.Walk u u,
      c.IsCycle → c.length ≤ 2 * n → False) :
    Fintype.card (RootedPath G root n) ≤ Fintype.card V :=
  Fintype.card_le_of_injective _
    (RootedPath.endpoint_injective_of_no_short_cycle hno)

/-- In a graph without short cycles, a neighbor of the endpoint of a short
path, other than the predecessor along the path, is a genuinely new
vertex. -/
lemma SimpleGraph.Walk.IsPath.neighbor_not_mem_support_of_no_short_cycle
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} (hp : p.IsPath) (hvw : G.Adj v w)
    (hwpen : w ≠ p.penultimate)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ p.length + 1 → False) :
    w ∉ p.support := by
  intro hwp
  let q := p.dropUntil w hwp
  have hqPath : q.IsPath := hp.dropUntil hwp
  have hedgeP : s(v, w) ∉ p.edges := by
    intro hedge
    exact hwpen (hp.eq_penultimate_of_mem_edges hedge)
  have hedgeQ : s(v, w) ∉ q.edges := by
    intro hedge
    exact hedgeP ((p.isSubwalk_dropUntil hwp).edges_subset hedge)
  let c : G.Walk v v := SimpleGraph.Walk.cons hvw q
  have hc : c.IsCycle := by
    exact (SimpleGraph.Walk.cons_isCycle_iff q hvw).mpr ⟨hqPath, hedgeQ⟩
  have hclen : c.length ≤ p.length + 1 := by
    simp only [c, SimpleGraph.Walk.length_cons]
    exact Nat.add_le_add_right (SimpleGraph.Walk.length_dropUntil_le p hwp) 1
  exact hno v c hc hclen

def RootedPath.availableNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {root : V} {n : ℕ}
    (p : RootedPath G root n) : Finset V :=
  (G.neighborFinset p.endpoint).erase p.walk.penultimate

lemma RootedPath.two_le_card_availableNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v)
    {root : V} {n : ℕ} (p : RootedPath G root n) :
    2 ≤ p.availableNeighbors.card := by
  have hd := hdeg p.endpoint
  by_cases hp : p.walk.penultimate ∈ G.neighborFinset p.endpoint
  · rw [availableNeighbors, Finset.card_erase_of_mem hp]
    have hcard : (G.neighborFinset p.endpoint).card = G.degree p.endpoint :=
      G.card_neighborFinset_eq_degree p.endpoint
    rw [hcard]
    omega
  · rw [availableNeighbors, Finset.erase_eq_of_notMem hp]
    rw [G.card_neighborFinset_eq_degree p.endpoint]
    omega

noncomputable def RootedPath.nextEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v)
    {root : V} {n : ℕ} (p : RootedPath G root n) :
    Fin 2 ↪ p.availableNeighbors := {
  toFun := fun i ↦ p.availableNeighbors.equivFin.symm
    (Fin.castLE (p.two_le_card_availableNeighbors hdeg) i)
  inj' := fun i j hij ↦ by
    have hij' := p.availableNeighbors.equivFin.symm.injective hij
    exact Fin.castLE_injective _ hij' }

noncomputable def RootedPath.extend
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v)
    {root : V} {n : ℕ} (p : RootedPath G root n) (i : Fin 2)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    RootedPath G root (n + 1) := by
  let z : V := p.nextEmbedding hdeg i
  have hzmem : z ∈ p.availableNeighbors := (p.nextEmbedding hdeg i).property
  have hzdata := Finset.mem_erase.mp hzmem
  have hadj : G.Adj p.endpoint z := by
    exact (G.mem_neighborFinset p.endpoint z).mp hzdata.2
  have hznew : z ∉ p.walk.support := by
    apply Erdos795.SimpleGraph.Walk.IsPath.neighbor_not_mem_support_of_no_short_cycle
      p.isPath hadj hzdata.1
    intro x c hc hclen
    apply hno x c hc
    rw [p.length_eq] at hclen
    omega
  exact {
    endpoint := z
    walk := p.walk.concat hadj
    isPath := p.isPath.concat hznew hadj
    length_eq := by simp [p.length_eq] }

noncomputable def RootedPath.extensionEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v)
    {root : V} {n : ℕ}
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    RootedPath G root n × Fin 2 ↪ RootedPath G root (n + 1) := {
  toFun := fun pi ↦ pi.1.extend hdeg pi.2 hno
  inj' := by
    rintro ⟨p, i⟩ ⟨q, j⟩ hext
    have hep : p.endpoint = q.endpoint := by
      have hpen := congrArg
        (fun r : RootedPath G root (n + 1) ↦ r.walk.penultimate) hext
      simpa [RootedPath.extend, SimpleGraph.Walk.penultimate_concat] using hpen
    have hpq : p = q := by
      apply RootedPath.endpoint_injective_of_no_short_cycle
      intro x c hc hclen
      apply hno x c hc
      omega
      exact hep
    subst q
    have hend : (p.nextEmbedding hdeg i : V) =
        (p.nextEmbedding hdeg j : V) := congrArg RootedPath.endpoint hext
    have hij : i = j := by
      apply (p.nextEmbedding hdeg).injective
      apply Subtype.ext
      exact hend
    subst j
    rfl }

lemma RootedPath.card_double_le_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v)
    {root : V} {n : ℕ}
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    Fintype.card (RootedPath G root n) * 2 ≤
      Fintype.card (RootedPath G root (n + 1)) := by
  have hcard := Fintype.card_le_of_injective _
    (RootedPath.extensionEmbedding (root := root) hdeg hno).injective
  simpa using hcard

def RootedPath.nil {V : Type*} {G : SimpleGraph V} (root : V) :
    RootedPath G root 0 := {
  endpoint := root
  walk := SimpleGraph.Walk.nil
  isPath := SimpleGraph.Walk.IsPath.nil
  length_eq := rfl }

lemma RootedPath.pow_two_le_card_of_no_short_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v)
    {root : V} {n : ℕ}
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * n → False) :
    2 ^ n ≤ Fintype.card (RootedPath G root n) := by
  induction n with
  | zero =>
      have hpos : 0 < Fintype.card (RootedPath G root 0) :=
        Fintype.card_pos_iff.mpr ⟨RootedPath.nil root⟩
      simpa only [pow_zero]
  | succ n ih =>
      have hnoPrev : ∀ x : V, ∀ c : G.Walk x x,
          c.IsCycle → c.length ≤ 2 * n → False := by
        intro x c hc hclen
        apply hno x c hc
        omega
      have hpow : 2 ^ n ≤ Fintype.card (RootedPath G root n) := ih hnoPrev
      have hmul : 2 ^ n * 2 ≤ Fintype.card (RootedPath G root n) * 2 :=
        Nat.mul_le_mul_right 2 hpow
      rw [pow_succ]
      exact hmul.trans (RootedPath.card_double_le_succ hdeg hno)

theorem exists_short_cycle_of_minDegree_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : 0 < Fintype.card V)
    (hdeg : ∀ v, 3 ≤ G.degree v) :
    ∃ x : V, ∃ c : G.Walk x x,
      c.IsCycle ∧ c.length ≤ 2 * (Nat.log2 (Fintype.card V) + 1) := by
  let root : V := Classical.choice (Fintype.card_pos_iff.mp hV)
  by_contra hcontra
  push Not at hcontra
  have hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (Nat.log2 (Fintype.card V) + 1) → False := by
    intro x c hc hlen
    have := hcontra x c hc
    omega
  have hpow := RootedPath.pow_two_le_card_of_no_short_cycle hdeg (root := root) hno
  have hpaths := RootedPath.card_le_vertices_of_no_short_cycle (root := root) hno
  have htwo : 2 ^ (Nat.log2 (Fintype.card V) + 1) ≤ Fintype.card V :=
    hpow.trans hpaths
  have hlog : Nat.log2 (Fintype.card V) + 1 ≤ Nat.log2 (Fintype.card V) :=
    (Nat.le_log2 (Nat.ne_of_gt hV)).mpr htwo
  omega

/-! ## Non-backtracking continuations -/

/-- An oriented edge of a finite simple graph, represented by its tail and
head. -/
abbrev Dart {V : Type*} (G : SimpleGraph V) :=
  Σ v : V, G.neighborSet v

namespace Dart

abbrev tail {V : Type*} {G : SimpleGraph V} (e : Dart G) : V := e.1

abbrev head {V : Type*} {G : SimpleGraph V} (e : Dart G) : V := e.2.1

abbrev adj {V : Type*} {G : SimpleGraph V} (e : Dart G) :
    G.Adj e.tail e.head := e.2.2

def nextVertices {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) : Finset (G.neighborSet e.head) :=
  Finset.univ.erase ⟨e.tail, e.adj.symm⟩

lemma mem_nextVertices {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {e : Dart G} {w : G.neighborSet e.head} :
    w ∈ e.nextVertices ↔ w.1 ≠ e.tail := by
  simp only [nextVertices, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro h hw
    exact h (Subtype.ext hw)
  · intro h hw
    exact h (congrArg Subtype.val hw)

abbrev nextDart {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) (w : e.nextVertices) : Dart G :=
  ⟨e.head, w.1.1, w.1.2⟩

@[simp] lemma tail_nextDart {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) (w : e.nextVertices) : (e.nextDart w).tail = e.head := rfl

@[simp] lemma head_nextDart {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) (w : e.nextVertices) : (e.nextDart w).head = w.1 := rfl

lemma card_nextVertices {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (e : Dart G) :
    e.nextVertices.card = G.degree e.head - 1 := by
  rw [nextVertices, Finset.card_erase_of_mem (Finset.mem_univ _)]
  change Fintype.card (G.neighborSet e.head) - 1 = _
  rw [G.card_neighborSet_eq_degree]

lemma card_pos_nextVertices_of_two_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (e : Dart G) :
    0 < e.nextVertices.card := by
  rw [card_nextVertices]
  have := hdeg e.head
  omega

end Dart

universe u

/-- A sequence of non-backtracking choices after an initial oriented edge.
`NBTrace G e r` has total walk length `r+1`. -/
def NBTrace {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Dart G → ℕ → Type u
  | _, 0 => ULift.{u} (Fin 1)
  | e, n + 1 => Σ w : e.nextVertices, NBTrace G (e.nextDart w) n

noncomputable instance NBTrace.instFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Dart G) (n : ℕ) : Fintype (NBTrace G e n) := by
  induction n generalizing e with
  | zero => rw [NBTrace]; infer_instance
  | succ n ih =>
      rw [NBTrace]
      letI (w : e.nextVertices) : Fintype (NBTrace G (e.nextDart w) n) := ih _
      infer_instance

lemma NBTrace.card_zero {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (e : Dart G) :
    Fintype.card (NBTrace G e 0) = 1 := by
  change Fintype.card (ULift (Fin 1)) = 1
  rw [Fintype.card_congr Equiv.ulift]
  simp

lemma NBTrace.card_succ {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (e : Dart G) (n : ℕ) :
    Fintype.card (NBTrace G e (n + 1)) =
      ∑ w : e.nextVertices, Fintype.card (NBTrace G (e.nextDart w) n) := by
  change Fintype.card (Σ w : e.nextVertices,
    NBTrace G (e.nextDart w) n) = _
  rw [Fintype.card_sigma]

lemma NBTrace.card_pos_of_two_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (e : Dart G) (n : ℕ) :
    0 < Fintype.card (NBTrace G e n) := by
  induction n generalizing e with
  | zero => rw [NBTrace.card_zero]; norm_num
  | succ n ih =>
      rw [NBTrace.card_succ]
      have hne : e.nextVertices.Nonempty :=
        Finset.card_pos.mp (e.card_pos_nextVertices_of_two_le_degree hdeg)
      exact Finset.sum_pos (fun z _ ↦ ih (e.nextDart z))
        (by simpa using hne)

namespace NBTrace

def endpoint {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    {e : Dart G} → {n : ℕ} → NBTrace G e n → V
  | e, 0, _ => e.head
  | _, _ + 1, ⟨_, t⟩ => endpoint t

def choices {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    {e : Dart G} → {n : ℕ} → NBTrace G e n → List V
  | _, 0, _ => []
  | _, _ + 1, ⟨w, t⟩ => w.1.1 :: choices t

def walk {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    (e : Dart G) → {n : ℕ} → (t : NBTrace G e n) →
      G.Walk e.tail (endpoint t)
  | e, 0, _ => e.adj.toWalk
  | e, _ + 1, ⟨w, t⟩ => SimpleGraph.Walk.cons e.adj (walk (e.nextDart w) t)

@[simp] lemma length_walk {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) {n : ℕ} (t : NBTrace G e n) :
    (walk e t).length = n + 1 := by
  induction n generalizing e with
  | zero => exact e.adj.length_toWalk
  | succ n ih =>
      rcases t with ⟨w, t⟩
      simp only [walk, endpoint]
      change (walk (e.nextDart w) t).length + 1 = n + 1 + 1
      rw [ih]

@[simp] lemma snd_walk {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) {n : ℕ} (t : NBTrace G e n) :
    (walk e t).snd = e.head := by
  cases n with
  | zero => rfl
  | succ n =>
      rcases t with ⟨w, t⟩
      simp only [walk, endpoint]
      change (SimpleGraph.Walk.cons e.adj (walk (e.nextDart w) t)).getVert 1 = e.head
      simp only [SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]

lemma support_walk {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) {n : ℕ} (t : NBTrace G e n) :
    (walk e t).support = e.tail :: e.head :: choices t := by
  induction n generalizing e with
  | zero => exact e.adj.support_toWalk
  | succ n ih =>
      rcases t with ⟨w, t⟩
      simp only [walk, endpoint, choices]
      change e.tail :: (walk (e.nextDart w) t).support =
        e.tail :: e.head :: w.1.1 :: choices t
      rw [ih]

theorem choices_injective {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) (n : ℕ) : Function.Injective
      (choices : NBTrace G e n → List V) := by
  induction n generalizing e with
  | zero =>
      intro t s h
      apply ULift.ext
      exact Subsingleton.elim _ _
  | succ n ih =>
      rintro ⟨w, t⟩ ⟨z, s⟩ h
      change w.1.1 :: choices t = z.1.1 :: choices s at h
      have hwzVal : w.1 = z.1 := Subtype.ext (List.cons.inj h).1
      have hwz : w = z := Subtype.ext hwzVal
      subst z
      have hts : t = s := ih (e.nextDart w) (List.cons.inj h).2
      subst s
      rfl

theorem eq_of_support_walk_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) {n : ℕ} (t s : NBTrace G e n)
    (h : (walk e t).support = (walk e s).support) : t = s := by
  apply choices_injective e n
  simpa [support_walk] using h

theorem isPath_walk_of_no_short_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) {n : ℕ} (t : NBTrace G e n)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    (walk e t).IsPath := by
  induction n generalizing e with
  | zero =>
      exact e.adj.isPath_toWalk
  | succ n ih =>
      rcases t with ⟨w, t⟩
      have hnoTail : ∀ x : V, ∀ c : G.Walk x x,
          c.IsCycle → c.length ≤ 2 * (n + 1) → False := by
        intro x c hc hlen
        apply hno x c hc
        omega
      have htPath : (walk (e.nextDart w) t).IsPath :=
        ih (e.nextDart w) t hnoTail
      have htailNot : e.tail ∉ (walk (e.nextDart w) t).support := by
        have hrevNot : e.tail ∉ (walk (e.nextDart w) t).reverse.support := by
          apply Erdos795.SimpleGraph.Walk.IsPath.neighbor_not_mem_support_of_no_short_cycle
            htPath.reverse e.adj.symm
          · rw [SimpleGraph.Walk.penultimate_reverse, snd_walk]
            exact (Dart.mem_nextVertices.mp w.2).symm
          · intro x c hc hlen
            apply hno x c hc
            rw [SimpleGraph.Walk.length_reverse, length_walk] at hlen
            omega
        rw [SimpleGraph.Walk.support_reverse] at hrevNot
        simpa using hrevNot
      exact htPath.cons htailNot

def toRootedPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) {n : ℕ} (t : NBTrace G e n)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    RootedPath G e.tail (n + 1) := {
  endpoint := endpoint t
  walk := walk e t
  isPath := isPath_walk_of_no_short_cycle e t hno
  length_eq := length_walk e t }

theorem card_le_vertices_of_no_short_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : Dart G) (n : ℕ)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    Fintype.card (NBTrace G e n) ≤ Fintype.card V := by
  let f : NBTrace G e n → V := fun t ↦ (toRootedPath e t hno).endpoint
  apply Fintype.card_le_of_injective f
  intro t s hts
  have hp : toRootedPath e t hno = toRootedPath e s hno := by
    apply RootedPath.endpoint_injective_of_no_short_cycle hno
    exact hts
  apply eq_of_support_walk_eq e t s
  exact congrArg (fun p : RootedPath G e.tail (n + 1) ↦ p.walk.support) hp

end NBTrace

lemma Dart.card_eq_twice_card_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (Dart G) = 2 * G.edgeFinset.card := by
  rw [Fintype.card_sigma]
  simp_rw [G.card_neighborSet_eq_degree]
  exact G.sum_degrees_eq_twice_card_edges

namespace Dart

abbrev reverse {V : Type*} {G : SimpleGraph V} (e : Dart G) : Dart G :=
  ⟨e.head, e.tail, e.adj.symm⟩

@[simp] lemma reverse_reverse {V : Type*} {G : SimpleGraph V} (e : Dart G) :
    e.reverse.reverse = e := by
  cases e
  rfl

def reverseEquiv {V : Type*} (G : SimpleGraph V) : Dart G ≃ Dart G where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

end Dart

lemma sum_erase_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, ∑ y ∈ s.erase x, f y) =
      (s.card - 1 : ℕ) * ∑ y ∈ s, f y := by
  calc
    (∑ x ∈ s, ∑ y ∈ s.erase x, f y) =
        ∑ x ∈ s, ∑ y ∈ s, if y = x then 0 else f y := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.sum_erase_add _ (fun y ↦ if y = x then 0 else f y) hx]
          simp only [if_pos, add_zero]
          apply Finset.sum_congr rfl
          intro y hy
          have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
          simp [hyx]
    _ = ∑ y ∈ s, ∑ x ∈ s, if y = x then 0 else f y := by
          rw [Finset.sum_comm]
    _ = ∑ y ∈ s, (s.card - 1 : ℕ) * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.sum_erase_add _ _ hy]
          have hsum : (∑ x ∈ s.erase y, if y = x then 0 else f y) =
              ∑ _x ∈ s.erase y, f y := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxy : y ≠ x := (Finset.mem_erase.mp hx).1.symm
            simp [hxy]
          rw [hsum]
          simp [Finset.card_erase_of_mem hy]
    _ = (s.card - 1 : ℕ) * ∑ y ∈ s, f y := by
          rw [Finset.mul_sum]

lemma sum_erase_div_card_sub_one {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (hcard : 2 ≤ s.card) :
    (∑ x ∈ s, (∑ y ∈ s.erase x, f y) / (s.card - 1 : ℕ)) =
      ∑ y ∈ s, f y := by
  rw [← Finset.sum_div, sum_erase_sum]
  have hne : ((s.card - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < s.card - 1 := by omega
    exact_mod_cast (Nat.ne_of_gt this)
  field_simp

lemma sum_subtype_erase_div_card_sub_one {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (hcard : 2 ≤ s.card) :
    (∑ x : s, (∑ y : s.erase x.1, f y.1) / (s.card - 1 : ℕ)) =
      ∑ y : s, f y.1 := by
  rw [Finset.univ_eq_attach]
  calc
    (∑ x ∈ s.attach, (∑ y : s.erase x.1, f y.1) /
        (s.card - 1 : ℕ)) =
        ∑ x ∈ s.attach, (∑ y ∈ s.erase x.1, f y) /
          (s.card - 1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.univ_eq_attach, Finset.sum_attach]
    _ = ∑ x ∈ s, (∑ y ∈ s.erase x, f y) /
          (s.card - 1 : ℕ) := by
            exact Finset.sum_attach s (fun x ↦
              (∑ y ∈ s.erase x, f y) / (s.card - 1 : ℕ))
    _ = ∑ y ∈ s, f y := sum_erase_div_card_sub_one s f hcard
    _ = ∑ y ∈ s.attach, f y.1 := by
      symm
      exact Finset.sum_attach s f

lemma fintype_sum_erase_div_card_sub_one {α : Type*}
    [Fintype α] [DecidableEq α] (f : α → ℝ)
    (hcard : 2 ≤ Fintype.card α) :
    (∑ x : α, (∑ y : (Finset.univ.erase x : Finset α), f y.1) /
        (Fintype.card α - 1 : ℕ)) = ∑ y : α, f y := by
  calc
    (∑ x : α, (∑ y : (Finset.univ.erase x : Finset α), f y.1) /
        (Fintype.card α - 1 : ℕ)) =
        ∑ x ∈ (Finset.univ : Finset α),
          (∑ y ∈ Finset.univ.erase x, f y) /
            ((Finset.univ : Finset α).card - 1 : ℕ) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.univ_eq_attach, Finset.sum_attach]
              rfl
    _ = ∑ y ∈ (Finset.univ : Finset α), f y :=
      sum_erase_div_card_sub_one Finset.univ f (by simpa using hcard)
    _ = ∑ y : α, f y := rfl

lemma Dart.stationary_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : Dart G → ℝ) :
    (∑ e : Dart G,
      (∑ w : e.nextVertices, f (e.nextDart w)) /
        (e.nextVertices.card : ℝ)) = ∑ e : Dart G, f e := by
  let F : Dart G → ℝ := fun e ↦
    (∑ w : e.nextVertices, f (e.nextDart w)) /
      (e.nextVertices.card : ℝ)
  rw [show (∑ e : Dart G, F e) =
      ∑ e : Dart G, F ((Dart.reverseEquiv G) e) by
        exact ((Dart.reverseEquiv G).sum_comp F).symm]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  change (∑ v : V, ∑ u : G.neighborSet v,
      F (Dart.reverse (⟨v, u⟩ : Dart G))) =
    ∑ v : V, ∑ w : G.neighborSet v, f ⟨v, w⟩
  apply Finset.sum_congr rfl
  intro v hv
  have hcard : 2 ≤ Fintype.card (G.neighborSet v) := by
    rw [G.card_neighborSet_eq_degree v]
    exact hdeg v
  simp only [F, Dart.reverseEquiv, Dart.reverse, Dart.head, Dart.tail,
    Dart.nextVertices, Dart.nextDart, Subtype.coe_eta, Finset.card_erase_of_mem,
    Finset.mem_univ]
  change (∑ u : G.neighborSet v,
      (∑ w : (Finset.univ.erase u : Finset (G.neighborSet v)),
        f ⟨v, w.1.1, w.1.2⟩) /
          ((Finset.univ : Finset (G.neighborSet v)).card - 1 : ℕ)) =
    ∑ w : G.neighborSet v, f ⟨v, w⟩
  exact fintype_sum_erase_div_card_sub_one
    (fun w : G.neighborSet v ↦ f ⟨v, w⟩) hcard

lemma log_card_add_average_le_log_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hs : s.Nonempty) (hf : ∀ x ∈ s, 0 < f x) :
    Real.log (s.card : ℝ) +
        (∑ x ∈ s, Real.log (f x)) / (s.card : ℝ) ≤
      Real.log (∑ x ∈ s, f x) := by
  let d : ℝ := s.card
  let S : ℝ := ∑ x ∈ s, f x
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Finset.card_pos.mpr hs)
  have hS : 0 < S := Finset.sum_pos hf hs
  have hsum : (∑ x ∈ s, Real.log (d * f x / S)) ≤
      ∑ x ∈ s, (d * f x / S - 1) := by
    apply Finset.sum_le_sum
    intro x hx
    exact Real.log_le_sub_one_of_pos (div_pos (mul_pos hd (hf x hx)) hS)
  have hlhs : (∑ x ∈ s, Real.log (d * f x / S)) =
      d * Real.log d + (∑ x ∈ s, Real.log (f x)) -
        d * Real.log S := by
    calc
      (∑ x ∈ s, Real.log (d * f x / S)) =
          ∑ x ∈ s, (Real.log d + Real.log (f x) - Real.log S) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Real.log_div (mul_ne_zero hd.ne' (hf x hx).ne') hS.ne',
              Real.log_mul hd.ne' (hf x hx).ne']
      _ = d * Real.log d + (∑ x ∈ s, Real.log (f x)) -
          d * Real.log S := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.sum_const, nsmul_eq_mul]
            dsimp [d]
  have hrhs : (∑ x ∈ s, (d * f x / S - 1)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    dsimp [S] at hS
    dsimp [d, S]
    field_simp [hS.ne']
    ring
  have hmain : d * Real.log d + (∑ x ∈ s, Real.log (f x)) -
      d * Real.log S ≤ 0 := by
    rw [hlhs, hrhs] at hsum
    exact hsum
  have hmul :
      (Real.log (s.card : ℝ) +
          (∑ x ∈ s, Real.log (f x)) / (s.card : ℝ)) * d ≤
        Real.log (∑ x ∈ s, f x) * d := by
    dsimp [d, S] at hd hmain ⊢
    field_simp
    linarith
  nlinarith [hmul]

lemma fintype_log_card_add_average_le_log_sum
    {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ)
    (hα : Nonempty α) (hf : ∀ x, 0 < f x) :
    Real.log (Fintype.card α : ℝ) +
        (∑ x, Real.log (f x)) / (Fintype.card α : ℝ) ≤
      Real.log (∑ x, f x) := by
  simpa using log_card_add_average_le_log_sum
    (Finset.univ : Finset α) f ⟨Classical.choice hα, Finset.mem_univ _⟩
      (fun x _ ↦ hf x)

lemma NBTrace.log_card_next_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (e : Dart G) (n : ℕ) :
    Real.log (e.nextVertices.card : ℝ) +
        (∑ w : e.nextVertices,
            Real.log (Fintype.card (NBTrace G (e.nextDart w) n) : ℝ)) /
          (e.nextVertices.card : ℝ) ≤
      Real.log (Fintype.card (NBTrace G e (n + 1)) : ℝ) := by
  have hneFin : e.nextVertices.Nonempty :=
    Finset.card_pos.mp (e.card_pos_nextVertices_of_two_le_degree hdeg)
  obtain ⟨w₀, hw₀⟩ := hneFin
  let hne : Nonempty e.nextVertices := ⟨⟨w₀, hw₀⟩⟩
  have hpos : ∀ w : e.nextVertices,
      0 < (Fintype.card (NBTrace G (e.nextDart w) n) : ℝ) := by
    intro w
    exact_mod_cast NBTrace.card_pos_of_two_le_degree hdeg (e.nextDart w) n
  have h := fintype_log_card_add_average_le_log_sum
    (fun w : e.nextVertices ↦
      (Fintype.card (NBTrace G (e.nextDart w) n) : ℝ)) hne hpos
  rw [NBTrace.card_succ]
  norm_num at h ⊢
  exact h

lemma NBTrace.log_card_sum_succ_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (n : ℕ) :
    (∑ e : Dart G, Real.log (e.nextVertices.card : ℝ)) +
        (∑ e : Dart G,
          Real.log (Fintype.card (NBTrace G e n) : ℝ)) ≤
      ∑ e : Dart G,
        Real.log (Fintype.card (NBTrace G e (n + 1)) : ℝ) := by
  calc
    (∑ e : Dart G, Real.log (e.nextVertices.card : ℝ)) +
        (∑ e : Dart G,
          Real.log (Fintype.card (NBTrace G e n) : ℝ)) =
        ∑ e : Dart G,
          (Real.log (e.nextVertices.card : ℝ) +
            (∑ w : e.nextVertices,
              Real.log (Fintype.card (NBTrace G (e.nextDart w) n) : ℝ)) /
                (e.nextVertices.card : ℝ)) := by
          rw [Finset.sum_add_distrib]
          congr 1
          symm
          exact Dart.stationary_sum hdeg (fun e : Dart G ↦
            Real.log (Fintype.card (NBTrace G e n) : ℝ))
    _ ≤ ∑ e : Dart G,
        Real.log (Fintype.card (NBTrace G e (n + 1)) : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      exact NBTrace.log_card_next_le hdeg e n

lemma Dart.sum_log_card_nextVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ e : Dart G, Real.log (e.nextVertices.card : ℝ)) =
      ∑ v : V, (G.degree v : ℝ) *
        Real.log (G.degree v - 1 : ℕ) := by
  let f : Dart G → ℝ := fun e ↦ Real.log (e.nextVertices.card : ℝ)
  rw [show (∑ e : Dart G, f e) =
      ∑ e : Dart G, f ((Dart.reverseEquiv G) e) by
        exact ((Dart.reverseEquiv G).sum_comp f).symm]
  rw [Fintype.sum_sigma]
  simp only [f, Dart.card_nextVertices]
  change (∑ v : V, ∑ _y : G.neighborSet v,
      Real.log (G.degree v - 1 : ℕ)) = _
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    G.card_neighborSet_eq_degree]

lemma degree_sub_two_mul_log_two_le
    (d : ℕ) (hd : 2 ≤ d) :
    ((d - 2 : ℕ) : ℝ) * Real.log 2 ≤
      (d : ℝ) * Real.log (d - 1 : ℕ) := by
  by_cases htwo : d = 2
  · subst d
    norm_num [Real.log_one]
  · have hd3 : 3 ≤ d := by omega
    have hargNat : 2 ≤ d - 1 := by omega
    have harg : (2 : ℝ) ≤ (d - 1 : ℕ) := by exact_mod_cast hargNat
    have hlog : Real.log 2 ≤ Real.log (d - 1 : ℕ) :=
      Real.log_le_log (by norm_num) harg
    have hlogNonneg : 0 ≤ Real.log (d - 1 : ℕ) :=
      le_trans (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))) hlog
    calc
      ((d - 2 : ℕ) : ℝ) * Real.log 2 ≤
          ((d - 2 : ℕ) : ℝ) * Real.log (d - 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (d : ℝ) * Real.log (d - 1 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hlogNonneg
        exact_mod_cast Nat.sub_le d 2

lemma Dart.excess_mul_log_two_le_sum_log_next
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) {q : ℕ}
    (hexcess : Fintype.card V + q ≤ G.edgeFinset.card) :
    (2 * q : ℕ) * Real.log 2 ≤
      ∑ e : Dart G, Real.log (e.nextVertices.card : ℝ) := by
  have hpoint : (∑ v : V,
      ((G.degree v - 2 : ℕ) : ℝ) * Real.log 2) ≤
      ∑ v : V, (G.degree v : ℝ) *
        Real.log (G.degree v - 1 : ℕ) := by
    apply Finset.sum_le_sum
    intro v hv
    exact degree_sub_two_mul_log_two_le (G.degree v) (hdeg v)
  have hsumSub : (∑ v : V, ((G.degree v - 2 : ℕ) : ℝ)) =
      2 * (G.edgeFinset.card : ℝ) - 2 * (Fintype.card V : ℝ) := by
    simp_rw [Nat.cast_sub (hdeg _)]
    rw [Finset.sum_sub_distrib]
    have hdegSum : (∑ v : V, (G.degree v : ℝ)) =
        2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hdegSum]
    simp
    ring
  have hexcessReal :
      ((2 * q : ℕ) : ℝ) ≤
        2 * (G.edgeFinset.card : ℝ) - 2 * (Fintype.card V : ℝ) := by
    have h : (Fintype.card V : ℝ) + (q : ℝ) ≤
        (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hexcess
    norm_num at ⊢
    nlinarith
  rw [Dart.sum_log_card_nextVertices]
  have hscaled : (2 * q : ℕ) * Real.log 2 ≤
      (∑ v : V, ((G.degree v - 2 : ℕ) : ℝ)) * Real.log 2 := by
    rw [hsumSub]
    exact mul_le_mul_of_nonneg_right hexcessReal
      (le_of_lt (Real.log_pos (by norm_num)))
  calc
    (2 * q : ℕ) * Real.log 2 ≤
        (∑ v : V, ((G.degree v - 2 : ℕ) : ℝ)) * Real.log 2 := hscaled
    _ = ∑ v : V, ((G.degree v - 2 : ℕ) : ℝ) * Real.log 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ v : V, (G.degree v : ℝ) *
        Real.log (G.degree v - 1 : ℕ) := hpoint

lemma NBTrace.iterated_excess_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) {q : ℕ}
    (hexcess : Fintype.card V + q ≤ G.edgeFinset.card) (n : ℕ) :
    (n : ℝ) * (2 * q : ℕ) * Real.log 2 ≤
      ∑ e : Dart G,
        Real.log (Fintype.card (NBTrace G e n) : ℝ) := by
  induction n with
  | zero =>
      simp [NBTrace.card_zero]
  | succ n ih =>
      calc
        (n + 1 : ℕ) * (2 * q : ℕ) * Real.log 2 =
            (2 * q : ℕ) * Real.log 2 +
              (n : ℝ) * (2 * q : ℕ) * Real.log 2 := by
          push_cast
          ring
        _ ≤ (∑ e : Dart G, Real.log (e.nextVertices.card : ℝ)) +
              ∑ e : Dart G,
                Real.log (Fintype.card (NBTrace G e n) : ℝ) :=
          add_le_add (Dart.excess_mul_log_two_le_sum_log_next hdeg hexcess) ih
        _ ≤ ∑ e : Dart G,
            Real.log (Fintype.card (NBTrace G e (n + 1)) : ℝ) :=
          NBTrace.log_card_sum_succ_lower hdeg n

lemma NBTrace.log_card_sum_le_of_no_short_cycle
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (n : ℕ)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    (∑ e : Dart G,
        Real.log (Fintype.card (NBTrace G e n) : ℝ)) ≤
      (2 * G.edgeFinset.card : ℕ) * Real.log (Fintype.card V : ℝ) := by
  calc
    (∑ e : Dart G,
        Real.log (Fintype.card (NBTrace G e n) : ℝ)) ≤
        ∑ _e : Dart G, Real.log (Fintype.card V : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      by_cases ht : Fintype.card (NBTrace G e n) = 0
      · rw [ht]
        norm_num [Real.log_zero]
        apply Real.log_nonneg
        exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
      · apply Real.log_le_log
        · exact_mod_cast Nat.pos_of_ne_zero ht
        · exact_mod_cast NBTrace.card_le_vertices_of_no_short_cycle e n hno
    _ = (2 * G.edgeFinset.card : ℕ) *
        Real.log (Fintype.card V : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Dart.card_eq_twice_card_edges]

lemma Nat.lt_two_pow_log2_add_one (n : ℕ) (hn : n ≠ 0) :
    n < 2 ^ (n.log2 + 1) := by
  apply Nat.lt_of_not_ge
  intro h
  have : n.log2 + 1 ≤ n.log2 := (Nat.le_log2 hn).2 h
  omega

lemma log_nat_le_log2_add_one_mul_log_two (n : ℕ) (hn : n ≠ 0) :
    Real.log (n : ℝ) ≤ (n.log2 + 1 : ℕ) * Real.log 2 := by
  have hpowNat : n ≤ 2 ^ (n.log2 + 1) :=
    (Nat.lt_two_pow_log2_add_one n hn).le
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpowReal : (n : ℝ) ≤ (2 : ℝ) ^ (n.log2 + 1) := by
    exact_mod_cast hpowNat
  calc
    Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (n.log2 + 1)) :=
      Real.log_le_log hnReal hpowReal
    _ = (n.log2 + 1 : ℕ) * Real.log 2 := Real.log_pow 2 _

lemma NBTrace.moore_real_inequality
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) {q n : ℕ}
    (hexcess : Fintype.card V + q ≤ G.edgeFinset.card)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    (n : ℝ) * (2 * q : ℕ) * Real.log 2 ≤
      (2 * G.edgeFinset.card : ℕ) *
        Real.log (Fintype.card V : ℝ) :=
  (NBTrace.iterated_excess_lower hdeg hexcess n).trans
    (NBTrace.log_card_sum_le_of_no_short_cycle n hno)

lemma NBTrace.moore_excess_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) {q n : ℕ}
    (hexcess : Fintype.card V + q ≤ G.edgeFinset.card)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    n * q ≤ G.edgeFinset.card * (Nat.log2 (Fintype.card V) + 1) := by
  have hreal := NBTrace.moore_real_inequality hdeg hexcess hno
  have hlog := log_nat_le_log2_add_one_mul_log_two
    (Fintype.card V) (Fintype.card_ne_zero)
  have hupper :
      (2 * G.edgeFinset.card : ℕ) * Real.log (Fintype.card V : ℝ) ≤
        (2 * G.edgeFinset.card : ℕ) *
          ((Nat.log2 (Fintype.card V) + 1 : ℕ) * Real.log 2) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hchain := hreal.trans hupper
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((n * q : ℕ) : ℝ) ≤
      (G.edgeFinset.card * (Nat.log2 (Fintype.card V) + 1) : ℕ) := by
    push_cast at hchain ⊢
    nlinarith
  exact_mod_cast hcast

lemma induced_edge_card_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) {x : V} (hx : x ∈ s) :
    (G.induce (↑(s.erase x) : Set V)).edgeFinset.card =
      (G.induce (↑s : Set V)).edgeFinset.card -
        (G.induce (↑s : Set V)).degree ⟨x, hx⟩ := by
  let F : Finset (Sym2 V) := {e ∈ G.edgeFinset | e.toFinset ⊆ s}
  let F' : Finset (Sym2 V) :=
    {e ∈ G.edgeFinset | e.toFinset ⊆ s.erase x}
  have hF : F.card = (G.induce (↑s : Set V)).edgeFinset.card := by
    exact G.card_filter_edgeFinset_toFinset_subset s
  have hF' : F'.card =
      (G.induce (↑(s.erase x) : Set V)).edgeFinset.card := by
    exact G.card_filter_edgeFinset_toFinset_subset (s.erase x)
  have hdiff : F' = F \ G.incidenceFinset x := by
    ext e
    simp only [F, F', Finset.mem_filter, Finset.mem_sdiff,
      SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨he, hall⟩
      refine ⟨⟨he, fun y hy ↦ (Finset.mem_erase.mp (hall hy)).2⟩, ?_⟩
      intro hinc
      have heSet : e ∈ G.edgeSet := G.mem_edgeFinset.mp he
      have hxmem : x ∈ e :=
        (G.edge_mem_incidenceSet_iff (e := ⟨e, heSet⟩)).mp hinc
      have hxerase : x ∈ s.erase x := hall (Sym2.mem_toFinset.mpr hxmem)
      exact (Finset.mem_erase.mp hxerase).1 rfl
    · rintro ⟨⟨he, hall⟩, hxnot⟩
      refine ⟨he, fun y hy ↦ Finset.mem_erase.mpr ⟨?_, hall hy⟩⟩
      intro hyx
      subst y
      have heSet : e ∈ G.edgeSet := G.mem_edgeFinset.mp he
      apply hxnot
      exact (G.edge_mem_incidenceSet_iff (e := ⟨e, heSet⟩)).mpr
        (Sym2.mem_toFinset.mp hy)
  let H : SimpleGraph (↑s : Set V) := G.induce (↑s : Set V)
  let ι : (↑s : Set V) ↪ V := Function.Embedding.subtype _
  have hinc :
      (H.incidenceFinset ⟨x, hx⟩).map ι.sym2Map =
        G.incidenceFinset x ∩ F := by
    have hadj : ∀ {a b : V}, G.Adj a b → G.Adj b a :=
      fun {_ _} h ↦ h.symm
    ext e
    cases e using Sym2.inductionOn with
    | _ a b =>
    simp [H, ι, F, H.incidenceFinset_eq_filter,
      G.incidenceFinset_eq_filter, G.map_edgeFinset_induce,
      Finset.subset_iff, Sym2.exists, Function.Embedding.subtype_apply]
    aesop
  rw [← hF', hdiff, Finset.card_sdiff]
  have hcardInc : (G.incidenceFinset x ∩ F).card = H.degree ⟨x, hx⟩ := by
    rw [← hinc, Finset.card_map, H.card_incidenceFinset_eq_degree]
  rw [hcardInc, hF]

lemma exists_min_degree_two_induced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hq : 0 < q) (hexcess : Fintype.card V + q ≤ G.edgeFinset.card) :
    ∃ s : Finset V,
      s.Nonempty ∧
      s.card + q ≤ (G.induce (↑s : Set V)).edgeFinset.card ∧
      ∀ v : (↑s : Set V), 2 ≤ (G.induce (↑s : Set V)).degree v := by
  classical
  let Good : Finset V → Prop := fun s ↦
    s.card + q ≤ (G.induce (↑s : Set V)).edgeFinset.card
  let P : ℕ → Prop := fun k ↦ ∃ s : Finset V, s.card = k ∧ Good s
  let : DecidablePred P := Classical.decPred P
  have hP : ∃ k, P k := by
    refine ⟨Fintype.card V, Finset.univ, Finset.card_univ, ?_⟩
    dsimp [Good]
    have hedge : (G.induce ((↑(Finset.univ : Finset V)) : Set V)).edgeFinset.card =
        G.edgeFinset.card := by
      have h := G.card_filter_edgeFinset_toFinset_subset
        (Finset.univ : Finset V)
      simpa using h.symm
    simpa [hedge] using hexcess
  obtain ⟨s, hsk, hsGood⟩ := Nat.find_spec hP
  have hminimal {t : Finset V} (ht : Good t) : s.card ≤ t.card := by
    rw [hsk]
    exact Nat.find_min' hP ⟨t, rfl, ht⟩
  have hsNonempty : s.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst s
    have hedgeEmpty :
        (G.induce ((↑(∅ : Finset V)) : Set V)).edgeFinset.card = 0 := by
      have hle := (G.induce ((↑(∅ : Finset V)) : Set V)).card_edgeFinset_le_card_choose_two
      simpa using hle
    dsimp [Good] at hsGood
    rw [hedgeEmpty] at hsGood
    omega
  refine ⟨s, hsNonempty, hsGood, ?_⟩
  intro v
  by_contra hv
  have hvle : (G.induce (↑s : Set V)).degree v ≤ 1 := by omega
  let t : Finset V := s.erase v.1
  have htcard : t.card = s.card - 1 := by
    dsimp [t]
    exact Finset.card_erase_of_mem v.2
  have htcardAdd : t.card + 1 = s.card := by
    dsimp [t]
    exact Finset.card_erase_add_one v.2
  have hedgeErase : (G.induce (↑t : Set V)).edgeFinset.card =
      (G.induce (↑s : Set V)).edgeFinset.card -
        (G.induce (↑s : Set V)).degree v := by
    exact induced_edge_card_erase G s v.2
  have htGood : Good t := by
    dsimp [Good]
    rw [hedgeErase]
    have hdEdge := (G.induce (↑s : Set V)).degree_le_card_edgeFinset v
    omega
  have hcardMin := hminimal htGood
  omega

lemma Nat.log2_mono_of_le {a b : ℕ} (hab : a ≤ b) :
    Nat.log2 a ≤ Nat.log2 b := by
  by_cases ha : a = 0
  · simp [ha]
  · have hb : b ≠ 0 := fun hb ↦ ha (Nat.eq_zero_of_le_zero (hb ▸ hab))
    apply (Nat.le_log2 hb).2
    exact ((Nat.le_log2 ha).1 le_rfl).trans hab

lemma moore_excess_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {q n : ℕ}
    (hq : 0 < q)
    (hexcess : Fintype.card V + q ≤ G.edgeFinset.card)
    (hno : ∀ x : V, ∀ c : G.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    n * q ≤ G.edgeFinset.card * (Nat.log2 (Fintype.card V) + 1) := by
  obtain ⟨s, hsne, hsExcess, hsDeg⟩ :=
    exists_min_degree_two_induced G hq hexcess
  let H : SimpleGraph (↑s : Set V) := G.induce (↑s : Set V)
  let ι : H →g G := {
    toFun := Subtype.val
    map_rel' := fun {_ _} h ↦ h }
  have hnoH : ∀ x : (↑s : Set V), ∀ c : H.Walk x x,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False := by
    intro x c hc hlen
    apply hno x.1 (c.map ι)
    · exact hc.map Subtype.val_injective
    · simpa using hlen
  let : Nonempty (↑s : Set V) := hsne.to_subtype
  have hcardS : Fintype.card (↑s : Set V) = s.card := by
    change Fintype.card ↑s = s.card
    exact Fintype.card_coe s
  have hcore : n * q ≤ H.edgeFinset.card *
      (Nat.log2 (Fintype.card (↑s : Set V)) + 1) := by
    apply NBTrace.moore_excess_le hsDeg (by simpa [hcardS] using hsExcess) hnoH
  have hEdge : H.edgeFinset.card ≤ G.edgeFinset.card := by
    have hcard := G.card_filter_edgeFinset_toFinset_subset s
    change (G.induce (↑s : Set V)).edgeFinset.card ≤ G.edgeFinset.card
    rw [← hcard]
    exact Finset.card_filter_le _ _
  have hVert : Fintype.card (↑s : Set V) ≤ Fintype.card V := by
    rw [hcardS]
    exact Finset.card_le_univ s
  exact hcore.trans (Nat.mul_le_mul hEdge
    (Nat.add_le_add_right (Nat.log2_mono_of_le hVert) 1))

/-! ## Finite vertex models for the product graph -/

/-- Every endpoint used by the product graph is either the auxiliary
vertex `1` or a high prime. -/
def graphVertices (N : ℕ) : Finset ℕ := insert 1 (highPrimes N)

lemma elementEdgeSet_subset_graphVertices (N a : ℕ) :
    elementEdgeSet N a ⊆ graphVertices N := by
  intro p hp
  by_cases hcard : (highFactorization N a).support.card = 1
  · simp only [elementEdgeSet, hcard, if_true, graphVertices,
      Finset.mem_insert] at hp ⊢
    exact hp.elim Or.inl (fun h ↦ Or.inr (highFactorization_support_subset N a h))
  · simp only [elementEdgeSet, hcard, if_false, graphVertices,
      Finset.mem_insert] at hp ⊢
    exact Or.inr (highFactorization_support_subset N a hp)

lemma productGraph_support_subset_graphVertices
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (productGraph N A).support ⊆ (↑(graphVertices N) : Set ℕ) := by
  intro p hp
  rw [SimpleGraph.mem_support] at hp
  obtain ⟨q, hpq⟩ := hp
  have hedge : s(p, q) ∈ (productGraph N A).edgeSet := by
    simpa using hpq
  rw [productGraph_edgeSet hAN hnonzero] at hedge
  obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hedge
  have haA := (Finset.mem_filter.mp ha).1
  have hanot := (Finset.mem_filter.mp ha).2
  have haI := Finset.mem_Icc.mp (hAN haA)
  have hacard := elementEdgeSet_card haI.1 haI.2 (hnonzero a haA) hanot
  have hpEdge : p ∈ (elementEdge N a).toFinset := by
    rw [hea]
    simp
  rw [elementEdge_toFinset hacard] at hpEdge
  exact elementEdgeSet_subset_graphVertices N a hpEdge

lemma graphVertices_card (N : ℕ) :
    (graphVertices N).card = (highPrimes N).card + 1 := by
  rw [graphVertices, Finset.card_insert_of_notMem]
  intro h
  rw [highPrimes_eq, Finset.mem_sdiff] at h
  exact Nat.not_prime_one (mem_primesUpTo.mp h.1).2.2

lemma productEdge_toFinset_subset_graphVertices
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {e : Sym2 ℕ} (he : e ∈ productEdgeFinset N A) :
    e.toFinset ⊆ graphVertices N := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have haA := (Finset.mem_filter.mp ha).1
  have hanot := (Finset.mem_filter.mp ha).2
  have haI := Finset.mem_Icc.mp (hAN haA)
  have hacard := elementEdgeSet_card haI.1 haI.2 (hnonzero a haA) hanot
  rw [elementEdge_toFinset hacard]
  exact elementEdgeSet_subset_graphVertices N a

/-- Lift an unordered pair to a finite subtype containing both endpoints. -/
private lemma exists_liftSym2ToFinset {V : Type*} [DecidableEq V]
    (s : Finset V) (e : Sym2 V) (h : e.toFinset ⊆ s) :
    ∃ d : Sym2 (↑s),
      (Function.Embedding.subtype (fun x ↦ x ∈ s)).sym2Map d = e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      exact ⟨s(⟨a, h (by simp)⟩, ⟨b, h (by simp)⟩), rfl⟩

noncomputable def liftSym2ToFinset {V : Type*} [DecidableEq V]
    (s : Finset V) (e : Sym2 V) (h : e.toFinset ⊆ s) : Sym2 (↑s) :=
  Classical.choose (exists_liftSym2ToFinset s e h)

@[simp] lemma map_liftSym2ToFinset {V : Type*} [DecidableEq V]
    (s : Finset V) (e : Sym2 V) (h : e.toFinset ⊆ s) :
    (Function.Embedding.subtype (fun x ↦ x ∈ s)).sym2Map
      (liftSym2ToFinset s e h) = e := by
  exact Classical.choose_spec (exists_liftSym2ToFinset s e h)

abbrev ProductEdge (N : ℕ) (A : Finset ℕ) :=
  {e // e ∈ productEdgeFinset N A}

noncomputable def finiteProductEdge
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (e : ProductEdge N A) : Sym2 (↑(graphVertices N)) :=
  liftSym2ToFinset (graphVertices N) e.1
    (productEdge_toFinset_subset_graphVertices hAN hnonzero e.2)

lemma finiteProductEdge_injective
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Function.Injective (finiteProductEdge hAN hnonzero) := by
  intro e f hef
  apply Subtype.ext
  let ι := (Function.Embedding.subtype
    (fun x ↦ x ∈ graphVertices N)).sym2Map
  calc
    e.1 = ι (finiteProductEdge hAN hnonzero e) := by
      symm
      exact map_liftSym2ToFinset _ _ _
    _ = ι (finiteProductEdge hAN hnonzero f) := congrArg ι hef
    _ = f.1 := map_liftSym2ToFinset _ _ _

def finiteProductEdgeFinset
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Finset (Sym2 (↑(graphVertices N))) :=
  Finset.univ.image (finiteProductEdge hAN hnonzero)

def finiteProductGraph
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    SimpleGraph (↑(graphVertices N)) :=
  SimpleGraph.fromEdgeSet (finiteProductEdgeFinset hAN hnonzero :
    Set (Sym2 (↑(graphVertices N))))

lemma finiteProductEdgeFinset_card
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (finiteProductEdgeFinset hAN hnonzero).card =
      (productEdgeFinset N A).card := by
  rw [finiteProductEdgeFinset, Finset.card_image_of_injective]
  · exact Fintype.card_coe _
  · exact finiteProductEdge_injective hAN hnonzero

lemma finiteProductEdgeFinset_disjoint_diag
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Disjoint (finiteProductEdgeFinset hAN hnonzero :
      Set (Sym2 (↑(graphVertices N)))) Sym2.diagSet := by
  rw [Set.disjoint_left]
  intro e he hdiag
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  have hmapDiag :
      (Function.Embedding.subtype
        (fun x ↦ x ∈ graphVertices N)).sym2Map
          (finiteProductEdge hAN hnonzero f) ∈ Sym2.diagSet :=
    (Sym2.mem_diagSet.mp hdiag).map
  have hmap :
      (Function.Embedding.subtype
        (fun x ↦ x ∈ graphVertices N)).sym2Map
          (finiteProductEdge hAN hnonzero f) = f.1 := by
    exact map_liftSym2ToFinset _ _ _
  rw [hmap] at hmapDiag
  exact Set.disjoint_left.mp (productEdgeFinset_disjoint_diag hAN hnonzero)
    f.2 hmapDiag

lemma finiteProductGraph_edgeFinset
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (finiteProductGraph hAN hnonzero).edgeFinset =
      finiteProductEdgeFinset hAN hnonzero := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  change (finiteProductGraph hAN hnonzero).edgeSet = _
  rw [finiteProductGraph, SimpleGraph.edgeSet_fromEdgeSet,
    (finiteProductEdgeFinset_disjoint_diag hAN hnonzero).sdiff_eq_left]

lemma finiteProductGraph_card_edges
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (finiteProductGraph hAN hnonzero).edgeFinset.card =
      (productGraph N A).edgeFinset.card := by
  rw [finiteProductGraph_edgeFinset hAN hnonzero,
    finiteProductEdgeFinset_card hAN hnonzero,
    productGraph_edgeFinset hAN hnonzero]

/-! ## Recurrent large vertices -/

def nonlargeVertices (N : ℕ) : Finset ℕ := insert 1 (mediumPrimes N)

lemma one_not_mem_mediumPrimes (N : ℕ) : 1 ∉ mediumPrimes N := by
  intro h
  exact (mem_mediumPrimes.mp h).2.2.2.ne_one rfl

lemma card_nonlargeVertices (N : ℕ) :
    (nonlargeVertices N).card = (mediumPrimes N).card + 1 := by
  exact Finset.card_insert_of_notMem (one_not_mem_mediumPrimes N)

def residualProductGraph (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) : SimpleGraph ℕ :=
  (productGraph N A).deleteEdges D

noncomputable instance residualProductGraph.fintypeEdgeSet'
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    Fintype (residualProductGraph N A D).edgeSet := by
  dsimp [residualProductGraph]
  exact residualProductGraph.fintypeEdgeSet N A D

noncomputable instance residualProductGraph.fintypeNeighborSet
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) (q : ℕ) :
    Fintype ((residualProductGraph N A D).neighborSet q) := by
  let G := residualProductGraph N A D
  letI : Fintype G.edgeSet := by
    dsimp [G, residualProductGraph]
    exact residualProductGraph.fintypeEdgeSet N A D
  letI : Fintype (G.incidenceSet q) := by
    apply Set.Finite.fintype
    exact (Set.toFinite G.edgeSet).subset (G.incidenceSet_subset q)
  exact Fintype.ofEquiv (G.incidenceSet q) (G.incidenceSetEquivNeighborSet q)

def recurrentLarge (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) : Finset ℕ :=
  (largePrimes N).filter fun q ↦ 2 ≤ (residualProductGraph N A D).degree q

@[simp] lemma mem_recurrentLarge {N : ℕ} {A : Finset ℕ}
    {D : Finset (Sym2 ℕ)} {q : ℕ} :
    q ∈ recurrentLarge N A D ↔ q ∈ largePrimes N ∧
      2 ≤ (residualProductGraph N A D).degree q := by
  simp [recurrentLarge]

lemma residual_adj_productGraph
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)} {u v : ℕ}
    (h : (residualProductGraph N A D).Adj u v) :
    (productGraph N A).Adj u v := by
  exact h.1

lemma neighbor_of_large_mem_nonlarge
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {q v : ℕ} (hq : q ∈ largePrimes N)
    (hqv : (residualProductGraph N A D).Adj q v) :
    v ∈ nonlargeVertices N := by
  have hqvG : (productGraph N A).Adj q v := residual_adj_productGraph hqv
  have hvSupp : v ∈ (productGraph N A).support := by
    rw [SimpleGraph.mem_support]
    exact ⟨q, hqvG.symm⟩
  have hvVert := productGraph_support_subset_graphVertices hAN hnonzero hvSupp
  simp only [graphVertices, Finset.coe_insert, Finset.coe_sort_coe,
    Set.mem_insert_iff] at hvVert
  rcases hvVert with rfl | hvHigh
  · exact Finset.mem_insert_self _ _
  · rw [highPrimes] at hvHigh
    rcases Finset.mem_union.mp hvHigh with hvMed | hvLarge
    · exact Finset.mem_insert_of_mem hvMed
    · exact (productGraph_no_adj_large_large hAN hnonzero hq hvLarge hqvG).elim

structure LargeNeighborPair
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) (q : ℕ) where
  first : ℕ
  second : ℕ
  first_adj : (residualProductGraph N A D).Adj q first
  second_adj : (residualProductGraph N A D).Adj q second
  ne : first ≠ second

lemma largeNeighborPair_nonempty
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    {q : ℕ} (hq : 2 ≤ (residualProductGraph N A D).degree q) :
    Nonempty (LargeNeighborPair N A D q) := by
  have hcard : 1 < ((residualProductGraph N A D).neighborFinset q).card := by
    rw [(residualProductGraph N A D).card_neighborFinset_eq_degree]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  exact ⟨{
    first := u
    second := v
    first_adj := ((residualProductGraph N A D).mem_neighborFinset q u).mp hu
    second_adj := ((residualProductGraph N A D).mem_neighborFinset q v).mp hv
    ne := huv }⟩

noncomputable def chosenLargeNeighbors
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (q : recurrentLarge N A D) : LargeNeighborPair N A D q.1 :=
  Classical.choice (largeNeighborPair_nonempty (mem_recurrentLarge.mp q.2).2)

noncomputable def chosenLargeNeighbor
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (q : recurrentLarge N A D) (b : Bool) : nonlargeVertices N :=
  if b then
    ⟨(chosenLargeNeighbors q).first,
      neighbor_of_large_mem_nonlarge hAN hnonzero
        (mem_recurrentLarge.mp q.2).1 (chosenLargeNeighbors q).first_adj⟩
  else
    ⟨(chosenLargeNeighbors q).second,
      neighbor_of_large_mem_nonlarge hAN hnonzero
        (mem_recurrentLarge.mp q.2).1 (chosenLargeNeighbors q).second_adj⟩

lemma chosenLargeNeighbor_injective
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (q : recurrentLarge N A D) :
    Function.Injective (chosenLargeNeighbor hAN hnonzero q) := by
  intro b c hbc
  cases b <;> cases c
  · rfl
  · exfalso
    exact (chosenLargeNeighbors q).ne (congrArg Subtype.val hbc).symm
  · exfalso
    exact (chosenLargeNeighbors q).ne (congrArg Subtype.val hbc)
  · rfl

lemma chosenLargeNeighbor_adj
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (q : recurrentLarge N A D) (b : Bool) :
    (residualProductGraph N A D).Adj q.1
      (chosenLargeNeighbor hAN hnonzero q b).1 := by
  cases b <;> simp [chosenLargeNeighbor,
    (chosenLargeNeighbors q).first_adj,
    (chosenLargeNeighbors q).second_adj]

abbrev AuxiliaryVertex (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) :=
  recurrentLarge N A D ⊕ nonlargeVertices N

noncomputable def auxiliaryEdge
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (qb : recurrentLarge N A D × Bool) :
    Sym2 (AuxiliaryVertex N A D) :=
  s(Sum.inl qb.1, Sum.inr (chosenLargeNeighbor hAN hnonzero qb.1 qb.2))

lemma auxiliaryEdge_injective
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Function.Injective (auxiliaryEdge (D := D) hAN hnonzero) := by
  rintro ⟨q, b⟩ ⟨r, c⟩ h
  have hor := Sym2.eq_iff.mp h
  rcases hor with hsame | hswap
  · have hqr : q = r := Sum.inl_injective hsame.1
    subst r
    have hbc : b = c := chosenLargeNeighbor_injective hAN hnonzero q
      (Sum.inr_injective hsame.2)
    subst c
    rfl
  · exact (Sum.inl_ne_inr hswap.1).elim

def auxiliaryEdgeFinset
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Finset (Sym2 (AuxiliaryVertex N A D)) :=
  Finset.univ.image (auxiliaryEdge (D := D) hAN hnonzero)

def auxiliaryGraph
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    SimpleGraph (AuxiliaryVertex N A D) :=
  SimpleGraph.fromEdgeSet (auxiliaryEdgeFinset (D := D) hAN hnonzero : Set _)

lemma auxiliaryEdgeFinset_disjoint_diag
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    Disjoint (auxiliaryEdgeFinset (D := D) hAN hnonzero : Set _)
      (Sym2.diagSet : Set (Sym2 (AuxiliaryVertex N A D))) := by
  rw [Set.disjoint_left]
  intro e he hdiag
  obtain ⟨⟨q, b⟩, hqb, rfl⟩ := Finset.mem_image.mp he
  rw [Sym2.mem_diagSet] at hdiag
  exact Sum.inl_ne_inr hdiag

lemma auxiliaryGraph_edgeFinset
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (auxiliaryGraph (D := D) hAN hnonzero).edgeFinset =
      auxiliaryEdgeFinset (D := D) hAN hnonzero := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  rw [auxiliaryGraph, SimpleGraph.edgeSet_fromEdgeSet,
    (auxiliaryEdgeFinset_disjoint_diag (D := D) hAN hnonzero).sdiff_eq_left]

lemma auxiliaryGraph_card_edges
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (auxiliaryGraph (D := D) hAN hnonzero).edgeFinset.card =
      2 * (recurrentLarge N A D).card := by
  rw [auxiliaryGraph_edgeFinset (D := D) hAN hnonzero, auxiliaryEdgeFinset,
    Finset.card_image_of_injective]
  · simp [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]
  · exact auxiliaryEdge_injective (D := D) hAN hnonzero

def auxiliaryVertexMap
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)} :
    AuxiliaryVertex N A D → ℕ
  | Sum.inl q => q.1
  | Sum.inr m => m.1

lemma auxiliaryVertexMap_injective
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)} :
    Function.Injective (auxiliaryVertexMap : AuxiliaryVertex N A D → ℕ) := by
  intro x y hxy
  rcases x with q | m
  · rcases y with r | t
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exfalso
      change q.1 = t.1 at hxy
      have hq := (mem_recurrentLarge.mp q.2).1
      have hm := t.2
      simp only [nonlargeVertices, Finset.mem_insert] at hm
      rcases hm with hm | hm
      · exact Nat.Prime.ne_one (mem_largePrimes.mp hq).2.2.2 (hxy.trans hm)
      · have hmed := mem_mediumPrimes.mp hm
        have hlarge := mem_largePrimes.mp hq
        omega
  · rcases y with r | t
    · exfalso
      change m.1 = r.1 at hxy
      have hr := (mem_recurrentLarge.mp r.2).1
      have hm := m.2
      simp only [nonlargeVertices, Finset.mem_insert] at hm
      rcases hm with hm | hm
      · exact Nat.Prime.ne_one (mem_largePrimes.mp hr).2.2.2 (hxy.symm.trans hm)
      · have hmed := mem_mediumPrimes.mp hm
        have hlarge := mem_largePrimes.mp hr
        omega
    · exact congrArg Sum.inr (Subtype.ext hxy)

def auxiliaryHom
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    auxiliaryGraph (D := D) hAN hnonzero →g residualProductGraph N A D where
  toFun := auxiliaryVertexMap
  map_rel' := by
    intro x y hxy
    have hedge : s(x, y) ∈ auxiliaryEdgeFinset (D := D) hAN hnonzero := by
      have hxy' := hxy
      rw [auxiliaryGraph, SimpleGraph.fromEdgeSet_adj] at hxy'
      exact hxy'.1
    obtain ⟨⟨q, b⟩, hqb, heq⟩ := Finset.mem_image.mp hedge
    rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [← hx, ← hy]
      exact chosenLargeNeighbor_adj hAN hnonzero q b
    · rw [← hy, ← hx]
      exact (chosenLargeNeighbor_adj hAN hnonzero q b).symm

/-! The selected incidence graph is bipartite.  We record the parity
argument directly for walks, since the subsequent Moore application needs
the quantitative fact that every cycle transported to the product graph is
an even circuit. -/

lemma SimpleGraph.Walk.length_mod_two_of_bicoloring
    {V : Type*} {G : SimpleGraph V} (color : V → Bool)
    (hcolor : ∀ {u v : V}, G.Adj u v → color u ≠ color v)
    {u v : V} (w : G.Walk u v) :
    w.length % 2 = if color u = color v then 0 else 1 := by
  induction w with
  | nil => simp
  | @cons u v z huv p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.add_mod, ih]
      have huv' := hcolor huv
      cases hu : color u <;> cases hv : color v <;>
        cases hz : color z <;> simp_all

lemma SimpleGraph.Walk.even_length_of_bicoloring
    {V : Type*} {G : SimpleGraph V} (color : V → Bool)
    (hcolor : ∀ {u v : V}, G.Adj u v → color u ≠ color v)
    {u : V} (w : G.Walk u u) : Even w.length := by
  rw [Nat.even_iff]
  simpa using SimpleGraph.Walk.length_mod_two_of_bicoloring color hcolor w

lemma SimpleGraph.Walk.length_mod_two_of_edges_bicoloring
    {V : Type*} {G : SimpleGraph V} (color : V → Bool)
    {u v : V} (w : G.Walk u v)
    (hcolor : ∀ {a b : V}, s(a, b) ∈ w.edges → color a ≠ color b) :
    w.length % 2 = if color u = color v then 0 else 1 := by
  induction w with
  | nil => simp
  | @cons u v z huv p ih =>
      have huv' : color u ≠ color v := hcolor (by simp)
      have hp : ∀ {a b : V}, s(a, b) ∈ p.edges → color a ≠ color b := by
        intro a b hab
        exact hcolor (by simp [hab])
      rw [SimpleGraph.Walk.length_cons, Nat.add_mod, ih hp]
      cases hu : color u <;> cases hv : color v <;>
        cases hz : color z <;> simp_all

lemma SimpleGraph.Walk.even_length_of_edges_bicoloring
    {V : Type*} {G : SimpleGraph V} (color : V → Bool)
    {u : V} (w : G.Walk u u)
    (hcolor : ∀ {a b : V}, s(a, b) ∈ w.edges → color a ≠ color b) :
    Even w.length := by
  rw [Nat.even_iff]
  simpa using SimpleGraph.Walk.length_mod_two_of_edges_bicoloring color w hcolor

lemma productGraph_support_mem_nonlarge_or_large
    {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {v : ℕ} (hv : v ∈ (productGraph N A).support) :
    v ∈ nonlargeVertices N ∨ v ∈ largePrimes N := by
  have hv' := productGraph_support_subset_graphVertices hAN hnonzero hv
  simp only [graphVertices, Finset.coe_insert, Set.mem_insert_iff] at hv'
  rcases hv' with rfl | hv'
  · exact Or.inl (Finset.mem_insert_self _ _)
  · rw [highPrimes] at hv'
    rcases Finset.mem_union.mp hv' with hv' | hv'
    · exact Or.inl (Finset.mem_insert_of_mem hv')
    · exact Or.inr hv'

lemma residual_adj_endpoint_classification
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : ℕ} (huv : (residualProductGraph N A D).Adj u v) :
    (u ∈ nonlargeVertices N ∨ u ∈ largePrimes N) ∧
      (v ∈ nonlargeVertices N ∨ v ∈ largePrimes N) := by
  have huvG : (productGraph N A).Adj u v := residual_adj_productGraph huv
  constructor
  · apply productGraph_support_mem_nonlarge_or_large hAN hnonzero
    rw [SimpleGraph.mem_support]
    exact ⟨v, huvG⟩
  · apply productGraph_support_mem_nonlarge_or_large hAN hnonzero
    rw [SimpleGraph.mem_support]
    exact ⟨u, huvG.symm⟩

lemma nonlargeVertices_disjoint_largePrimes (N : ℕ) :
    Disjoint (nonlargeVertices N) (largePrimes N) := by
  rw [Finset.disjoint_left]
  intro v hvn hvl
  rcases Finset.mem_insert.mp hvn with rfl | hvm
  · exact (mem_largePrimes.mp hvl).2.2.2.ne_one rfl
  · exact Finset.disjoint_left.mp (mediumPrimes_disjoint_largePrimes N) hvm hvl

def largeColor (N v : ℕ) : Bool := decide (v ∈ largePrimes N)

/-- An odd cycle in the product graph cannot alternate between large and
nonlarge vertices, so it contains an edge whose two endpoints are both in
the medium/special colour class. -/
lemma oddCycle_exists_nonlarge_edge
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u : ℕ} (c : (residualProductGraph N A D).Walk u u)
    (hodd : Odd c.length) :
    ∃ a b : ℕ, s(a, b) ∈ c.edges ∧
      a ∈ nonlargeVertices N ∧ b ∈ nonlargeVertices N := by
  by_contra h
  push_neg at h
  have hcolor : ∀ {a b : ℕ}, s(a, b) ∈ c.edges →
      largeColor N a ≠ largeColor N b := by
    intro a b hab
    have habAdj : (residualProductGraph N A D).Adj a b := by
      exact c.adj_of_mem_edges hab
    obtain ⟨ha, hb⟩ := residual_adj_endpoint_classification hAN hnonzero habAdj
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (h a b hab ha hb).elim
    · have hna : a ∉ largePrimes N :=
        Finset.disjoint_left.mp (nonlargeVertices_disjoint_largePrimes N) ha
      simp [largeColor, hna, hb]
    · have hnb : b ∉ largePrimes N :=
        Finset.disjoint_left.mp (nonlargeVertices_disjoint_largePrimes N) hb
      simp [largeColor, ha, hnb]
    · exact (productGraph_no_adj_large_large hAN hnonzero
        ha hb (residual_adj_productGraph habAdj)).elim
  have heven : Even c.length :=
    SimpleGraph.Walk.even_length_of_edges_bicoloring (largeColor N) c hcolor
  exact Nat.not_even_iff_odd.mpr hodd heven

lemma shortOddCycle_support_disjoint_squarePrimeSet
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    {u : ℕ} {c : (residualProductGraph N A D).Walk u u}
    (hc : c.IsCycle) (hodd : Odd c.length) (hlen : c.length ≤ L) :
    c.support.Disjoint (squarePrimeSet N A).toList := by
  rw [List.disjoint_left]
  intro p hpc hpSq
  have hpSq' : p ∈ squarePrimeSet N A := by simpa using hpSq
  let c' := c.rotate p hpc
  exact hnoSquare p hpSq' c' (hc.rotate hpc).isCircuit
    (by simpa [c'] using hodd) (by simpa [c'] using hlen)

def nonsquareNonlargeVertices (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  insert 1 (mediumPrimes N \ squarePrimeSet N A)

lemma nonsquareNonlargeVertices_card_le (N : ℕ) (A : Finset ℕ) :
    (nonsquareNonlargeVertices N A).card ≤ (mediumPrimes N).card + 1 := by
  calc
    (nonsquareNonlargeVertices N A).card ≤
        (insert 1 (mediumPrimes N)).card := by
      apply Finset.card_le_card
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hv).1
    _ = (mediumPrimes N).card + 1 := card_nonlargeVertices N

lemma nonsquareNonlargeVertices_card_add_squarePrimeSet
    {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ interval N) :
    (nonsquareNonlargeVertices N A).card +
        (squarePrimeSet N A).card = (mediumPrimes N).card + 1 := by
  have hs := squarePrimeSet_subset_medium (N := N) (A := A) hAN
  have hscard := Finset.card_le_card hs
  have hone : 1 ∉ mediumPrimes N \ squarePrimeSet N A := by
    intro h
    exact one_not_mem_mediumPrimes N (Finset.mem_sdiff.mp h).1
  rw [nonsquareNonlargeVertices, Finset.card_insert_of_notMem hone,
    Finset.card_sdiff_of_subset hs]
  omega

lemma shortOddCycle_exists_nonsquare_nonlarge_edge
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    {u : ℕ} {c : (residualProductGraph N A D).Walk u u}
    (hc : c.IsCycle) (hodd : Odd c.length) (hlen : c.length ≤ L) :
    ∃ a b : ℕ, s(a, b) ∈ c.edges ∧
      a ∈ nonsquareNonlargeVertices N A ∧
      b ∈ nonsquareNonlargeVertices N A := by
  obtain ⟨a, b, hab, ha, hb⟩ := oddCycle_exists_nonlarge_edge
    hAN hnonzero c hodd
  have hdis := shortOddCycle_support_disjoint_squarePrimeSet
    hnoSquare hc hodd hlen
  have haSupp := c.fst_mem_support_of_mem_edges hab
  have hbSupp := c.snd_mem_support_of_mem_edges hab
  have haSq : a ∉ squarePrimeSet N A := by
    intro haSq
    exact List.disjoint_left.mp hdis haSupp (by simpa using haSq)
  have hbSq : b ∉ squarePrimeSet N A := by
    intro hbSq
    exact List.disjoint_left.mp hdis hbSupp (by simpa using hbSq)
  refine ⟨a, b, hab, ?_, ?_⟩
  · rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨ha, haSq⟩)
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hb, hbSq⟩)

structure ShortOddCycleWitness (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) (L : ℕ) (s : Finset (Sym2 ℕ)) where
  base : ℕ
  walk : (residualProductGraph N A D).Walk base base
  isCycle : walk.IsCycle
  odd : Odd walk.length
  length_le : walk.length ≤ L
  edges_eq : isCycle.isCircuit.isTrail.edgesFinset = s

def shortOddCycleEdgeSets (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) (L : ℕ) : Finset (Finset (Sym2 ℕ)) :=
  (residualProductGraph N A D).edgeFinset.powerset.filter fun s ↦
    Nonempty (ShortOddCycleWitness N A D L s)

lemma mem_shortOddCycleEdgeSets
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    {s : Finset (Sym2 ℕ)} :
    s ∈ shortOddCycleEdgeSets N A D L ↔
      s ⊆ (residualProductGraph N A D).edgeFinset ∧
      Nonempty (ShortOddCycleWitness N A D L s) := by
  simp [shortOddCycleEdgeSets]

noncomputable def shortOddCycleWitness
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (s : shortOddCycleEdgeSets N A D L) :
    ShortOddCycleWitness N A D L s.1 :=
  Classical.choice (mem_shortOddCycleEdgeSets.mp s.2).2

structure NonsquareNonlargeEdgeChoice
    (N : ℕ) (A : Finset ℕ) (s : Finset (Sym2 ℕ)) where
  first : ℕ
  second : ℕ
  edge_mem : s(first, second) ∈ s
  first_mem : first ∈ nonsquareNonlargeVertices N A
  second_mem : second ∈ nonsquareNonlargeVertices N A

lemma nonsquareNonlargeEdgeChoice_nonempty
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (t : shortOddCycleEdgeSets N A D L) :
    Nonempty (NonsquareNonlargeEdgeChoice N A t.1) := by
  let W := shortOddCycleWitness t
  obtain ⟨a, b, hab, ha, hb⟩ := shortOddCycle_exists_nonsquare_nonlarge_edge
    hAN hnonzero hnoSquare W.isCycle W.odd W.length_le
  refine ⟨⟨a, b, ?_, ha, hb⟩⟩
  rw [← W.edges_eq]
  exact hab

noncomputable def chosenShortOddEdge
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (t : shortOddCycleEdgeSets N A D L) :
    NonsquareNonlargeEdgeChoice N A t.1 :=
  Classical.choice (nonsquareNonlargeEdgeChoice_nonempty
    hAN hnonzero hnoSquare t)

noncomputable def chosenShortOddVertex
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (t : shortOddCycleEdgeSets N A D L) :
    nonsquareNonlargeVertices N A :=
  ⟨(chosenShortOddEdge hAN hnonzero hnoSquare t).first,
    (chosenShortOddEdge hAN hnonzero hnoSquare t).first_mem⟩

lemma chosenShortOddVertex_injective_of_support_disjoint
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (hdis : ∀ s t : shortOddCycleEdgeSets N A D L, s ≠ t →
      (shortOddCycleWitness s).walk.support.Disjoint
        (shortOddCycleWitness t).walk.support) :
    Function.Injective (chosenShortOddVertex hAN hnonzero hnoSquare) := by
  intro s t hst
  by_contra hne
  let es := chosenShortOddEdge hAN hnonzero hnoSquare s
  let et := chosenShortOddEdge hAN hnonzero hnoSquare t
  have hsMem : es.first ∈ (shortOddCycleWitness s).walk.support := by
    apply (shortOddCycleWitness s).walk.fst_mem_support_of_mem_edges
    have he : s(es.first, es.second) ∈
        (shortOddCycleWitness s).isCycle.isCircuit.isTrail.edgesFinset := by
      rw [(shortOddCycleWitness s).edges_eq]
      exact es.edge_mem
    exact he
  have htMem : et.first ∈ (shortOddCycleWitness t).walk.support := by
    apply (shortOddCycleWitness t).walk.fst_mem_support_of_mem_edges
    have he : s(et.first, et.second) ∈
        (shortOddCycleWitness t).isCycle.isCircuit.isTrail.edgesFinset := by
      rw [(shortOddCycleWitness t).edges_eq]
      exact et.edge_mem
    exact he
  have hval : es.first = et.first := congrArg Subtype.val hst
  exact List.disjoint_left.mp (hdis s t hne) hsMem (hval ▸ htMem)

def chosenShortOddEdgeFinset
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False) :
    Finset (Sym2 ℕ) :=
  Finset.univ.image fun t : shortOddCycleEdgeSets N A D L ↦
    s((chosenShortOddEdge hAN hnonzero hnoSquare t).first,
      (chosenShortOddEdge hAN hnonzero hnoSquare t).second)

lemma chosenShortOddEdgeFinset_card_le
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (hdis : ∀ s t : shortOddCycleEdgeSets N A D L, s ≠ t →
      (shortOddCycleWitness s).walk.support.Disjoint
        (shortOddCycleWitness t).walk.support) :
    (chosenShortOddEdgeFinset hAN hnonzero hnoSquare).card ≤
      (mediumPrimes N).card + 1 := by
  calc
    (chosenShortOddEdgeFinset hAN hnonzero hnoSquare).card ≤
        Fintype.card (shortOddCycleEdgeSets N A D L) := by
      apply Finset.card_image_le
    _ ≤ Fintype.card (nonsquareNonlargeVertices N A) :=
      Fintype.card_le_of_injective _
        (chosenShortOddVertex_injective_of_support_disjoint
          hAN hnonzero hnoSquare hdis)
    _ = (nonsquareNonlargeVertices N A).card := Fintype.card_coe _
    _ ≤ (mediumPrimes N).card + 1 :=
      nonsquareNonlargeVertices_card_le N A

lemma chosenShortOddEdgeFinset_card_le_nonsquare
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (hdis : ∀ s t : shortOddCycleEdgeSets N A D L, s ≠ t →
      (shortOddCycleWitness s).walk.support.Disjoint
        (shortOddCycleWitness t).walk.support) :
    (chosenShortOddEdgeFinset hAN hnonzero hnoSquare).card ≤
      (nonsquareNonlargeVertices N A).card := by
  calc
    (chosenShortOddEdgeFinset hAN hnonzero hnoSquare).card ≤
        Fintype.card (shortOddCycleEdgeSets N A D L) := by
      apply Finset.card_image_le
    _ ≤ Fintype.card (nonsquareNonlargeVertices N A) :=
      Fintype.card_le_of_injective _
        (chosenShortOddVertex_injective_of_support_disjoint
          hAN hnonzero hnoSquare hdis)
    _ = (nonsquareNonlargeVertices N A).card := Fintype.card_coe _

lemma isCycle_transfer {G H : SimpleGraph ℕ} {u : ℕ}
    {w : H.Walk u u} (hw : w.IsCycle)
    (hedge : ∀ e ∈ w.edges, e ∈ G.edgeSet) :
    (w.transfer G hedge).IsCycle := by
  have hc := isCircuit_transfer hw.isCircuit hedge
  refine ⟨hc, ?_⟩
  simpa [SimpleGraph.Walk.support_transfer] using hw.support_nodup

/-- Delete one medium/special edge from each remaining short odd cycle.
The disjoint-support hypothesis is supplied below by the theta argument for
two intersecting odd cycles. -/
theorem exists_deleteEdges_no_short_cycle_of_support_disjoint
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoeven : ∀ u : ℕ, ∀ w : (residualProductGraph N A D).Walk u u,
      w.IsCircuit → Even w.length → w.length ≤ L → False)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False)
    (hdis : ∀ s t : shortOddCycleEdgeSets N A D L, s ≠ t →
      (shortOddCycleWitness s).walk.support.Disjoint
        (shortOddCycleWitness t).walk.support) :
    ∃ F : Finset (Sym2 ℕ),
      F ⊆ (residualProductGraph N A D).edgeFinset ∧
      F.card ≤ (nonsquareNonlargeVertices N A).card ∧
      ∀ u : ℕ,
        ∀ c : ((residualProductGraph N A D).deleteEdges F).Walk u u,
          c.IsCycle → c.length ≤ L → False := by
  let F := chosenShortOddEdgeFinset hAN hnonzero hnoSquare
  refine ⟨F, ?_, chosenShortOddEdgeFinset_card_le_nonsquare
    hAN hnonzero hnoSquare hdis, ?_⟩
  · intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    exact (mem_shortOddCycleEdgeSets.mp t.2).1
      (chosenShortOddEdge hAN hnonzero hnoSquare t).edge_mem
  · intro u c hc hlen
    let G := residualProductGraph N A D
    have hedgeG : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      have he' := c.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at he'
      exact he'.1
    let cG : G.Walk u u := c.transfer G hedgeG
    have hcG : cG.IsCycle := isCycle_transfer hc hedgeG
    have hlenG : cG.length ≤ L := by simpa [cG] using hlen
    have hoddG : Odd cG.length := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      exact hnoeven u cG hcG.isCircuit heven hlenG
    let s : Finset (Sym2 ℕ) := hcG.isCircuit.isTrail.edgesFinset
    have hsC : s ∈ shortOddCycleEdgeSets N A D L := by
      apply mem_shortOddCycleEdgeSets.mpr
      constructor
      · intro e he
        have heG : e ∈ G.edgeSet := cG.edges_subset_edgeSet he
        simpa [G] using heG
      · exact ⟨{
          base := u
          walk := cG
          isCycle := hcG
          odd := hoddG
          length_le := hlenG
          edges_eq := rfl }⟩
    let t : shortOddCycleEdgeSets N A D L := ⟨s, hsC⟩
    let e := s((chosenShortOddEdge hAN hnonzero hnoSquare t).first,
      (chosenShortOddEdge hAN hnonzero hnoSquare t).second)
    have heS : e ∈ s := (chosenShortOddEdge hAN hnonzero hnoSquare t).edge_mem
    have heCG : e ∈ cG.edges := heS
    have heC : e ∈ c.edges := by
      simpa [cG, SimpleGraph.Walk.edges_transfer] using heCG
    have heF : e ∈ F := by
      change e ∈ Finset.univ.image (fun t : shortOddCycleEdgeSets N A D L ↦
        s((chosenShortOddEdge hAN hnonzero hnoSquare t).first,
          (chosenShortOddEdge hAN hnonzero hnoSquare t).second))
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    have heDel := c.edges_subset_edgeSet heC
    rw [SimpleGraph.edgeSet_deleteEdges] at heDel
    exact heDel.2 heF

/-! A first-exit construction for a simple cycle.  It is the finite-list
device used in the theta argument: starting inside a set and walking toward
a known outside vertex, the prefix up to the first exit is a simple path
whose earlier vertices all remain inside. -/

structure CycleFirstExit {G : SimpleGraph ℕ} {z : ℕ}
    (r : G.Walk z z) (S : Set ℕ) where
  index : ℕ
  endpoint : ℕ
  walk : G.Walk z endpoint
  index_pos : 0 < index
  index_lt_length : index < r.length
  endpoint_eq_getVert : endpoint = r.getVert index
  walk_eq_take : walk = (r.take index).copy rfl endpoint_eq_getVert.symm
  isPath : walk.IsPath
  endpoint_not_mem : endpoint ∉ S
  start_mem : z ∈ S
  internal_mem : ∀ v ∈ walk.support, v ≠ endpoint → v ∈ S
  length_le : walk.length ≤ r.length

noncomputable def cycleFirstExit
    {G : SimpleGraph ℕ} {z : ℕ} {r : G.Walk z z}
    (hr : r.IsCycle) (S : Set ℕ) (hz : z ∈ S)
    (hout : ∃ x ∈ r.support, x ∉ S) : CycleFirstExit r S := by
  let p : ℕ → Bool := fun x ↦ decide (x ∉ S)
  let j := r.support.findIdx p
  have hex : ∃ x ∈ r.support, p x := by
    obtain ⟨x, hx, hxn⟩ := hout
    exact ⟨x, hx, by simp [p, hxn]⟩
  have hjSupp : j < r.support.length :=
    List.findIdx_lt_length_of_exists hex
  have hjle : j ≤ r.length := by
    rw [SimpleGraph.Walk.length_support] at hjSupp
    omega
  let y := r.getVert j
  have hyNot : y ∉ S := by
    have hpY : p r.support[j] := List.findIdx_getElem (xs := r.support)
      (p := p) (w := hjSupp)
    have hget : r.support[j] = y := by
      symm
      exact r.getVert_eq_support_getElem hjle
    simpa [p, y, hget] using hpY
  have hjlt : j < r.length := by
    have hjne : j ≠ r.length := by
      intro hj
      apply hyNot
      simpa [y, hj] using hz
    omega
  have hjpos : 0 < j := by
    by_contra hj
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
    apply hyNot
    simpa [y, hj0] using hz
  let w := r.take j
  have hwPath : w.IsPath := hr.isPath_take hjlt
  refine {
    index := j
    endpoint := y
    walk := w
    index_pos := hjpos
    index_lt_length := hjlt
    endpoint_eq_getVert := rfl
    walk_eq_take := by rfl
    isPath := hwPath
    endpoint_not_mem := hyNot
    start_mem := hz
    internal_mem := ?_
    length_le := ?_ }
  · intro v hv hvy
    have hv' : v ∈ r.support.take (j + 1) := by
      simpa [w, SimpleGraph.Walk.support_take] using hv
    rw [List.take_succ_eq_append_getElem hjSupp] at hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · have hpFalse := List.false_of_mem_take_findIdx (p := p) hv'
      simpa [p] using hpFalse
    · have : v = y := by simpa [y, r.getVert_eq_support_getElem hjle] using hv'
      exact (hvy this).elim
  · simp [w]

lemma cycleFirstExit_support_union_of_eq
    {G : SimpleGraph ℕ} {z : ℕ} {r : G.Walk z z}
    (hr : r.IsCycle) {S : Set ℕ}
    (f : CycleFirstExit r S) (b : CycleFirstExit r.reverse S)
    (hfb : f.endpoint = b.endpoint) :
    ∀ x ∈ r.support, x ∈ f.walk.support ∨ x ∈ b.walk.support := by
  have hidx : f.index = r.length - b.index := by
    apply hr.getVert_injOn
    · simp only [Set.mem_ofPred_eq]
      exact ⟨f.index_pos, f.index_lt_length.le⟩
    · simp only [Set.mem_ofPred_eq]
      have hbpos := b.index_pos
      have hblt := b.index_lt_length
      simp only [SimpleGraph.Walk.length_reverse] at hblt
      omega
    · rw [← f.endpoint_eq_getVert, hfb, b.endpoint_eq_getVert,
        SimpleGraph.Walk.getVert_reverse]
  intro x hx
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
  obtain ⟨i, hix, hi⟩ := hx
  subst x
  by_cases hif : i ≤ f.index
  · left
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    refine ⟨i, ?_, ?_⟩
    · simp [f.walk_eq_take, SimpleGraph.Walk.take_getVert, hif]
    · simp [f.walk_eq_take]
      exact ⟨hif, hi⟩
  · right
    let j := r.length - i
    have hjb : j ≤ b.index := by
      dsimp [j]
      omega
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    refine ⟨j, ?_, ?_⟩
    · simp [b.walk_eq_take, SimpleGraph.Walk.take_getVert, hjb, j,
        SimpleGraph.Walk.getVert_reverse]
      have hsub : r.length - (r.length - i) = i := by omega
      rw [hsub]
    · simp [b.walk_eq_take]
      constructor
      · exact hjb
      · have hb := hjb.trans b.index_lt_length.le
        simpa using hb

structure ExternalCyclePath {G : SimpleGraph ℕ} {u v : ℕ}
    (c : G.Walk u u) (d : G.Walk v v) where
  start : ℕ
  stop : ℕ
  ne : start ≠ stop
  walk : G.Walk start stop
  isPath : walk.IsPath
  start_mem_cycle : start ∈ c.support
  stop_mem_cycle : stop ∈ c.support
  internal_not_mem_cycle :
    ∀ x ∈ walk.support, x ≠ start → x ≠ stop → x ∉ c.support
  edges_disjoint_cycle : walk.edges.Disjoint c.edges
  length_le : walk.length ≤ 2 * d.length

/-- Two different first exits from an outside vertex, in the two cyclic
directions, give a simple external path after bypassing repetitions. -/
noncomputable def externalCyclePathOfDistinctExits
    {G : SimpleGraph ℕ} {u v z : ℕ}
    {c : G.Walk u u} {d : G.Walk v v}
    (hd : d.IsCycle) (hz : z ∈ d.support) (hzc : z ∉ c.support)
    (hmeet : ∃ x ∈ d.support, x ∈ c.support)
    (hne : (cycleFirstExit (hd.rotate hz)
        {x | x ∉ c.support} hzc (by
          obtain ⟨x, hxd, hxc⟩ := hmeet
          refine ⟨x, ?_, by simpa using hxc⟩
          have : x ∈ d.toSubgraph.verts := by
            simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
          have : x ∈ (d.rotate z hz).toSubgraph.verts := by
            simpa [SimpleGraph.Walk.toSubgraph_rotate] using this
          simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this)).endpoint ≠
      (cycleFirstExit ((hd.rotate hz).reverse)
        {x | x ∉ c.support} hzc (by
          obtain ⟨x, hxd, hxc⟩ := hmeet
          refine ⟨x, ?_, by simpa using hxc⟩
          have : x ∈ d.toSubgraph.verts := by
            simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
          have : x ∈ ((d.rotate z hz).reverse).toSubgraph.verts := by
            simpa [SimpleGraph.Walk.toSubgraph_reverse,
              SimpleGraph.Walk.toSubgraph_rotate] using this
          simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this)).endpoint) :
    ExternalCyclePath c d := by
  let r := d.rotate z hz
  have hr : r.IsCycle := hd.rotate hz
  have houtR : ∃ x ∈ r.support, x ∈ c.support := by
    obtain ⟨x, hxd, hxc⟩ := hmeet
    refine ⟨x, ?_, hxc⟩
    have : x ∈ d.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
    have : x ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using this
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this
  have houtRev : ∃ x ∈ r.reverse.support, x ∈ c.support := by
    obtain ⟨x, hxr, hxc⟩ := houtR
    refine ⟨x, ?_, hxc⟩
    simpa [SimpleGraph.Walk.support_reverse] using hxr
  let f := cycleFirstExit hr {x | x ∉ c.support} hzc (by
    obtain ⟨x, hx, hxc⟩ := houtR
    exact ⟨x, hx, by simpa using hxc⟩)
  let b := cycleFirstExit hr.reverse {x | x ∉ c.support} hzc (by
    obtain ⟨x, hx, hxc⟩ := houtRev
    exact ⟨x, hx, by simpa using hxc⟩)
  have hfb : f.endpoint ≠ b.endpoint := by simpa [f, b, r] using hne
  let w0 := b.walk.reverse.append f.walk
  let w := w0.toPath
  refine {
    start := b.endpoint
    stop := f.endpoint
    ne := hfb.symm
    walk := w
    isPath := w.property
    start_mem_cycle := by simpa using b.endpoint_not_mem
    stop_mem_cycle := by simpa using f.endpoint_not_mem
    internal_not_mem_cycle := ?_
    edges_disjoint_cycle := ?_
    length_le := ?_ }
  · intro x hx hxb hxf
    have hx0 : x ∈ w0.support := w0.support_toPath_subset_support hx
    rw [SimpleGraph.Walk.support_append] at hx0
    rcases List.mem_append.mp hx0 with hx0 | hx0
    · have hxB : x ∈ b.walk.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hx0
      exact b.internal_mem x hxB hxb
    · have hxF : x ∈ f.walk.support := List.mem_of_mem_tail hx0
      exact f.internal_mem x hxF hxf
  · rw [List.disjoint_left]
    intro e heW heC
    have he0 : e ∈ w0.edges := w0.edges_toPath_subset_edges heW
    rw [SimpleGraph.Walk.edges_append] at he0
    rcases List.mem_append.mp he0 with heB | heF
    · have heB' : e ∈ b.walk.edges := by
        simpa [SimpleGraph.Walk.edges_reverse] using heB
      induction e using Sym2.inductionOn with
      | _ a a' =>
          have haB := b.walk.fst_mem_support_of_mem_edges heB'
          have haB' := b.walk.snd_mem_support_of_mem_edges heB'
          have haC := c.fst_mem_support_of_mem_edges heC
          have haC' := c.snd_mem_support_of_mem_edges heC
          have ha : a = b.endpoint := by
            by_contra hne
            exact (b.internal_mem a haB hne) haC
          have ha' : a' = b.endpoint := by
            by_contra hne
            exact (b.internal_mem a' haB' hne) haC'
          exact (b.walk.adj_of_mem_edges heB').ne (ha.trans ha'.symm)
    · induction e using Sym2.inductionOn with
      | _ a a' =>
          have haF := f.walk.fst_mem_support_of_mem_edges heF
          have haF' := f.walk.snd_mem_support_of_mem_edges heF
          have haC := c.fst_mem_support_of_mem_edges heC
          have haC' := c.snd_mem_support_of_mem_edges heC
          have ha : a = f.endpoint := by
            by_contra hne
            exact (f.internal_mem a haF hne) haC
          have ha' : a' = f.endpoint := by
            by_contra hne
            exact (f.internal_mem a' haF' hne) haC'
          exact (f.walk.adj_of_mem_edges heF).ne (ha.trans ha'.symm)
  · calc
      (w : G.Walk b.endpoint f.endpoint).length ≤ w0.length :=
        w0.length_bypass_le_length
      _ = b.walk.length + f.walk.length := by simp [w0]
      _ ≤ r.reverse.length + r.length := Nat.add_le_add b.length_le f.length_le
      _ = 2 * d.length := by simp [r, Nat.two_mul]

/-- An external path joining two distinct vertices of an odd cycle, and
sharing no edge with that cycle, forms an even circuit with one of the two
arcs of the cycle.  This is the parity step in the theta argument. -/
lemma evenCircuit_of_externalCyclePath
    {G : SimpleGraph ℕ} {u v : ℕ}
    {c : G.Walk u u} {d : G.Walk v v}
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ExternalCyclePath c d) :
    ∃ w : G.Walk P.start P.start,
      w.IsCircuit ∧ Even w.length ∧
        w.length ≤ c.length + P.walk.length := by
  let r := c.rotate P.start P.start_mem_cycle
  have hr : r.IsCycle := hc.rotate P.start_mem_cycle
  have hstop : P.stop ∈ r.support := by
    have hv : P.stop ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using P.stop_mem_cycle
    have hv' : P.stop ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hv
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hv'
  let q₁ : G.Walk P.start P.stop := r.takeUntil P.stop hstop
  let q₂ : G.Walk P.start P.stop := (r.dropUntil P.stop hstop).reverse
  have hq₁Path : q₁.IsPath := hr.isPath_takeUntil hstop
  have hq₂Path : q₂.IsPath := by
    have hsplit : (q₁.append (r.dropUntil P.stop hstop)).IsCycle := by
      simpa [q₁] using hr
    have htake : ¬ q₁.Nil := SimpleGraph.Walk.not_nil_of_ne P.ne
    exact (r.dropUntil P.stop hstop).isPath_reverse_iff.mpr
      (hsplit.isPath_of_append_right htake)
  have hq₁Edges : q₁.edges ⊆ c.edges := by
    intro e he
    have her : e ∈ r.edges := r.edges_takeUntil_subset_edges hstop he
    exact (c.rotate_edges P.start P.start_mem_cycle).perm.subset her
  have hq₂Edges : q₂.edges ⊆ c.edges := by
    intro e he
    have he' : e ∈ (r.dropUntil P.stop hstop).edges := by
      simpa [q₂, SimpleGraph.Walk.edges_reverse] using he
    have her : e ∈ r.edges := r.edges_dropUntil_subset_edges hstop he'
    exact (c.rotate_edges P.start P.start_mem_cycle).perm.subset her
  have hsum : q₁.length + q₂.length = c.length := by
    have h := congrArg SimpleGraph.Walk.length (r.take_spec hstop)
    simp only [SimpleGraph.Walk.length_append] at h
    simpa [q₁, q₂, r] using h
  have circuit_of_arc
      (q : G.Walk P.start P.stop) (hqPath : q.IsPath)
      (hqEdges : q.edges ⊆ c.edges) :
      (P.walk.append q.reverse).IsCircuit := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_append]
      refine ⟨P.isPath.isTrail, hqPath.reverse.isTrail, ?_⟩
      rw [List.disjoint_left]
      intro e heP heq
      apply List.disjoint_left.mp P.edges_disjoint_cycle heP
      apply hqEdges
      simpa [SimpleGraph.Walk.edges_reverse] using heq
    · intro hnil
      have hnil' : (P.walk.append q.reverse).Nil := by
        rw [hnil]
        exact SimpleGraph.Walk.nil_nil
      exact P.ne (SimpleGraph.Walk.nil_append_iff.mp hnil').1.eq
  have hparity : Even (P.walk.length + q₁.length) ∨
      Even (P.walk.length + q₂.length) := by
    rw [Nat.even_iff, Nat.even_iff]
    rw [Nat.odd_iff] at hcodd
    omega
  rcases hparity with heven | heven
  · let w := P.walk.append q₁.reverse
    refine ⟨w, circuit_of_arc q₁ hq₁Path hq₁Edges, ?_, ?_⟩
    · simpa [w, Nat.add_comm] using heven
    · simp only [w, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_reverse]
      omega
  · let w := P.walk.append q₂.reverse
    refine ⟨w, circuit_of_arc q₂ hq₂Path hq₂Edges, ?_, ?_⟩
    · simpa [w, Nat.add_comm] using heven
    · simp only [w, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_reverse]
      omega

/-- A chord of an odd cycle cuts it into two arcs; adjoining the chord to
the arc of matching parity gives an even circuit. -/
lemma evenCircuit_of_chord_oddCycle
    {G : SimpleGraph ℕ} {u a b : ℕ} {c : G.Walk u u}
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hab : G.Adj a b) (hchord : s(a, b) ∉ c.edges) :
    ∃ w : G.Walk a a,
      w.IsCircuit ∧ Even w.length ∧ w.length ≤ c.length + 1 := by
  let r := c.rotate a ha
  have hr : r.IsCycle := hc.rotate ha
  have hb' : b ∈ r.support := by
    have hv : b ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hb
    have hv' : b ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hv
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hv'
  let q₁ : G.Walk a b := r.takeUntil b hb'
  let q₂ : G.Walk a b := (r.dropUntil b hb').reverse
  have hne : a ≠ b := hab.ne
  have hq₁Path : q₁.IsPath := hr.isPath_takeUntil hb'
  have hq₂Path : q₂.IsPath := by
    have hsplit : (q₁.append (r.dropUntil b hb')).IsCycle := by
      simpa [q₁] using hr
    have htake : ¬ q₁.Nil := SimpleGraph.Walk.not_nil_of_ne hne
    exact (r.dropUntil b hb').isPath_reverse_iff.mpr
      (hsplit.isPath_of_append_right htake)
  have hq₁NoChord : s(a, b) ∉ q₁.reverse.edges := by
    intro he
    apply hchord
    have he' : s(a, b) ∈ q₁.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using he
    have her : s(a, b) ∈ r.edges :=
      r.edges_takeUntil_subset_edges hb' he'
    exact (c.rotate_edges a ha).perm.subset her
  have hq₂NoChord : s(a, b) ∉ q₂.reverse.edges := by
    intro he
    apply hchord
    have he' : s(a, b) ∈ q₂.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using he
    have he'' : s(a, b) ∈ (r.dropUntil b hb').edges := by
      simpa [q₂, SimpleGraph.Walk.edges_reverse] using he'
    have her : s(a, b) ∈ r.edges :=
      r.edges_dropUntil_subset_edges hb' he''
    exact (c.rotate_edges a ha).perm.subset her
  let w₁ : G.Walk a a := SimpleGraph.Walk.cons hab q₁.reverse
  let w₂ : G.Walk a a := SimpleGraph.Walk.cons hab q₂.reverse
  have hw₁ : w₁.IsCycle := by
    exact (SimpleGraph.Walk.cons_isCycle_iff q₁.reverse hab).mpr
      ⟨hq₁Path.reverse, hq₁NoChord⟩
  have hw₂ : w₂.IsCycle := by
    exact (SimpleGraph.Walk.cons_isCycle_iff q₂.reverse hab).mpr
      ⟨hq₂Path.reverse, hq₂NoChord⟩
  have hsum : q₁.length + q₂.length = c.length := by
    have h := congrArg SimpleGraph.Walk.length (r.take_spec hb')
    simp only [SimpleGraph.Walk.length_append] at h
    simpa [q₁, q₂, r] using h
  have hparity : Even (q₁.length + 1) ∨ Even (q₂.length + 1) := by
    rw [Nat.even_iff, Nat.even_iff]
    rw [Nat.odd_iff] at hcodd
    omega
  rcases hparity with heven | heven
  · refine ⟨w₁, hw₁.isCircuit, ?_, ?_⟩
    · simpa [w₁, Nat.add_comm] using heven
    · simp only [w₁, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_reverse]
      omega
  · refine ⟨w₂, hw₂.isCircuit, ?_, ?_⟩
    · simpa [w₂, Nat.add_comm] using heven
    · simp only [w₂, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_reverse]
      omega

lemma cycle_edges_disjoint_of_equal_exits
    {G : SimpleGraph ℕ} {u v z : ℕ}
    {c : G.Walk u u} {d : G.Walk v v}
    (hd : d.IsCycle) (hz : z ∈ d.support) (hzc : z ∉ c.support)
    (hmeet : ∃ x ∈ d.support, x ∈ c.support)
    (heq : (cycleFirstExit (hd.rotate hz)
        {x | x ∉ c.support} hzc (by
          obtain ⟨x, hxd, hxc⟩ := hmeet
          refine ⟨x, ?_, by simpa using hxc⟩
          have : x ∈ d.toSubgraph.verts := by
            simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
          have : x ∈ (d.rotate z hz).toSubgraph.verts := by
            simpa [SimpleGraph.Walk.toSubgraph_rotate] using this
          simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this)).endpoint =
      (cycleFirstExit ((hd.rotate hz).reverse)
        {x | x ∉ c.support} hzc (by
          obtain ⟨x, hxd, hxc⟩ := hmeet
          refine ⟨x, ?_, by simpa using hxc⟩
          have : x ∈ d.toSubgraph.verts := by
            simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
          have : x ∈ ((d.rotate z hz).reverse).toSubgraph.verts := by
            simpa [SimpleGraph.Walk.toSubgraph_reverse,
              SimpleGraph.Walk.toSubgraph_rotate] using this
          simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this)).endpoint) :
    c.edges.Disjoint d.edges := by
  let r := d.rotate z hz
  have hr : r.IsCycle := hd.rotate hz
  have houtR : ∃ x ∈ r.support, x ∈ c.support := by
    obtain ⟨x, hxd, hxc⟩ := hmeet
    refine ⟨x, ?_, hxc⟩
    have : x ∈ d.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
    have : x ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using this
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this
  have houtRev : ∃ x ∈ r.reverse.support, x ∈ c.support := by
    obtain ⟨x, hxr, hxc⟩ := houtR
    exact ⟨x, by simpa [SimpleGraph.Walk.support_reverse] using hxr, hxc⟩
  let f := cycleFirstExit hr {x | x ∉ c.support} hzc (by
    obtain ⟨x, hx, hxc⟩ := houtR
    exact ⟨x, hx, by simpa using hxc⟩)
  let b := cycleFirstExit hr.reverse {x | x ∉ c.support} hzc (by
    obtain ⟨x, hx, hxc⟩ := houtRev
    exact ⟨x, hx, by simpa using hxc⟩)
  have hfb : f.endpoint = b.endpoint := by simpa [f, b, r] using heq
  have hcommon : ∀ x, x ∈ d.support → x ∈ c.support →
      x = f.endpoint := by
    intro x hxd hxc
    have hxr : x ∈ r.support := by
      have : x ∈ d.toSubgraph.verts := by
        simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hxd
      have : x ∈ r.toSubgraph.verts := by
        simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using this
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this
    rcases cycleFirstExit_support_union_of_eq hr f b hfb x hxr with hx | hx
    · by_contra hne
      exact (f.internal_mem x hx hne) hxc
    · by_contra hne
      have hne' : x ≠ b.endpoint := fun h ↦ hne (h.trans hfb.symm)
      exact (b.internal_mem x hx hne') hxc
  rw [List.disjoint_left]
  intro e hec hed
  induction e using Sym2.inductionOn with
  | _ a b' =>
      have haC := c.fst_mem_support_of_mem_edges hec
      have hbC := c.snd_mem_support_of_mem_edges hec
      have haD := d.fst_mem_support_of_mem_edges hed
      have hbD := d.snd_mem_support_of_mem_edges hed
      have ha := hcommon a haD haC
      have hb := hcommon b' hbD hbC
      exact (c.adj_of_mem_edges hec).ne (ha.trans hb.symm)

/-- If one odd cycle has an edge absent from another, then the two cycles
are vertex-disjoint provided even circuits up to three times their common
length bound have already been excluded. -/
theorem oddCycles_support_disjoint_of_edge_difference
    {G : SimpleGraph ℕ} {L : ℕ}
    (hnoeven : ∀ z : ℕ, ∀ w : G.Walk z z,
      w.IsCircuit → Even w.length → w.length ≤ 3 * L → False)
    {u v : ℕ} {c : G.Walk u u} {d : G.Walk v v}
    (hc : c.IsCycle) (hd : d.IsCycle)
    (hcodd : Odd c.length) (hdodd : Odd d.length)
    (hclen : c.length ≤ L) (hdlen : d.length ≤ L)
    (hedge : ∃ a b : ℕ, s(a, b) ∈ d.edges ∧ s(a, b) ∉ c.edges) :
    c.support.Disjoint d.support := by
  rw [List.disjoint_left]
  intro x hxc hxd
  obtain ⟨a, b, habD, habC⟩ := hedge
  have haD : a ∈ d.support := d.fst_mem_support_of_mem_edges habD
  have hbD : b ∈ d.support := d.snd_mem_support_of_mem_edges habD
  have hadj : G.Adj a b := d.adj_of_mem_edges habD
  have hmeet : ∃ y ∈ d.support, y ∈ c.support := ⟨x, hxd, hxc⟩
  have outside_contradiction (z : ℕ) (hzD : z ∈ d.support)
      (hzC : z ∉ c.support) : False := by
    let r := d.rotate z hzD
    have hr : r.IsCycle := hd.rotate hzD
    have houtR : ∃ y ∈ r.support, y ∈ c.support := by
      obtain ⟨y, hyD, hyC⟩ := hmeet
      refine ⟨y, ?_, hyC⟩
      have hy : y ∈ d.toSubgraph.verts := by
        simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hyD
      have hy' : y ∈ r.toSubgraph.verts := by
        simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hy
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hy'
    have houtRev : ∃ y ∈ r.reverse.support, y ∈ c.support := by
      obtain ⟨y, hy, hyC⟩ := houtR
      exact ⟨y, by simpa [SimpleGraph.Walk.support_reverse] using hy, hyC⟩
    let f := cycleFirstExit hr {y | y ∉ c.support} hzC (by
      obtain ⟨y, hy, hyC⟩ := houtR
      exact ⟨y, hy, by simpa using hyC⟩)
    let bwd := cycleFirstExit hr.reverse {y | y ∉ c.support} hzC (by
      obtain ⟨y, hy, hyC⟩ := houtRev
      exact ⟨y, hy, by simpa using hyC⟩)
    by_cases hfb : f.endpoint = bwd.endpoint
    · have hedges : c.edges.Disjoint d.edges := by
        apply cycle_edges_disjoint_of_equal_exits hd hzD hzC hmeet
        simpa [f, bwd, r] using hfb
      have hdis := oddCycles_support_disjoint_of_no_short_even
        (G := G) (L := L) (fun z w hw heven hlen ↦
          hnoeven z w hw heven (by omega))
        hc hd hcodd hdodd hclen hdlen hedges
      exact List.disjoint_left.mp hdis hxc hxd
    · let P := externalCyclePathOfDistinctExits hd hzD hzC hmeet (by
        simpa [f, bwd, r] using hfb)
      obtain ⟨w, hw, heven, hwlen⟩ :=
        evenCircuit_of_externalCyclePath hc hcodd P
      apply hnoeven P.start w hw heven
      calc
        w.length ≤ c.length + P.walk.length := hwlen
        _ ≤ 3 * L := by
          have hP := P.length_le
          omega
  by_cases haC : a ∈ c.support
  · by_cases hbC : b ∈ c.support
    · obtain ⟨w, hw, heven, hwlen⟩ :=
        evenCircuit_of_chord_oddCycle hc hcodd haC hbC hadj habC
      have hcThree := hc.three_le_length
      exact hnoeven a w hw heven (by omega)
    · exact outside_contradiction b hbD hbC
  · exact outside_contradiction a haD haC

/-- Distinct edge sets of short odd cycles have disjoint supports once
short even circuits are absent.  The asymmetric edge-difference lemma is
applied in whichever direction contains a missing edge. -/
theorem oddCycles_support_disjoint_of_distinct_edges
    {G : SimpleGraph ℕ} {L : ℕ}
    (hnoeven : ∀ z : ℕ, ∀ w : G.Walk z z,
      w.IsCircuit → Even w.length → w.length ≤ 3 * L → False)
    {u v : ℕ} {c : G.Walk u u} {d : G.Walk v v}
    (hc : c.IsCycle) (hd : d.IsCycle)
    (hcodd : Odd c.length) (hdodd : Odd d.length)
    (hclen : c.length ≤ L) (hdlen : d.length ≤ L)
    (hne : hc.isCircuit.isTrail.edgesFinset ≠
      hd.isCircuit.isTrail.edgesFinset) :
    c.support.Disjoint d.support := by
  let C := hc.isCircuit.isTrail.edgesFinset
  let D := hd.isCircuit.isTrail.edgesFinset
  by_cases hDC : D ⊆ C
  · have hCD : ¬ C ⊆ D := by
      intro hCD
      exact hne (Finset.Subset.antisymm hCD hDC)
    obtain ⟨e, heC, heD⟩ := Finset.not_subset.mp hCD
    induction e using Sym2.inductionOn with
    | _ a b =>
        have h := oddCycles_support_disjoint_of_edge_difference
          hnoeven hd hc hdodd hcodd hdlen hclen (by
            refine ⟨a, b, ?_, ?_⟩
            · change s(a, b) ∈ c.edges at heC
              exact heC
            · change s(a, b) ∉ d.edges at heD
              exact heD)
        exact h.symm
  · obtain ⟨e, heD, heC⟩ := Finset.not_subset.mp hDC
    induction e using Sym2.inductionOn with
    | _ a b =>
        exact oddCycles_support_disjoint_of_edge_difference
          hnoeven hc hd hcodd hdodd hclen hdlen (by
            refine ⟨a, b, ?_, ?_⟩
            · change s(a, b) ∈ d.edges at heD
              exact heD
            · change s(a, b) ∉ c.edges at heC
              exact heC)

lemma shortOddCycleWitness_support_disjoint
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hnoeven : ∀ z : ℕ, ∀ w : (residualProductGraph N A D).Walk z z,
      w.IsCircuit → Even w.length → w.length ≤ 3 * L → False) :
    ∀ s t : shortOddCycleEdgeSets N A D L, s ≠ t →
      (shortOddCycleWitness s).walk.support.Disjoint
        (shortOddCycleWitness t).walk.support := by
  intro s t hst
  let Ws := shortOddCycleWitness s
  let Wt := shortOddCycleWitness t
  apply oddCycles_support_disjoint_of_distinct_edges hnoeven
    Ws.isCycle Wt.isCycle Ws.odd Wt.odd Ws.length_le Wt.length_le
  intro heq
  apply hst
  apply Subtype.ext
  change s.1 = t.1
  rw [← Ws.edges_eq, ← Wt.edges_eq]
  exact heq

/-- The unconditional final short-cycle deletion.  The theta lemma above
supplies the support-disjointness needed by the cheap one-edge-per-cycle
deletion. -/
theorem exists_deleteEdges_no_short_cycle
    {N L : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hinj : Set.InjOn (highFactorization N) A)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoeven : ∀ z : ℕ, ∀ w : (residualProductGraph N A D).Walk z z,
      w.IsCircuit → Even w.length → w.length ≤ 3 * L → False)
    (hnoSquare : ∀ p ∈ squarePrimeSet N A,
      ∀ w : (residualProductGraph N A D).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False) :
    ∃ F : Finset (Sym2 ℕ),
      F ⊆ (residualProductGraph N A D).edgeFinset ∧
      F.card + (squareElements N A).card ≤
        (mediumPrimes N).card + 1 ∧
      ∀ z : ℕ,
        ∀ c : ((residualProductGraph N A D).deleteEdges F).Walk z z,
          c.IsCycle → c.length ≤ L → False := by
  let hdis := shortOddCycleWitness_support_disjoint hnoeven
  obtain ⟨F, hFsub, hFcard, hFno⟩ :=
    exists_deleteEdges_no_short_cycle_of_support_disjoint
      hAN hnonzero (fun z w hw heven hlen ↦
        hnoeven z w hw heven (by omega)) hnoSquare hdis
  refine ⟨F, hFsub, ?_, hFno⟩
  calc
    F.card + (squareElements N A).card ≤
        (nonsquareNonlargeVertices N A).card +
          (squarePrimeSet N A).card := by
      rw [squarePrimeSet_card hinj]
      exact Nat.add_le_add_right hFcard _
    _ = (mediumPrimes N).card + 1 :=
      nonsquareNonlargeVertices_card_add_squarePrimeSet hAN

def auxiliaryColor
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)} :
    AuxiliaryVertex N A D → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

lemma auxiliaryColor_ne_of_adj
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u v : AuxiliaryVertex N A D}
    (huv : (auxiliaryGraph (D := D) hAN hnonzero).Adj u v) :
    auxiliaryColor u ≠ auxiliaryColor v := by
  have hedge : s(u, v) ∈ auxiliaryEdgeFinset (D := D) hAN hnonzero := by
    rw [← auxiliaryGraph_edgeFinset (D := D) hAN hnonzero]
    simpa using huv
  obtain ⟨⟨q, b⟩, hqb, heq⟩ := Finset.mem_image.mp hedge
  rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [← hu, ← hv]
    simp [auxiliaryColor]
  · rw [← hv, ← hu]
    simp [auxiliaryColor]

lemma auxiliaryWalk_even
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    {u : AuxiliaryVertex N A D}
    (w : (auxiliaryGraph (D := D) hAN hnonzero).Walk u u) :
    Even w.length :=
  SimpleGraph.Walk.even_length_of_bicoloring auxiliaryColor
    (auxiliaryColor_ne_of_adj (D := D) hAN hnonzero) w

lemma auxiliaryGraph_no_short_cycle_of_no_short_evenCircuit
    {N K : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoeven : ∀ u : ℕ, ∀ w : (residualProductGraph N A D).Walk u u,
      w.IsCircuit → Even w.length → w.length ≤ K → False) :
    ∀ u : AuxiliaryVertex N A D,
      ∀ c : (auxiliaryGraph (D := D) hAN hnonzero).Walk u u,
        c.IsCycle → c.length ≤ K → False := by
  intro u c hc hlen
  let c' := c.map (auxiliaryHom (D := D) hAN hnonzero)
  have hc' : c'.IsCycle := by
    exact hc.map auxiliaryVertexMap_injective
  have heven : Even c'.length := by
    simpa [c'] using auxiliaryWalk_even hAN hnonzero c
  have hlen' : c'.length ≤ K := by
    simpa [c'] using hlen
  exact hnoeven _ c' hc'.isCircuit heven hlen'

lemma auxiliaryVertex_card
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)} :
    Fintype.card (AuxiliaryVertex N A D) =
      (recurrentLarge N A D).card + (mediumPrimes N).card + 1 := by
  simp only [AuxiliaryVertex, Fintype.card_sum, Fintype.card_coe,
    card_nonlargeVertices]
  omega

/-- Quantitative Moore estimate for the recurrent large-prime vertices.
The selected incidence graph has two edges out of each such prime and its
other colour class has only the medium primes together with the auxiliary
vertex `1`. -/
lemma recurrentLarge_excess_moore
    {N n : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hnoeven : ∀ u : ℕ, ∀ w : (residualProductGraph N A D).Walk u u,
      w.IsCircuit → Even w.length → w.length ≤ 2 * (n + 1) → False) :
    n * ((recurrentLarge N A D).card - ((mediumPrimes N).card + 1)) ≤
      (2 * (recurrentLarge N A D).card) *
        (Nat.log2 ((recurrentLarge N A D).card +
          (mediumPrimes N).card + 1) + 1) := by
  let q := (recurrentLarge N A D).card - ((mediumPrimes N).card + 1)
  by_cases hq : 0 < q
  · have hexcess :
        Fintype.card (AuxiliaryVertex N A D) + q ≤
          (auxiliaryGraph (D := D) hAN hnonzero).edgeFinset.card := by
      rw [auxiliaryVertex_card,
        auxiliaryGraph_card_edges (D := D) hAN hnonzero]
      dsimp [q]
      omega
    have hno := auxiliaryGraph_no_short_cycle_of_no_short_evenCircuit
      hAN hnonzero hnoeven
    have hbound := moore_excess_le (G := auxiliaryGraph (D := D) hAN hnonzero)
      hq hexcess hno
    rw [auxiliaryGraph_card_edges (D := D) hAN hnonzero,
      auxiliaryVertex_card] at hbound
    exact hbound
  · have : q = 0 := Nat.eq_zero_of_not_pos hq
    simp [q, this]

/-! ## Trimming the nonrecurrent large vertices -/

def retainedVertices (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) : Finset ℕ :=
  nonlargeVertices N ∪ recurrentLarge N A D

def looseEdges (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) : Finset (Sym2 ℕ) :=
  (largePrimes N \ recurrentLarge N A D).biUnion
    (fun q ↦ (residualProductGraph N A D).incidenceFinset q)

def trimmedProductGraph (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) : SimpleGraph ℕ :=
  (residualProductGraph N A D).deleteEdges (looseEdges N A D)

noncomputable instance trimmedProductGraph.fintypeEdgeSet
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    Fintype (trimmedProductGraph N A D).edgeSet := by
  apply Set.Finite.fintype
  rw [trimmedProductGraph, SimpleGraph.edgeSet_deleteEdges]
  exact (Set.toFinite (residualProductGraph N A D).edgeSet).sdiff

lemma recurrentLarge_subset_large
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    recurrentLarge N A D ⊆ largePrimes N := by
  exact Finset.filter_subset _ _

lemma retainedVertices_card
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    (retainedVertices N A D).card =
      (mediumPrimes N).card + 1 + (recurrentLarge N A D).card := by
  rw [retainedVertices, Finset.card_union_of_disjoint]
  · rw [card_nonlargeVertices]
  · exact (nonlargeVertices_disjoint_largePrimes N).mono_right
      (recurrentLarge_subset_large N A D)

lemma looseEdges_subset_edgeFinset
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    looseEdges N A D ⊆ (residualProductGraph N A D).edgeFinset := by
  intro e he
  obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp he
  exact (residualProductGraph N A D).incidenceFinset_subset q heq

lemma degree_le_one_of_nonrecurrentLarge
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    {q : ℕ} (hq : q ∈ largePrimes N \ recurrentLarge N A D) :
    (residualProductGraph N A D).degree q ≤ 1 := by
  have hlarge := (Finset.mem_sdiff.mp hq).1
  have hnot := (Finset.mem_sdiff.mp hq).2
  have hnge : ¬ 2 ≤ (residualProductGraph N A D).degree q := by
    intro hdeg
    exact hnot (mem_recurrentLarge.mpr ⟨hlarge, hdeg⟩)
  omega

lemma looseEdges_card_le
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    (looseEdges N A D).card ≤
      (largePrimes N).card - (recurrentLarge N A D).card := by
  let H := residualProductGraph N A D
  calc
    (looseEdges N A D).card ≤
        ∑ q ∈ largePrimes N \ recurrentLarge N A D,
          (H.incidenceFinset q).card := Finset.card_biUnion_le
    _ = ∑ q ∈ largePrimes N \ recurrentLarge N A D,
          H.degree q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact H.card_incidenceFinset_eq_degree q
    _ ≤ ∑ _q ∈ largePrimes N \ recurrentLarge N A D, 1 := by
      apply Finset.sum_le_sum
      intro q hq
      exact degree_le_one_of_nonrecurrentLarge hq
    _ = (largePrimes N \ recurrentLarge N A D).card := by simp
    _ = (largePrimes N).card - (recurrentLarge N A D).card := by
      rw [Finset.card_sdiff_of_subset (recurrentLarge_subset_large N A D)]

lemma trimmedProductGraph_support_subset
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (trimmedProductGraph N A D).support ⊆
      (↑(retainedVertices N A D) : Set ℕ) := by
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hvw⟩ := hv
  have hvwH : (residualProductGraph N A D).Adj v w := hvw.1
  rcases (residual_adj_endpoint_classification hAN hnonzero hvwH).1 with
      hvNonlarge | hvLarge
  · exact Finset.mem_union_left _ hvNonlarge
  · by_cases hvRec : v ∈ recurrentLarge N A D
    · exact Finset.mem_union_right _ hvRec
    · exfalso
      have hvOut : v ∈ largePrimes N \ recurrentLarge N A D :=
        Finset.mem_sdiff.mpr ⟨hvLarge, hvRec⟩
      have hedgeInc : s(v, w) ∈
          (residualProductGraph N A D).incidenceFinset v := by
        rw [(residualProductGraph N A D).incidenceFinset_eq_filter]
        simp [hvwH]
      have hedgeLoose : s(v, w) ∈ looseEdges N A D := by
        exact Finset.mem_biUnion.mpr ⟨v, hvOut, hedgeInc⟩
      apply hvw.2
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hedgeLoose, hvwH.ne⟩

lemma trimmedProductGraph_card_add_loose
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    (trimmedProductGraph N A D).edgeFinset.card +
        (looseEdges N A D).card =
      (residualProductGraph N A D).edgeFinset.card := by
  let : Fintype ((residualProductGraph N A D).deleteEdges
      (↑(looseEdges N A D) : Set (Sym2 ℕ))).edgeSet := by
    apply Set.Finite.fintype
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact (Set.toFinite (residualProductGraph N A D).edgeSet).sdiff
  change ((residualProductGraph N A D).deleteEdges
      (looseEdges N A D)).edgeFinset.card + (looseEdges N A D).card = _
  rw [SimpleGraph.edgeFinset_deleteEdges,
    Finset.card_sdiff_add_card_eq_card (looseEdges_subset_edgeFinset N A D)]

def retainedFiniteGraph (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) :
    SimpleGraph (↑(retainedVertices N A D) : Set ℕ) :=
  (trimmedProductGraph N A D).induce
    (↑(retainedVertices N A D) : Set ℕ)

lemma retainedFiniteGraph_card_edges
    {N : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0) :
    (retainedFiniteGraph N A D).edgeFinset.card =
      (trimmedProductGraph N A D).edgeFinset.card := by
  let Kgraph := trimmedProductGraph N A D
  let S : Set ℕ := ↑(retainedVertices N A D)
  let ι : S ↪ ℕ := Function.Embedding.subtype _
  have hsupp : Kgraph.support ⊆ S :=
    trimmedProductGraph_support_subset hAN hnonzero
  have hend {x y : ℕ} (hxy : Kgraph.Adj x y) : x ∈ S ∧ y ∈ S :=
    ⟨hsupp ⟨y, hxy⟩, hsupp ⟨x, hxy.symm⟩⟩
  have hmap :
      (Kgraph.induce S).edgeFinset.map ι.sym2Map = Kgraph.edgeFinset := by
    aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall,
      SimpleGraph.adj_comm, Kgraph, S, ι]) <;>
      exact ⟨x, (hend a).1, y, a, (hend a).2, Or.inl ⟨rfl, rfl⟩⟩
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map] at hcard
  change (Kgraph.induce S).edgeFinset.card = Kgraph.edgeFinset.card
  convert hcard using 1 <;>
    rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card] <;>
    exact Fintype.card_congr (Equiv.refl _)

def retainedHom (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    retainedFiniteGraph N A D →g residualProductGraph N A D :=
  (SimpleGraph.Hom.ofLE (show trimmedProductGraph N A D ≤
      residualProductGraph N A D by
        exact SimpleGraph.deleteEdges_le
          (↑(looseEdges N A D) : Set (Sym2 ℕ)))).comp
    (SimpleGraph.Embedding.induce (G := trimmedProductGraph N A D)
      (↑(retainedVertices N A D) : Set ℕ)).toHom

lemma retainedHom_injective (N : ℕ) (A : Finset ℕ)
    (D : Finset (Sym2 ℕ)) : Function.Injective (retainedHom N A D) := by
  intro x y hxy
  apply Subtype.ext
  exact hxy

lemma retainedFiniteGraph_no_short_cycle
    {N K : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hno : ∀ z : ℕ, ∀ c : (residualProductGraph N A D).Walk z z,
      c.IsCycle → c.length ≤ K → False) :
    ∀ z : (↑(retainedVertices N A D) : Set ℕ),
      ∀ c : (retainedFiniteGraph N A D).Walk z z,
        c.IsCycle → c.length ≤ K → False := by
  intro z c hc hlen
  let cH := c.map (retainedHom N A D)
  have hcH : cH.IsCycle := hc.map (retainedHom_injective N A D)
  have walkMapLength : ∀ {x y : (↑(retainedVertices N A D) : Set ℕ)}
      (w : (retainedFiniteGraph N A D).Walk x y),
      (w.map (retainedHom N A D)).length = w.length := by
    intro x y w
    induction w with
    | nil => rfl
    | cons h p ih =>
        simp only [SimpleGraph.Walk.map, SimpleGraph.Walk.length]
        exact congrArg Nat.succ ih
  have hmapLength : cH.length = c.length := by
    exact walkMapLength c
  exact hno ((retainedHom N A D) z) cH hcH (hmapLength ▸ hlen)

lemma retained_excess_moore
    {N n : ℕ} {A : Finset ℕ} {D : Finset (Sym2 ℕ)}
    (hAN : A ⊆ interval N)
    (hnonzero : ∀ a ∈ A, highFactorization N a ≠ 0)
    (hno : ∀ z : ℕ, ∀ c : (residualProductGraph N A D).Walk z z,
      c.IsCycle → c.length ≤ 2 * (n + 1) → False) :
    n * ((trimmedProductGraph N A D).edgeFinset.card -
      (retainedVertices N A D).card) ≤
      (trimmedProductGraph N A D).edgeFinset.card *
        (Nat.log2 ((retainedVertices N A D).card) + 1) := by
  let q := (trimmedProductGraph N A D).edgeFinset.card -
    (retainedVertices N A D).card
  by_cases hq : 0 < q
  · have hexcess :
        Fintype.card (↑(retainedVertices N A D) : Set ℕ) + q ≤
          (retainedFiniteGraph N A D).edgeFinset.card := by
      have hVcard :
          Fintype.card (↑(retainedVertices N A D) : Set ℕ) =
            (retainedVertices N A D).card := by simp
      rw [hVcard, retainedFiniteGraph_card_edges hAN hnonzero]
      dsimp [q]
      omega
    have hbound := moore_excess_le
      (G := retainedFiniteGraph N A D) hq hexcess
      (retainedFiniteGraph_no_short_cycle hno)
    have hVcard :
        Fintype.card (↑(retainedVertices N A D) : Set ℕ) =
          (retainedVertices N A D).card := by simp
    rw [hVcard, retainedFiniteGraph_card_edges hAN hnonzero] at hbound
    exact hbound
  · have : q = 0 := Nat.eq_zero_of_not_pos hq
    simp [q, this]

/-! ## Assembly lemmas for the finite estimate -/

lemma noShortCircuit_deleteEdges
    {G : SimpleGraph ℕ} {F : Finset (Sym2 ℕ)} {K : ℕ}
    {P : ℕ → Prop}
    (hno : ∀ z : ℕ, ∀ c : G.Walk z z,
      c.IsCircuit → P c.length → c.length ≤ K → False) :
    ∀ z : ℕ, ∀ c : (G.deleteEdges F).Walk z z,
      c.IsCircuit → P c.length → c.length ≤ K → False := by
  intro z c hc hP hlen
  have hedge : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
    intro e he
    have he' := c.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges] at he'
    exact he'.1
  let cG := c.transfer G hedge
  have hcG : cG.IsCircuit := isCircuit_transfer hc hedge
  have hPG : P cG.length := by simpa [cG] using hP
  have hlenG : cG.length ≤ K := by simpa [cG] using hlen
  exact hno z cG hcG hPG hlenG

lemma noShortCircuit_of_noShortCycle
    {G : SimpleGraph ℕ} {K : ℕ}
    (hno : ∀ z : ℕ, ∀ c : G.Walk z z,
      c.IsCycle → c.length ≤ K → False) :
    ∀ z : ℕ, ∀ c : G.Walk z z,
      c.IsCircuit → c.length ≤ K → False := by
  intro z c hc hlen
  exact hno z c.cycleBypass hc.isCycle_cycleBypass
    ((c.length_cycleBypass_le_length).trans hlen)

lemma recurrentLarge_card_add_medium_le
    (N : ℕ) (A : Finset ℕ) (D : Finset (Sym2 ℕ)) :
    (recurrentLarge N A D).card + (mediumPrimes N).card ≤ N := by
  have hdis : Disjoint (recurrentLarge N A D) (mediumPrimes N) :=
    (mediumPrimes_disjoint_largePrimes N).symm.mono_left
      (recurrentLarge_subset_large N A D)
  rw [← Finset.card_union_of_disjoint hdis]
  calc
    (recurrentLarge N A D ∪ mediumPrimes N).card ≤ (interval N).card := by
      apply Finset.card_le_card
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · have hp' := mem_largePrimes.mp
          (recurrentLarge_subset_large N A D hp)
        exact Finset.mem_Icc.mpr ⟨hp'.1, hp'.2.2.1⟩
      · have hp' := mem_mediumPrimes.mp hp
        exact Finset.mem_Icc.mpr
          ⟨hp'.1, hp'.2.2.1.trans (sqrt_le_self N)⟩
    _ = N := interval_card N

lemma binaryScale_two_le {N : ℕ} (hN : 1 ≤ N) :
    2 ≤ binaryScale N := by
  have hlog : 1 ≤ Nat.log2 (N + 1) := by
    apply (Nat.le_log2 (by omega)).2
    norm_num
    omega
  simp only [binaryScale]
  omega

lemma cubic_moore_vertex_bound
    {ell m q : ℕ} (hell : 2 ≤ ell)
    (hmoore : ell ^ 3 * (q - m) ≤ 2 * q * ell) :
    q ≤ 2 * m := by
  by_contra hqm
  have hq : 0 < q := by omega
  have hsub : q < 2 * (q - m) := by omega
  have hleft : ell ^ 3 * q < ell ^ 3 * (2 * (q - m)) := by
    exact (Nat.mul_lt_mul_left (by positivity : 0 < ell ^ 3)).2 hsub
  have hright : ell ^ 3 * (2 * (q - m)) ≤ 2 * (2 * q * ell) := by
    calc
      ell ^ 3 * (2 * (q - m)) = 2 * (ell ^ 3 * (q - m)) := by ring
      _ ≤ 2 * (2 * q * ell) := Nat.mul_le_mul_left 2 hmoore
  have hcancel : ell ^ 3 < 4 * ell := by
    apply (Nat.mul_lt_mul_left hq).mp
    calc
      q * ell ^ 3 = ell ^ 3 * q := by ring
      _ < 2 * (2 * q * ell) := hleft.trans_le hright
      _ = q * (4 * ell) := by ring
  have hsquare : 4 ≤ ell ^ 2 := by nlinarith
  have hcontra : 4 * ell ≤ ell ^ 3 := by
    calc
      4 * ell ≤ ell ^ 2 * ell := Nat.mul_le_mul_right ell hsquare
      _ = ell ^ 3 := by ring
  omega

lemma cubic_moore_excess_bound
    {ell m q : ℕ} (hell : 2 ≤ ell) (hq : q ≤ 2 * m)
    (hmoore : ell ^ 3 * (q - m) ≤ 2 * q * ell) :
    ell ^ 2 * (q - m) ≤ 4 * m := by
  have htotal : ell * (ell ^ 2 * (q - m)) ≤ ell * (4 * m) := by
    calc
    ell * (ell ^ 2 * (q - m)) = ell ^ 3 * (q - m) := by ring
    _ ≤ 2 * q * ell := hmoore
    _ ≤ ell * (4 * m) := by
      have := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 2 hq)
      nlinarith
  exact Nat.le_of_mul_le_mul_left htotal (by omega)

lemma cubic_moore_edge_bound
    {ell s e : ℕ} (hell : 2 ≤ ell)
    (hmoore : ell ^ 3 * (e - s) ≤ e * ell) :
    e ≤ 2 * s := by
  by_contra hes
  have he : 0 < e := by omega
  have hsub : e < 2 * (e - s) := by omega
  have hleft : ell ^ 3 * e < ell ^ 3 * (2 * (e - s)) := by
    exact (Nat.mul_lt_mul_left (by positivity : 0 < ell ^ 3)).2 hsub
  have hright : ell ^ 3 * (2 * (e - s)) ≤ 2 * (e * ell) := by
    calc
      ell ^ 3 * (2 * (e - s)) = 2 * (ell ^ 3 * (e - s)) := by ring
      _ ≤ 2 * (e * ell) := Nat.mul_le_mul_left 2 hmoore
  have hcancel : ell ^ 3 < 2 * ell := by
    apply (Nat.mul_lt_mul_left he).mp
    calc
      e * ell ^ 3 = ell ^ 3 * e := by ring
      _ < 2 * (e * ell) := hleft.trans_le hright
      _ = e * (2 * ell) := by ring
  have hsquare : 2 ≤ ell ^ 2 := by nlinarith
  have hcontra : 2 * ell ≤ ell ^ 3 := by
    calc
      2 * ell ≤ ell ^ 2 * ell := Nat.mul_le_mul_right ell hsquare
      _ = ell ^ 3 := by ring
  omega

lemma cubic_moore_edge_excess_bound
    {ell m s e : ℕ} (hell : 2 ≤ ell)
    (hs : s ≤ 3 * m) (he : e ≤ 2 * s)
    (hmoore : ell ^ 3 * (e - s) ≤ e * ell) :
    ell ^ 2 * (e - s) ≤ 6 * m := by
  have htotal : ell * (ell ^ 2 * (e - s)) ≤ ell * (6 * m) := by
    calc
    ell * (ell ^ 2 * (e - s)) = ell ^ 3 * (e - s) := by ring
    _ ≤ e * ell := hmoore
    _ ≤ ell * (6 * m) := by
      have h := he.trans (Nat.mul_le_mul_left 2 hs)
      have := Nat.mul_le_mul_right ell h
      nlinarith
  exact Nat.le_of_mul_le_mul_left htotal (by omega)

lemma card_large_add_twice_medium_le (N : ℕ) :
    (largePrimes N).card + 2 * ((mediumPrimes N).card + 1) ≤
      Nat.primeCounting N + Nat.primeCounting (Nat.sqrt N) + 2 := by
  have hcube : Nat.primeCounting (cubeRoot N) ≤
      Nat.primeCounting (Nat.sqrt N) := by
    rw [← card_smallPrimes, ← card_primesUpTo]
    exact Finset.card_le_card (smallPrimes_subset_sqrt N)
  have hsqrt : Nat.primeCounting (Nat.sqrt N) ≤
      Nat.primeCounting N := by
    rw [← card_primesUpTo, ← card_primesUpTo]
    exact Finset.card_le_card (primesUpTo_sqrt_subset N)
  rw [card_largePrimes, card_mediumPrimes]
  omega

/-- The completely explicit finite remainder furnished by the graph proof.
It is `O(N^(1/3) log(N)^4 + sqrt(N)/log(N)^2)`. -/
def finiteError (N : ℕ) : ℕ :=
  (4 * shortCycleCutoff N + 2) * smallPrimeError N + 3 +
    (6 * ((mediumPrimes N).card + 1)) / (binaryScale N ^ 2)

/-- Exact finite form of Raghavan's upper-bound argument.  This is the
combinatorial heart of the resolution of Problem 795. -/
theorem card_le_primeCounting_add_sqrt_add_finiteError
    {N : ℕ} (hN : 1 ≤ N) {A : Finset ℕ}
    (hAN : A ⊆ interval N) (hA : DistinctSubsetProducts A) :
    A.card ≤ Nat.primeCounting N + Nat.primeCounting (Nat.sqrt N) +
      finiteError N := by
  obtain ⟨B, k₀, hBA, hBinj, hBzero, hAcard, hk₀⟩ :=
    exists_highFactorization_injective_nonzero_subset hAN hA
  have hBN : B ⊆ interval N := hBA.trans hAN
  have hB : DistinctSubsetProducts B := hA.mono hBA
  let L := shortCycleCutoff N
  obtain ⟨D, kD, hDsub, hDcard, hkD, hDno⟩ :=
    exists_deleteEdges_no_short_evenCircuit
      (N := N) (A := B) (L := 3 * L) hBN hB hBinj hBzero
  have hDnoTwo : ∀ u : ℕ,
      ∀ w : ((productGraph N B).deleteEdges D).Walk u u,
        w.IsCircuit → Even w.length → w.length ≤ 2 * L → False := by
    intro u w hw heven hlen
    exact hDno u w hw heven (by omega)
  obtain ⟨E, kE, hEsub, hEcard, hkE, hEno⟩ :=
    exists_deleteEdges_no_short_squareCircuit
      (N := N) (A := B) (D := D) (L := L)
      hBN hB hBinj hBzero hDnoTwo
  let DE : Finset (Sym2 ℕ) := D ∪ E
  have hEvenNested : ∀ u : ℕ,
      ∀ w : (((productGraph N B).deleteEdges D).deleteEdges E).Walk u u,
        w.IsCircuit → Even w.length → w.length ≤ 3 * L → False :=
    noShortCircuit_deleteEdges hDno
  have hgraphDE :
      ((productGraph N B).deleteEdges D).deleteEdges E =
        residualProductGraph N B DE := by
    ext u v
    simp [residualProductGraph, DE]
  have hEvenDE : ∀ u : ℕ,
      ∀ w : (residualProductGraph N B DE).Walk u u,
        w.IsCircuit → Even w.length → w.length ≤ 3 * L → False := by
    rw [← hgraphDE]
    exact hEvenNested
  have hSquareDE : ∀ p ∈ squarePrimeSet N B,
      ∀ w : (residualProductGraph N B DE).Walk p p,
        w.IsCircuit → Odd w.length → w.length ≤ L → False := by
    rw [← hgraphDE]
    exact hEno
  obtain ⟨F, hFsub, hFsquare, hFno⟩ :=
    exists_deleteEdges_no_short_cycle hBN hBinj hBzero hEvenDE hSquareDE
  let U : Finset (Sym2 ℕ) := DE ∪ F
  have hgraphU :
      (residualProductGraph N B DE).deleteEdges F =
        residualProductGraph N B U := by
    ext u v
    simp [residualProductGraph, U, DE, and_assoc]
  have hUno : ∀ z : ℕ, ∀ c : (residualProductGraph N B U).Walk z z,
      c.IsCycle → c.length ≤ L → False := by
    rw [← hgraphU]
    exact hFno
  have hUnocircuit : ∀ z : ℕ,
      ∀ c : (residualProductGraph N B U).Walk z z,
        c.IsCircuit → c.length ≤ L → False :=
    noShortCircuit_of_noShortCycle hUno
  have hUnoeven : ∀ z : ℕ,
      ∀ c : (residualProductGraph N B U).Walk z z,
        c.IsCircuit → Even c.length → c.length ≤ L → False := by
    intro z c hc _ hlen
    exact hUnocircuit z c hc hlen

  let ell := binaryScale N
  let m := (mediumPrimes N).card + 1
  let q := (recurrentLarge N B U).card
  let s := (retainedVertices N B U).card
  let e := (trimmedProductGraph N B U).edgeFinset.card
  have hell : 2 ≤ ell := by simpa [ell] using binaryScale_two_le hN
  have hsEq : s = m + q := by
    dsimp [s, m, q]
    rw [retainedVertices_card]
  have hsN : s ≤ N + 1 := by
    have hqm := recurrentLarge_card_add_medium_le N B U
    dsimp [s, m, q] at hsEq ⊢
    rw [retainedVertices_card]
    omega
  have hlog : Nat.log2 s + 1 ≤ ell := by
    dsimp [ell]
    exact Nat.add_le_add_right (Nat.log2_mono_of_le hsN) 1

  have hqMoore₀ := recurrentLarge_excess_moore
    (N := N) (A := B) (D := U) (n := cycleCutoff N)
    hBN hBzero (by
      simpa only [L, shortCycleCutoff] using hUnoeven)
  have hqMoore : ell ^ 3 * (q - m) ≤ 2 * q * ell := by
    have hlogq : Nat.log2 (q + (mediumPrimes N).card + 1) + 1 ≤ ell := by
      have heq : q + (mediumPrimes N).card + 1 = s := by
        omega
      rwa [heq]
    have htrans := hqMoore₀.trans
      (Nat.mul_le_mul_left (2 * q) hlogq)
    simpa only [cycleCutoff, ell, m, q, Nat.mul_assoc] using htrans
  have hqBound : q ≤ 2 * m := cubic_moore_vertex_bound hell hqMoore
  have hsBound : s ≤ 3 * m := by omega

  have heMoore₀ := retained_excess_moore
    (N := N) (A := B) (D := U) (n := cycleCutoff N)
      hBN hBzero (by simpa only [L, shortCycleCutoff] using hUno)
  have heMoore : ell ^ 3 * (e - s) ≤ e * ell := by
    have htrans := heMoore₀.trans (Nat.mul_le_mul_left e hlog)
    simpa only [cycleCutoff, ell, e, s] using htrans
  have heBound : e ≤ 2 * s := cubic_moore_edge_bound hell heMoore
  have hexcess : ell ^ 2 * (e - s) ≤ 6 * m :=
    cubic_moore_edge_excess_bound hell hsBound heBound heMoore
  have hexcessDiv : e - s ≤ (6 * m) / (ell ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < ell ^ 2)).2
    simpa [Nat.mul_comm] using hexcess

  have hEprod : E ⊆ (productGraph N B).edgeFinset := by
    intro x hx
    have hx' := hEsub hx
    rw [SimpleGraph.edgeFinset_deleteEdges] at hx'
    exact (Finset.mem_sdiff.mp hx').1
  have hDEsub : DE ⊆ (productGraph N B).edgeFinset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hDsub hx
    · exact hEprod hx
  have hFprod : F ⊆ (productGraph N B).edgeFinset := by
    intro x hx
    have hx' := hFsub hx
    have hx'' : x ∈ (residualProductGraph N B DE).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using hx'
    rw [residualProductGraph, SimpleGraph.edgeSet_deleteEdges] at hx''
    simpa only [SimpleGraph.mem_edgeFinset] using hx''.1
  have hUsub : U ⊆ (productGraph N B).edgeFinset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hDEsub hx
    · exact hFprod hx
  have hresidual : (residualProductGraph N B U).edgeFinset.card + U.card =
      (productGraph N B).edgeFinset.card := by
    change ((productGraph N B).deleteEdges U).edgeFinset.card + U.card = _
    rw [SimpleGraph.edgeFinset_deleteEdges,
      Finset.card_sdiff_add_card_eq_card hUsub]

  have hk₀' : k₀ ≤ smallPrimeError N := packingCount_le_smallPrimeError' hk₀
  have hkD' : kD ≤ smallPrimeError N := packingCount_le_smallPrimeError' hkD
  have hkE' : kE ≤ smallPrimeError N := packingCount_le_smallPrimeError' hkE
  have hDEcard : DE.card ≤ 4 * L * smallPrimeError N := by
    have hdu := Finset.card_union_le D E
    calc
      DE.card ≤ D.card + E.card := by simpa [DE] using hdu
      _ ≤ (3 * L) * kD + L * kE := Nat.add_le_add hDcard hEcard
      _ ≤ 4 * L * smallPrimeError N := by
        have h1 := Nat.mul_le_mul_left (3 * L) hkD'
        have h2 := Nat.mul_le_mul_left L hkE'
        nlinarith
  have hUsquare : U.card + (squareElements N B).card ≤
      4 * L * smallPrimeError N + m := by
    have hu := Finset.card_union_le DE F
    have hu' : U.card ≤ DE.card + F.card := by simpa [U] using hu
    omega

  have htrim := trimmedProductGraph_card_add_loose N B U
  have hloose := looseEdges_card_le N B U
  have heSplit : e ≤ s + (e - s) := by omega
  have hresBound : (residualProductGraph N B U).edgeFinset.card ≤
      (largePrimes N).card + m + (e - s) := by
    dsimp [e, s, m, q] at htrim hloose heSplit ⊢
    rw [retainedVertices_card] at heSplit
    have hqLarge := Finset.card_le_card (recurrentLarge_subset_large N B U)
    omega
  have hBgraph := productGraph_card_edges_add_squares hBN hBinj hBzero
  have hBcard : B.card ≤
      (largePrimes N).card + 2 * m + (e - s) +
        4 * L * smallPrimeError N := by
    omega
  have hprime := card_large_add_twice_medium_le N
  have hAfinite : A.card ≤
      Nat.primeCounting N + Nat.primeCounting (Nat.sqrt N) +
        ((4 * L + 2) * smallPrimeError N + 3 + (e - s)) := by
    have herr : (4 * L + 2) * smallPrimeError N =
        4 * L * smallPrimeError N + 2 * smallPrimeError N := by ring
    rw [herr]
    omega
  dsimp [finiteError, L] at ⊢ hAfinite
  dsimp [L, ell, m] at hexcessDiv
  omega

/-! ## Asymptotics of the explicit remainder -/

lemma smallPrimeError_le (N : ℕ) :
    smallPrimeError N ≤ 2 * cubeRoot N * binaryScale N := by
  let ell := binaryScale N
  have hpow : N + 1 < 2 ^ ell := by
    simpa only [ell, binaryScale] using
      Nat.lt_two_pow_log2_add_one (N + 1) (by omega)
  have hsq : (N + 1) ^ 2 < (2 ^ ell) ^ 2 :=
    Nat.pow_lt_pow_left hpow (by norm_num)
  have hNN : N * N + 1 < 2 ^ (2 * ell) := by
    calc
      N * N + 1 ≤ (N + 1) ^ 2 := by nlinarith
      _ < (2 ^ ell) ^ 2 := hsq
      _ = 2 ^ (2 * ell) := by rw [← Nat.pow_mul]; ring_nf
  have hlog : Nat.log 2 (N * N + 1) + 1 ≤ 2 * ell := by
    have hlt := (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2)
      (by omega : N * N + 1 ≠ 0)).2 hNN
    omega
  calc
    smallPrimeError N = (smallPrimes N).card *
        (Nat.log 2 (N * N + 1) + 1) := rfl
    _ ≤ cubeRoot N * (2 * ell) :=
      Nat.mul_le_mul (card_smallPrimes_le_cubeRoot N) hlog
    _ = 2 * cubeRoot N * binaryScale N := by simp [ell]; ring

lemma finiteError_deletionPart_le {N : ℕ} (hN : 1 ≤ N) :
    (4 * shortCycleCutoff N + 2) * smallPrimeError N + 3 ≤
      39 * cubeRoot N * binaryScale N ^ 4 := by
  let ell := binaryScale N
  have hell : 2 ≤ ell := by simpa [ell] using binaryScale_two_le hN
  have hcube : 1 ≤ cubeRoot N := by
    rw [cubeRoot, Nat.le_nthRoot_iff (by norm_num)]
    simpa using hN
  have hsmall := smallPrimeError_le N
  have hL : shortCycleCutoff N ≤ 4 * ell ^ 3 := by
    simp only [shortCycleCutoff, cycleCutoff, ell]
    have hp : 0 < ell ^ 3 := by positivity
    nlinarith
  have hcoeff : 4 * shortCycleCutoff N + 2 ≤ 18 * ell ^ 3 := by
    have hp : 0 < ell ^ 3 := by positivity
    nlinarith
  have hmain := Nat.mul_le_mul hcoeff hsmall
  dsimp [ell] at hmain ⊢
  nlinarith [show 3 ≤ 3 * cubeRoot N * binaryScale N ^ 4 by
    have hp : 0 < binaryScale N ^ 4 := by positivity
    nlinarith]

lemma mediumPrimes_card_le_sqrt (N : ℕ) :
    (mediumPrimes N).card ≤ Nat.sqrt N := by
  calc
    (mediumPrimes N).card ≤ (interval (Nat.sqrt N)).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(mem_mediumPrimes.mp hp).1,
        (mem_mediumPrimes.mp hp).2.2.1⟩
    _ = Nat.sqrt N := interval_card _

lemma cubeRoot_cast_le_rpow (N : ℕ) :
    (cubeRoot N : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 3)).2
  exact_mod_cast cubeRoot_pow_le N

lemma natSqrt_cast_le_realSqrt (N : ℕ) :
    (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
  have hN : (0 : ℝ) ≤ N := by positivity
  rw [Real.le_sqrt (by positivity) hN]
  exact_mod_cast Nat.sqrt_le' N

lemma log_nat_le_binaryScale {N : ℕ} (hN : N ≠ 0) :
    Real.log (N : ℝ) ≤ (binaryScale N : ℝ) := by
  have hlog := log_nat_le_log2_add_one_mul_log_two N hN
  have hmono : Nat.log2 N + 1 ≤ binaryScale N := by
    simp only [binaryScale]
    exact Nat.add_le_add_right (Nat.log2_mono_of_le (Nat.le_add_right N 1)) 1
  have htwo : (((Nat.log2 N + 1 : ℕ) : ℝ)) * Real.log 2 ≤
      ((Nat.log2 N + 1 : ℕ) : ℝ) := by
    have ha : (0 : ℝ) ≤ ((Nat.log2 N + 1 : ℕ) : ℝ) := by positivity
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hmonoR : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤
      (binaryScale N : ℝ) := by exact_mod_cast hmono
  exact hlog.trans (htwo.trans hmonoR)

lemma binaryScale_cast_le_log {N : ℕ} (hN : 1 ≤ N)
    (hlogOne : (1 : ℝ) ≤ Real.log N) :
    (binaryScale N : ℝ) ≤
      ((Real.log 2)⁻¹ + 2) * Real.log (N : ℝ) := by
  let a := Nat.log2 (N + 1)
  have hpowNat : 2 ^ a ≤ N + 1 := by
    exact (Nat.le_log2 (by omega : N + 1 ≠ 0)).1 le_rfl
  have hpow : (2 : ℝ) ^ a ≤ (N + 1 : ℕ) := by exact_mod_cast hpowNat
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hlogPow : (a : ℝ) * Real.log 2 ≤ Real.log (N + 1 : ℕ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hpowPos hpow
  have hNpos : (0 : ℝ) < N := by positivity
  have hNadd : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by
    exact_mod_cast (by omega : N + 1 ≤ 2 * N)
  have hlogAdd : Real.log (N + 1 : ℕ) ≤ Real.log 2 + Real.log N := by
    calc
      Real.log (N + 1 : ℕ) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by positivity) hNadd
      _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) hNpos.ne'
  have ha : (a : ℝ) ≤ Real.log N / Real.log 2 + 1 := by
    have hmul : (a : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log N :=
      hlogPow.trans hlogAdd
    have htwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ha₀ : (a : ℝ) ≤ (Real.log 2 + Real.log N) / Real.log 2 :=
      (le_div_iff₀ htwoPos).2 hmul
    calc
      (a : ℝ) ≤ (Real.log 2 + Real.log N) / Real.log 2 := ha₀
      _ = Real.log N / Real.log 2 + 1 := by
        field_simp [htwoPos.ne']
        ring
  simp only [binaryScale, a]
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Nat.log2 (N + 1) + 1 : ℕ) = (a : ℝ) + 1 := by simp [a]
    _ ≤ Real.log N / Real.log 2 + 2 := by linarith
    _ ≤ ((Real.log 2)⁻¹ + 2) * Real.log N := by
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg (le_of_lt htwo) (le_of_lt hNpos)]

theorem finiteError_isLittleO :
    (fun N : ℕ ↦ (finiteError N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ Real.sqrt N / Real.log N) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let C : ℝ := (Real.log 2)⁻¹ + 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let δ : ℝ := ε / (78 * C ^ 4)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hlogPower :
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ 5) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ) ^ (1 / 6 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop 5
        (by norm_num : (0 : ℝ) < 1 / 6)).comp_tendsto
          tendsto_natCast_atTop_atTop
  have hpowerBound := (Asymptotics.isLittleO_iff.mp hlogPower) hδ
  have hlogTendsto : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpowerBound, eventually_ge_atTop (1 : ℕ),
      hlogTendsto.eventually (eventually_ge_atTop (1 : ℝ)),
      hlogTendsto.eventually (eventually_ge_atTop (24 / ε))] with
      N hpower hN hlogOne hlogLarge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogPos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogOne
  have hsqrtPos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hpower' : Real.log (N : ℝ) ^ 5 ≤
      δ * (N : ℝ) ^ (1 / 6 : ℝ) := by
    rw [Real.norm_of_nonneg (pow_nonneg hlogPos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hpower
    exact hpower
  have hscale : (binaryScale N : ℝ) ≤ C * Real.log N := by
    simpa only [C] using binaryScale_cast_le_log hN hlogOne
  have hscaleNonneg : 0 ≤ C * Real.log (N : ℝ) :=
    mul_nonneg hC.le hlogPos.le
  have hrpow : (N : ℝ) ^ (1 / 3 : ℝ) *
      (N : ℝ) ^ (1 / 6 : ℝ) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
    norm_num
  let deletionPart : ℕ :=
    (4 * shortCycleCutoff N + 2) * smallPrimeError N + 3
  let moorePart : ℕ :=
    (6 * ((mediumPrimes N).card + 1)) / (binaryScale N ^ 2)
  have hdeletion₀ : (deletionPart : ℝ) ≤
      39 * (cubeRoot N : ℝ) * (binaryScale N : ℝ) ^ 4 := by
    exact_mod_cast finiteError_deletionPart_le hN
  have hdeletion₁ : (deletionPart : ℝ) ≤
      39 * C ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) *
        Real.log N ^ 4 := by
    calc
      (deletionPart : ℝ) ≤
          39 * (cubeRoot N : ℝ) * (binaryScale N : ℝ) ^ 4 := hdeletion₀
      _ ≤ 39 * ((N : ℝ) ^ (1 / 3 : ℝ)) *
          (C * Real.log N) ^ 4 := by
        gcongr
        · exact cubeRoot_cast_le_rpow N
      _ = 39 * C ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) *
          Real.log N ^ 4 := by ring
  have hdeletion : (deletionPart : ℝ) ≤
      (ε / 2) * (Real.sqrt N / Real.log N) := by
    rw [show (ε / 2) * (Real.sqrt N / Real.log N) =
        ((ε / 2) * Real.sqrt N) / Real.log N by ring]
    apply (le_div_iff₀ hlogPos).2
    calc
      (deletionPart : ℝ) * Real.log N ≤
          (39 * C ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) *
            Real.log N ^ 4) * Real.log N :=
        mul_le_mul_of_nonneg_right hdeletion₁ hlogPos.le
      _ = 39 * C ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) *
          Real.log N ^ 5 := by ring
      _ ≤ 39 * C ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) *
          (δ * (N : ℝ) ^ (1 / 6 : ℝ)) := by
        gcongr
      _ = (ε / 2) * Real.sqrt N := by
        rw [show 39 * C ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) *
            (δ * (N : ℝ) ^ (1 / 6 : ℝ)) =
            (39 * C ^ 4 * δ) * ((N : ℝ) ^ (1 / 3 : ℝ) *
              (N : ℝ) ^ (1 / 6 : ℝ)) by ring,
          hrpow]
        dsimp [δ]
        field_simp [hC.ne']
        ring

  have hmooreMulNat : moorePart * binaryScale N ^ 2 ≤
      6 * ((mediumPrimes N).card + 1) := by
    exact Nat.div_mul_le_self _ _
  have hmooreMul : (moorePart : ℝ) * (binaryScale N : ℝ) ^ 2 ≤
      6 * (((mediumPrimes N).card + 1 : ℕ) : ℝ) := by
    exact_mod_cast hmooreMulNat
  have hlogScale : Real.log (N : ℝ) ≤ (binaryScale N : ℝ) :=
    log_nat_le_binaryScale (by omega)
  have hmedium : ((mediumPrimes N).card : ℝ) ≤ Real.sqrt N := by
    have hmedium' : ((mediumPrimes N).card : ℝ) ≤ (Nat.sqrt N : ℝ) := by
      exact_mod_cast mediumPrimes_card_le_sqrt N
    exact hmedium'.trans (natSqrt_cast_le_realSqrt N)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt N := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hmooreLogSq : (moorePart : ℝ) * Real.log N ^ 2 ≤
      12 * Real.sqrt N := by
    calc
      (moorePart : ℝ) * Real.log N ^ 2 ≤
          (moorePart : ℝ) * (binaryScale N : ℝ) ^ 2 := by
        gcongr
      _ ≤ 6 * (((mediumPrimes N).card + 1 : ℕ) : ℝ) := hmooreMul
      _ ≤ 12 * Real.sqrt N := by
        push_cast
        nlinarith
  have hlargeMul : (24 : ℝ) ≤ ε * Real.log N := by
    have := mul_le_mul_of_nonneg_left hlogLarge hε.le
    field_simp [hε.ne'] at this
    nlinarith
  have hmooreLog : (moorePart : ℝ) * Real.log N ≤
      (ε / 2) * Real.sqrt N := by
    have hleft : 2 * ((moorePart : ℝ) * Real.log N ^ 2) ≤
        24 * Real.sqrt N := by nlinarith
    have hright : 24 * Real.sqrt N ≤
        ε * Real.sqrt N * Real.log N := by
      nlinarith [mul_le_mul_of_nonneg_right hlargeMul (Real.sqrt_nonneg N)]
    have hcancel : (2 * (moorePart : ℝ) * Real.log N) * Real.log N ≤
        (ε * Real.sqrt N) * Real.log N := by
      calc
        (2 * (moorePart : ℝ) * Real.log N) * Real.log N =
            2 * ((moorePart : ℝ) * Real.log N ^ 2) := by ring
        _ ≤ 24 * Real.sqrt N := hleft
        _ ≤ ε * Real.sqrt N * Real.log N := hright
    have := le_of_mul_le_mul_right hcancel hlogPos
    nlinarith
  have hmoore : (moorePart : ℝ) ≤
      (ε / 2) * (Real.sqrt N / Real.log N) := by
    rw [show (ε / 2) * (Real.sqrt N / Real.log N) =
        ((ε / 2) * Real.sqrt N) / Real.log N by ring]
    exact (le_div_iff₀ hlogPos).2 hmooreLog
  have herror : (finiteError N : ℝ) = deletionPart + moorePart := by
    simp only [finiteError, deletionPart, moorePart, Nat.cast_add]
  rw [herror, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg N) hlogPos.le)]
  nlinarith

/-- Uniform finite upper bound for the extremal function itself. -/
theorem g_le_primeCounting_add_sqrt_add_finiteError
    {N : ℕ} (hN : 1 ≤ N) :
    g N ≤ Nat.primeCounting N + Nat.primeCounting (Nat.sqrt N) +
      finiteError N := by
  obtain ⟨A, hAN, hA, hAg⟩ := exists_extremal N
  have hbound := card_le_primeCounting_add_sqrt_add_finiteError hN hAN hA
  omega

/-- The signed excess over the prime/prime-square construction is little-o
of `sqrt N / log N`.  Together with `baseline_le_g`, this pins the excess
between zero and the explicit remainder above. -/
theorem erdos_795_signed_error_isLittleO :
    (fun N : ℕ ↦ (g N : ℝ) - Nat.primeCounting N -
      Nat.primeCounting (Nat.sqrt N)) =o[atTop]
        (fun N : ℕ ↦ Real.sqrt N / Real.log N) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hfinite := (Asymptotics.isLittleO_iff.mp finiteError_isLittleO) hε
  have hlogTendsto : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hfinite, eventually_ge_atTop (1 : ℕ),
    hlogTendsto.eventually (eventually_ge_atTop (0 : ℝ))] with
      N hfinite hN hlog
  have hlower := baseline_le_g N
  have hupper := g_le_primeCounting_add_sqrt_add_finiteError hN
  have hlowerR' : (Nat.primeCounting N : ℝ) +
      Nat.primeCounting (Nat.sqrt N) ≤ (g N : ℝ) := by
    exact_mod_cast hlower
  have hupperR' : (g N : ℝ) ≤ (Nat.primeCounting N : ℝ) +
      Nat.primeCounting (Nat.sqrt N) + finiteError N := by
    exact_mod_cast hupper
  have hlowerR : (0 : ℝ) ≤ (g N : ℝ) - Nat.primeCounting N -
      Nat.primeCounting (Nat.sqrt N) := by linarith
  have hupperR : (g N : ℝ) - Nat.primeCounting N -
      Nat.primeCounting (Nat.sqrt N) ≤ finiteError N := by linarith
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg N) hlog)] at hfinite ⊢
  exact hupperR.trans hfinite

/-- **Resolution of Erdős Problem 795.**  For every positive error
coefficient, the conjectured upper bound holds for all sufficiently large
`N`.  This is the precise quantifier form of
`g(N) ≤ π(N) + π(√N) + o(√N / log N)`. -/
theorem erdos_795 :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (g N : ℝ) ≤ Nat.primeCounting N +
        Nat.primeCounting (Nat.sqrt N) +
          ε * (Real.sqrt N / Real.log N) := by
  intro ε hε
  have hsmall :=
    (Asymptotics.isLittleO_iff.mp erdos_795_signed_error_isLittleO) hε
  have hlogTendsto : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall,
    hlogTendsto.eventually (eventually_ge_atTop (0 : ℝ))] with
      N hsmall hlog
  have hexcess : (0 : ℝ) ≤ (g N : ℝ) - Nat.primeCounting N -
      Nat.primeCounting (Nat.sqrt N) := by
    have hbase : (Nat.primeCounting N : ℝ) +
        Nat.primeCounting (Nat.sqrt N) ≤ (g N : ℝ) := by
      exact_mod_cast baseline_le_g N
    linarith
  rw [Real.norm_of_nonneg hexcess,
    Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg N) hlog)] at hsmall
  linarith

end

end Erdos795

#print axioms Erdos795.erdos_795
