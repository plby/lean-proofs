/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.SubpowerComparable
import Mathlib.NumberTheory.Divisors

/-!
# Reciprocal-energy arithmetic

The high-moment argument for the convenient-factorization error separates
the diagonal solutions of an equality between two sums of reciprocals.  Once
denominators are cleared, every prime in the total product must occur in at
least two coordinates.  This file proves that exact finite statement.
-/

namespace Erdos387

open scoped BigOperators

/-- Every prime divisor occurs with multiplicity at least two. -/
def IsSquarefull (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

section FiniteReciprocalNumerator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The numerator obtained from `∑ i ∈ A, 1 / s i` after multiplying by the
full product of the denominators. -/
def reciprocalNumerator (A : Finset ι) (s : ι → ℕ) : ℕ :=
  ∑ i ∈ A, ∏ j ∈ (Finset.univ : Finset ι).erase i, s j

/-- The rational reciprocal sum whose cleared numerator is
`reciprocalNumerator`. -/
def reciprocalSum (A : Finset ι) (s : ι → ℕ) : ℚ :=
  ∑ i ∈ A, (s i : ℚ)⁻¹

theorem product_mul_inv_eq_erased_product
    (s : ι → ℕ) {i : ι} (hi : 0 < s i) :
    ((∏ j : ι, s j : ℕ) : ℚ) * (s i : ℚ)⁻¹ =
      ((∏ j ∈ (Finset.univ : Finset ι).erase i, s j : ℕ) : ℚ) := by
  have hprod : (∏ j : ι, s j) =
      s i * ∏ j ∈ (Finset.univ : Finset ι).erase i, s j := by
    exact (Finset.mul_prod_erase (Finset.univ : Finset ι) s
      (Finset.mem_univ i)).symm
  rw [hprod]
  push_cast
  field_simp

/-- Clearing the common product of positive denominators gives exactly the
natural-number numerator above. -/
theorem product_mul_reciprocalSum_eq
    (A : Finset ι) (s : ι → ℕ) (hpos : ∀ i, 0 < s i) :
    ((∏ j : ι, s j : ℕ) : ℚ) * reciprocalSum A s =
      (reciprocalNumerator A s : ℕ) := by
  simp_rw [reciprocalSum, Finset.mul_sum]
  unfold reciprocalNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simpa using product_mul_inv_eq_erased_product s (hpos i)

/-- Equality of two reciprocal sums over complementary index sets implies
the integral cleared-numerator identity used by the squarefull argument. -/
theorem reciprocalNumerator_eq_of_reciprocalSum_eq
    (A : Finset ι) (s : ι → ℕ) (hpos : ∀ i, 0 < s i)
    (hbalance : reciprocalSum A s =
      reciprocalSum ((Finset.univ : Finset ι) \ A) s) :
    reciprocalNumerator A s =
      reciprocalNumerator ((Finset.univ : Finset ι) \ A) s := by
  have hmul := congrArg
    (fun x : ℚ => ((∏ j : ι, s j : ℕ) : ℚ) * x) hbalance
  rw [product_mul_reciprocalSum_eq A s hpos,
    product_mul_reciprocalSum_eq ((Finset.univ : Finset ι) \ A) s hpos] at hmul
  exact_mod_cast hmul

theorem prime_dvd_all_erased_products_except
    (s : ι → ℕ) {p : ℕ} (_hp : p.Prime) {i j : ι}
    (hpi : p ∣ s i) (hji : j ≠ i) :
    p ∣ ∏ t ∈ (Finset.univ : Finset ι).erase j, s t := by
  exact hpi.trans (Finset.dvd_prod_of_mem s
    (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩))

theorem prime_dvd_reciprocalNumerator_erase
    (A : Finset ι) (s : ι → ℕ) {p : ℕ} (hp : p.Prime) {i : ι}
    (hpi : p ∣ s i) :
    p ∣ reciprocalNumerator (A.erase i) s := by
  unfold reciprocalNumerator
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_erase] at hj
  exact prime_dvd_all_erased_products_except s hp hpi hj.1

theorem prime_dvd_reciprocalNumerator_of_not_mem
    (A : Finset ι) (s : ι → ℕ) {p : ℕ} (hp : p.Prime) {i : ι}
    (hpi : p ∣ s i) (hiA : i ∉ A) :
    p ∣ reciprocalNumerator A s := by
  unfold reciprocalNumerator
  apply Finset.dvd_sum
  intro j hj
  exact prime_dvd_all_erased_products_except s hp hpi (by
    intro hji
    subst j
    exact hiA hj)

theorem reciprocalNumerator_insert_erase
    (A : Finset ι) (s : ι → ℕ) {i : ι} (hiA : i ∈ A) :
    reciprocalNumerator A s =
      (∏ j ∈ (Finset.univ : Finset ι).erase i, s j) +
        reciprocalNumerator (A.erase i) s := by
  rw [show A = insert i (A.erase i) by
    exact (Finset.insert_erase hiA).symm]
  simp [reciprocalNumerator]

/-- If clearing denominators makes the reciprocal sums over `A` and its
complement equal, no prime can occur in exactly one denominator. -/
theorem exists_second_dvd_of_reciprocalNumerator_eq
    (A : Finset ι) (s : ι → ℕ)
    (hbalance : reciprocalNumerator A s =
      reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)
    {p : ℕ} (hp : p.Prime) {i : ι} (hpi : p ∣ s i) :
    ∃ j : ι, j ≠ i ∧ p ∣ s j := by
  by_contra hno
  push Not at hno
  have hnotErase : ¬p ∣
      ∏ j ∈ (Finset.univ : Finset ι).erase i, s j := by
    apply hp.prime.not_dvd_finsetProd
    intro j hj
    rw [Finset.mem_erase] at hj
    exact hno j hj.1
  by_cases hiA : i ∈ A
  · have hleftRest := prime_dvd_reciprocalNumerator_erase A s hp hpi
    have hiComp : i ∉ (Finset.univ : Finset ι) \ A := by simp [hiA]
    have hright := prime_dvd_reciprocalNumerator_of_not_mem
      ((Finset.univ : Finset ι) \ A) s hp hpi hiComp
    have hsum : p ∣
        (∏ j ∈ (Finset.univ : Finset ι).erase i, s j) +
          reciprocalNumerator (A.erase i) s := by
      rw [← reciprocalNumerator_insert_erase A s hiA, hbalance]
      exact hright
    exact hnotErase ((Nat.dvd_add_left hleftRest).mp hsum)
  · have hrightMem : i ∈ (Finset.univ : Finset ι) \ A := by simp [hiA]
    have hrightRest := prime_dvd_reciprocalNumerator_erase
      ((Finset.univ : Finset ι) \ A) s hp hpi
    have hleft := prime_dvd_reciprocalNumerator_of_not_mem A s hp hpi hiA
    have hsum : p ∣
        (∏ j ∈ (Finset.univ : Finset ι).erase i, s j) +
          reciprocalNumerator (((Finset.univ : Finset ι) \ A).erase i) s := by
      rw [← reciprocalNumerator_insert_erase
        ((Finset.univ : Finset ι) \ A) s hrightMem, ← hbalance]
      exact hleft
    exact hnotErase ((Nat.dvd_add_left hrightRest).mp hsum)

theorem prime_sq_dvd_univ_prod_of_two
    (s : ι → ℕ) {p : ℕ} {i j : ι} (hij : i ≠ j)
    (hpi : p ∣ s i) (hpj : p ∣ s j) :
    p ^ 2 ∣ ∏ t : ι, s t := by
  let T : Finset ι := (Finset.univ.erase i).erase j
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset ι).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hprod : (∏ t : ι, s t) = s i * s j * ∏ t ∈ T, s t := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ι) s hi]
    rw [← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase i) s hj]
    dsimp [T]
    ring
  rw [hprod]
  simpa [pow_two] using
    dvd_mul_of_dvd_left (Nat.mul_dvd_mul hpi hpj) (∏ t ∈ T, s t)

/-- Exact squarefull-support lemma underlying BNPZ Lemma 9.1. -/
theorem isSquarefull_prod_of_reciprocalNumerator_eq
    (A : Finset ι) (s : ι → ℕ)
    (hbalance : reciprocalNumerator A s =
      reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) :
    IsSquarefull (∏ i : ι, s i) := by
  intro p hp hpProd
  obtain ⟨i, _hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff s).mp hpProd
  obtain ⟨j, hji, hpj⟩ :=
    exists_second_dvd_of_reciprocalNumerator_eq A s hbalance hp hpi
  exact prime_sq_dvd_univ_prod_of_two s hji.symm hpi hpj

/-- Rational form of the squarefull-support lemma: a positive tuple solving
an equality of complementary reciprocal sums has squarefull total product. -/
theorem isSquarefull_prod_of_reciprocalSum_eq
    (A : Finset ι) (s : ι → ℕ) (hpos : ∀ i, 0 < s i)
    (hbalance : reciprocalSum A s =
      reciprocalSum ((Finset.univ : Finset ι) \ A) s) :
    IsSquarefull (∏ i : ι, s i) := by
  exact isSquarefull_prod_of_reciprocalNumerator_eq A s
    (reciprocalNumerator_eq_of_reciprocalSum_eq A s hpos hbalance)

section FiniteEnergy

/-- Tuples drawn from `U` which solve the complementary reciprocal-sum
equation associated to `A`. -/
noncomputable def reciprocalEnergyTuples
    (A : Finset ι) (U : Finset ℕ) : Finset (ι → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : ι => U).filter fun s =>
    reciprocalSum A s = reciprocalSum ((Finset.univ : Finset ι) \ A) s

/-- The finite range of positive squarefull products up to `T ^ m`. -/
noncomputable def squarefullProductRange (T m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (T ^ m)).filter IsSquarefull

theorem reciprocalEnergyTuple_coordinate_mem
    {A : Finset ι} {U : Finset ℕ} {s : ι → ℕ}
    (hs : s ∈ reciprocalEnergyTuples A U) (i : ι) :
    s i ∈ U := by
  classical
  rw [reciprocalEnergyTuples, Finset.mem_filter] at hs
  exact Fintype.mem_piFinset.mp hs.1 i

theorem reciprocalEnergyTuple_balance
    {A : Finset ι} {U : Finset ℕ} {s : ι → ℕ}
    (hs : s ∈ reciprocalEnergyTuples A U) :
    reciprocalSum A s = reciprocalSum ((Finset.univ : Finset ι) \ A) s := by
  classical
  rw [reciprocalEnergyTuples, Finset.mem_filter] at hs
  exact hs.2

theorem reciprocalEnergyTuple_product_pos
    {A : Finset ι} {U : Finset ℕ}
    (hUpos : ∀ u ∈ U, 0 < u) {s : ι → ℕ}
    (hs : s ∈ reciprocalEnergyTuples A U) :
    0 < ∏ i : ι, s i := by
  apply Finset.prod_pos
  intro i hi
  exact hUpos (s i) (reciprocalEnergyTuple_coordinate_mem hs i)

theorem reciprocalEnergyTuple_product_le
    {A : Finset ι} {U : Finset ℕ} {T : ℕ}
    (hUle : ∀ u ∈ U, u ≤ T) {s : ι → ℕ}
    (hs : s ∈ reciprocalEnergyTuples A U) :
    (∏ i : ι, s i) ≤ T ^ Fintype.card ι := by
  calc
    (∏ i : ι, s i) ≤ ∏ _i : ι, T := by
      apply Finset.prod_le_prod
      · intro i hi
        omega
      · intro i hi
        exact hUle (s i) (reciprocalEnergyTuple_coordinate_mem hs i)
    _ = T ^ Fintype.card ι := by simp

theorem reciprocalEnergyTuple_product_squarefull
    {A : Finset ι} {U : Finset ℕ}
    (hUpos : ∀ u ∈ U, 0 < u) {s : ι → ℕ}
    (hs : s ∈ reciprocalEnergyTuples A U) :
    IsSquarefull (∏ i : ι, s i) := by
  apply isSquarefull_prod_of_reciprocalSum_eq A s
  · intro i
    exact hUpos (s i) (reciprocalEnergyTuple_coordinate_mem hs i)
  · exact reciprocalEnergyTuple_balance hs

theorem reciprocalEnergyTuple_product_mem_squarefullRange
    {A : Finset ι} {U : Finset ℕ} {T : ℕ}
    (hUpos : ∀ u ∈ U, 0 < u) (hUle : ∀ u ∈ U, u ≤ T)
    {s : ι → ℕ} (hs : s ∈ reciprocalEnergyTuples A U) :
    (∏ i : ι, s i) ∈ squarefullProductRange T (Fintype.card ι) := by
  classical
  rw [squarefullProductRange, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨reciprocalEnergyTuple_product_pos hUpos hs,
    reciprocalEnergyTuple_product_le hUle hs⟩,
    reciprocalEnergyTuple_product_squarefull hUpos hs⟩

/-- A tuple in a fixed nonzero product fibre lies in the Cartesian power of
the divisor set of that product. -/
theorem reciprocalEnergy_productFiber_subset_divisorBox
    (A : Finset ι) (U : Finset ℕ) {N : ℕ} (hN : N ≠ 0) :
    (reciprocalEnergyTuples A U).filter
        (fun s => (∏ i : ι, s i) = N) ⊆
      Fintype.piFinset (fun _ : ι => N.divisors) := by
  classical
  intro s hs
  rw [Finset.mem_filter] at hs
  rw [Fintype.mem_piFinset]
  intro i
  rw [Nat.mem_divisors]
  refine ⟨?_, hN⟩
  rw [← hs.2]
  exact Finset.dvd_prod_of_mem s (Finset.mem_univ i)

theorem reciprocalEnergy_productFiber_card_le
    (A : Finset ι) (U : Finset ℕ) {N : ℕ} (hN : N ≠ 0) :
    ((reciprocalEnergyTuples A U).filter
        (fun s => (∏ i : ι, s i) = N)).card ≤
      N.divisors.card ^ Fintype.card ι := by
  classical
  calc
    ((reciprocalEnergyTuples A U).filter
        (fun s => (∏ i : ι, s i) = N)).card ≤
        (Fintype.piFinset (fun _ : ι => N.divisors)).card :=
      Finset.card_le_card
        (reciprocalEnergy_productFiber_subset_divisorBox A U hN)
    _ = N.divisors.card ^ Fintype.card ι := by
      simp

/-- Exact finite squarefull-product majorant for reciprocal energy.  This is
the combinatorial reduction at the start of BNPZ Lemma 9.1; the remaining
analytic step is to estimate the displayed squarefull divisor sum. -/
theorem reciprocalEnergyTuples_card_le_squarefull_divisorSum
    (A : Finset ι) (U : Finset ℕ) (T : ℕ)
    (hUpos : ∀ u ∈ U, 0 < u) (hUle : ∀ u ∈ U, u ≤ T) :
    (reciprocalEnergyTuples A U).card ≤
      ∑ N ∈ squarefullProductRange T (Fintype.card ι),
        N.divisors.card ^ Fintype.card ι := by
  classical
  let P : (ι → ℕ) → ℕ := fun s => ∏ i : ι, s i
  have hmap :
      ((reciprocalEnergyTuples A U : Finset (ι → ℕ)) : Set (ι → ℕ)).MapsTo
        P (squarefullProductRange T (Fintype.card ι) : Set ℕ) := by
    intro s hs
    exact reciprocalEnergyTuple_product_mem_squarefullRange hUpos hUle hs
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_le_sum
  intro N hN
  have hNpos : 0 < N := by
    rw [squarefullProductRange, Finset.mem_filter, Finset.mem_Icc] at hN
    exact hN.1.1
  simpa [P] using reciprocalEnergy_productFiber_card_le A U hNpos.ne'

end FiniteEnergy

end FiniteReciprocalNumerator

end Erdos387
