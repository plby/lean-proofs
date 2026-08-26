import ErdosProblems.Erdos67b.MRT
import ErdosProblems.Erdos67b.PrimeEstimates
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import Mathlib.Data.Nat.Totient

/-!
# Density of the typical-factorisation set

This file contains the finite counting layer in the Matomäki--Radziwiłł--Tao
typical-factorisation argument.  It separates the elementary reduction from the analytic
sieve estimate: an integer is atypical exactly when it misses one of the selected prime
blocks, hence the atypical set is a finite union of sifted sets.  For one block we also identify
the sifted set with integers coprime to the product of the primes in that block and give the
standard complete-period upper bound in terms of Euler's totient.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

/-! ## Missing blocks and the finite union bound -/

/-- Integers in `[1,X]` having no prime factor in the block `I`. -/
noncomputable def missingPrimeBlockSet (I : ℕ × ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n ↦ ¬HasPrimeFactorInBlock I n

@[simp]
theorem mem_missingPrimeBlockSet {I : ℕ × ℕ} {X n : ℕ} :
    n ∈ missingPrimeBlockSet I X ↔
      1 ≤ n ∧ n ≤ X ∧ ¬HasPrimeFactorInBlock I n := by
  simp [missingPrimeBlockSet, and_assoc]

/-- The complement of the typical-factorisation set inside `[1,X]`. -/
noncomputable def atypicalFactorizationSet
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n ↦ ¬HasTypicalFactorization blocks n

@[simp]
theorem mem_atypicalFactorizationSet {blocks : Finset (ℕ × ℕ)} {X n : ℕ} :
    n ∈ atypicalFactorizationSet blocks X ↔
      1 ≤ n ∧ n ≤ X ∧ ¬HasTypicalFactorization blocks n := by
  simp [atypicalFactorizationSet, and_assoc]

/-- An integer is atypical iff it belongs to the missing set for at least one block. -/
theorem atypicalFactorizationSet_eq_biUnion
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) :
    atypicalFactorizationSet blocks X =
      blocks.biUnion fun I ↦ missingPrimeBlockSet I X := by
  classical
  ext n
  simp only [atypicalFactorizationSet, missingPrimeBlockSet, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_biUnion, HasTypicalFactorization, not_forall,
    Prod.exists]
  aesop

/-- Finite union bound for the integers missing at least one prime block. -/
theorem card_atypicalFactorizationSet_le_sum_card_missing
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) :
    #(atypicalFactorizationSet blocks X) ≤
      ∑ I ∈ blocks, #(missingPrimeBlockSet I X) := by
  classical
  rw [atypicalFactorizationSet_eq_biUnion]
  exact Finset.card_biUnion_le

/-- A uniform missing-block bound implies the usual cardinality union bound. -/
theorem card_atypicalFactorizationSet_le_card_mul
    {blocks : Finset (ℕ × ℕ)} {X E : ℕ}
    (hE : ∀ I ∈ blocks, #(missingPrimeBlockSet I X) ≤ E) :
    #(atypicalFactorizationSet blocks X) ≤ #blocks * E := by
  calc
    #(atypicalFactorizationSet blocks X) ≤
        ∑ I ∈ blocks, #(missingPrimeBlockSet I X) :=
      card_atypicalFactorizationSet_le_sum_card_missing blocks X
    _ ≤ ∑ _I ∈ blocks, E := Finset.sum_le_sum fun I hI ↦ hE I hI
    _ = #blocks * E := by simp

/-- The typical and atypical subsets partition `[1,X]`. -/
theorem typical_card_add_atypical_card (blocks : Finset (ℕ × ℕ)) (X : ℕ) :
    #(typicalFactorizationSet blocks X) + #(atypicalFactorizationSet blocks X) = X := by
  classical
  simpa [typicalFactorizationSet, atypicalFactorizationSet] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.Icc 1 X) (p := HasTypicalFactorization blocks))

/-- Subtracting the union bound gives a lower bound for the typical set. -/
theorem card_mul_sub_le_card_typical
    {blocks : Finset (ℕ × ℕ)} {X E : ℕ}
    (hE : ∀ I ∈ blocks, #(missingPrimeBlockSet I X) ≤ E) :
    X - #blocks * E ≤ #(typicalFactorizationSet blocks X) := by
  have hbad := card_atypicalFactorizationSet_le_card_mul hE
  have hpartition := typical_card_add_atypical_card blocks X
  omega

/-- Non-uniform form of the density reduction: each block may have its own error bound. -/
theorem sub_sum_le_card_typical
    {blocks : Finset (ℕ × ℕ)} {X : ℕ} {E : ℕ × ℕ → ℕ}
    (hE : ∀ I ∈ blocks, #(missingPrimeBlockSet I X) ≤ E I) :
    X - ∑ I ∈ blocks, E I ≤ #(typicalFactorizationSet blocks X) := by
  have hbad : #(atypicalFactorizationSet blocks X) ≤ ∑ I ∈ blocks, E I :=
    (card_atypicalFactorizationSet_le_sum_card_missing blocks X).trans
      (Finset.sum_le_sum fun I hI ↦ hE I hI)
  have hpartition := typical_card_add_atypical_card blocks X
  omega

/-! ## A missing block as a sifted set -/

/-- Product of all primes in a selected block. -/
def primeBlockProduct (I : ℕ × ℕ) : ℕ :=
  ∏ p ∈ primesInBlock I, p

theorem primeBlockProduct_pos (I : ℕ × ℕ) : 0 < primeBlockProduct I := by
  unfold primeBlockProduct
  exact Finset.prod_pos fun p hp ↦ (mem_primesInBlock.mp hp).1.pos

theorem primeBlockProduct_ne_zero (I : ℕ × ℕ) : primeBlockProduct I ≠ 0 :=
  (primeBlockProduct_pos I).ne'

/-- The product of the distinct primes in a block is squarefree. -/
theorem primeBlockProduct_squarefree (I : ℕ × ℕ) :
    Squarefree (primeBlockProduct I) := by
  unfold primeBlockProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (mem_primesInBlock.mp hp).1
        (mem_primesInBlock.mp hq).1).mpr hpq)
  · intro p hp
    exact (mem_primesInBlock.mp hp).1.squarefree

/-- Missing every prime in a block is equivalent to coprimality with their product. -/
theorem not_hasPrimeFactorInBlock_iff_coprime_primeBlockProduct
    (I : ℕ × ℕ) (n : ℕ) :
    ¬HasPrimeFactorInBlock I n ↔ (primeBlockProduct I).Coprime n := by
  classical
  rw [primeBlockProduct, Nat.coprime_prod_left_iff]
  simp only [HasPrimeFactorInBlock, not_exists, not_and]
  constructor
  · intro h p hp
    exact (mem_primesInBlock.mp hp).1.coprime_iff_not_dvd.mpr (h p hp)
  · intro h p hp
    exact (mem_primesInBlock.mp hp).1.coprime_iff_not_dvd.mp (h p hp)

theorem missingPrimeBlockSet_eq_filter_coprime (I : ℕ × ℕ) (X : ℕ) :
    missingPrimeBlockSet I X =
      (Finset.Icc 1 X).filter fun n ↦ (primeBlockProduct I).Coprime n := by
  classical
  ext n
  simp [missingPrimeBlockSet,
    not_hasPrimeFactorInBlock_iff_coprime_primeBlockProduct]

/-- Complete-period bound for a single missing block.  This is the elementary interval-support
bridge needed before inserting a Selberg/Mertens estimate for the totient ratio. -/
theorem card_missingPrimeBlockSet_le_totient_mul
    (I : ℕ × ℕ) (X : ℕ) :
    #(missingPrimeBlockSet I X) ≤
      Nat.totient (primeBlockProduct I) * (X / primeBlockProduct I + 1) := by
  rw [missingPrimeBlockSet_eq_filter_coprime, ← Finset.Ico_add_one_right_eq_Icc]
  simpa [Nat.add_comm] using
    Nat.Ico_filter_coprime_le 1 X (primeBlockProduct_ne_zero I)

/-- The totient of a prime-block product is exactly the product of `p-1`. -/
theorem totient_primeBlockProduct (I : ℕ × ℕ) :
    Nat.totient (primeBlockProduct I) =
      ∏ p ∈ primesInBlock I, (p - 1) := by
  unfold primeBlockProduct
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.primeFactors_prod (fun p hp ↦ (mem_primesInBlock.mp hp).1)]
  have hpos : 0 < ∏ p ∈ primesInBlock I, p :=
    Finset.prod_pos fun p hp ↦ (mem_primesInBlock.mp hp).1.pos
  rw [Nat.div_self hpos, one_mul]

/-- Rational Euler-product form of the block density. -/
theorem totient_primeBlockProduct_cast (I : ℕ × ℕ) :
    (Nat.totient (primeBlockProduct I) : ℚ) =
      primeBlockProduct I *
        ∏ p ∈ primesInBlock I, (1 - (p : ℚ)⁻¹) := by
  unfold primeBlockProduct
  rw [Nat.totient_eq_mul_prod_factors,
    Nat.primeFactors_prod (fun p hp ↦ (mem_primesInBlock.mp hp).1)]

/-- The real Euler product giving the density of integers coprime to the block product. -/
def primeBlockDensity (I : ℕ × ℕ) : ℝ :=
  ∏ p ∈ primesInBlock I, (1 - (p : ℝ)⁻¹)

theorem primeBlockDensity_nonneg (I : ℕ × ℕ) : 0 ≤ primeBlockDensity I := by
  unfold primeBlockDensity
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primesInBlock.mp hp).1.one_le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  rw [sub_nonneg, inv_le_one₀ hp0]
  exact hp1

theorem primeBlockDensity_le_one (I : ℕ × ℕ) : primeBlockDensity I ≤ 1 := by
  unfold primeBlockDensity
  apply Finset.prod_le_one
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primesInBlock.mp hp).1.one_le
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
    rw [sub_nonneg, inv_le_one₀ hp0]
    exact hp1
  · intro p hp
    exact sub_le_self 1 (inv_nonneg.mpr (show (0 : ℝ) ≤ (p : ℝ) by positivity))

/-- The elementary exponential upper bound for a prime-block density.  Writing the closed
natural interval `[L,U]` as the half-open interval `(L-1,U]` aligns this exactly with the
reciprocal-prime interval used by `PrimeEstimates`. -/
theorem primeBlockDensity_le_exp_neg_reciprocalPrimeInterval
    {L U : ℕ} (hL : 0 < L) :
    primeBlockDensity (L, U) ≤
      Real.exp (-PrimeEstimates.reciprocalPrimeInterval (L - 1) U) := by
  have hsets : primesInBlock (L, U) =
      PrimeEstimates.primesInInterval (L - 1) U := by
    ext p
    simp only [mem_primesInBlock, PrimeEstimates.mem_primesInInterval]
    constructor
    · rintro ⟨hp, hLp, hpU⟩
      exact ⟨by omega, hpU, hp⟩
    · rintro ⟨hLmp, hpU, hp⟩
      exact ⟨hp, by omega, hpU⟩
  unfold primeBlockDensity PrimeEstimates.reciprocalPrimeInterval
  rw [hsets, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hpPrime := (PrimeEstimates.mem_primesInInterval.mp hp).2.2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
    exact sub_nonneg.mpr (inv_le_one₀ (by positivity) |>.mpr hp1)
  · intro p hp
    have h := Real.add_one_le_exp (-(p : ℝ)⁻¹)
    simpa [sub_eq_add_neg, add_comm] using h

/-- Mertens' reciprocal-prime theorem gives the matching lower bound for one block. -/
theorem reciprocalPrimeInterval_log_log_lower
    {L U : ℕ} (hL : 3 ≤ L) (hLU : L ≤ U) :
    Real.log (Real.log (U : ℝ)) -
          Real.log (Real.log ((L - 1 : ℕ) : ℝ)) -
        2 * PrimeEstimates.mertensBound ≤
      PrimeEstimates.reciprocalPrimeInterval (L - 1) U := by
  have hLm : 2 ≤ L - 1 := by omega
  have hLmU : L - 1 ≤ U := by omega
  rw [PrimeEstimates.reciprocalPrimeInterval_eq_sub hLmU]
  have hU : 2 ≤ U := by omega
  have hu := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hU
  have hl := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hLm
  rw [abs_le] at hu hl
  linarith

/-- A source-sized Mertens bound for the density of integers missing a full prime block:
up to one absolute constant it is `log (L-1) / log U`. -/
theorem primeBlockDensity_le_mertensRatio
    {L U : ℕ} (hL : 3 ≤ L) (hLU : L ≤ U) :
    primeBlockDensity (L, U) ≤
        Real.exp (2 * PrimeEstimates.mertensBound) *
          (Real.log ((L - 1 : ℕ) : ℝ) / Real.log (U : ℝ)) := by
  have hLpos : 0 < L := by omega
  have hLm : 2 ≤ L - 1 := by omega
  have hU : 2 ≤ U := by omega
  have hlogLm : 0 < Real.log ((L - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L - 1 by omega))
  have hlogU : 0 < Real.log (U : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  calc
    primeBlockDensity (L, U) ≤
        Real.exp (-PrimeEstimates.reciprocalPrimeInterval (L - 1) U) :=
      primeBlockDensity_le_exp_neg_reciprocalPrimeInterval hLpos
    _ ≤ Real.exp (-(Real.log (Real.log (U : ℝ)) -
          Real.log (Real.log ((L - 1 : ℕ) : ℝ)) -
            2 * PrimeEstimates.mertensBound)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (reciprocalPrimeInterval_log_log_lower hL hLU)
    _ = Real.exp (2 * PrimeEstimates.mertensBound) *
          (Real.log ((L - 1 : ℕ) : ℝ) / Real.log (U : ℝ)) := by
      rw [show -(Real.log (Real.log (U : ℝ)) -
            Real.log (Real.log ((L - 1 : ℕ) : ℝ)) -
              2 * PrimeEstimates.mertensBound) =
          2 * PrimeEstimates.mertensBound +
            (Real.log (Real.log ((L - 1 : ℕ) : ℝ)) -
              Real.log (Real.log (U : ℝ))) by ring,
        Real.exp_add, Real.exp_sub, Real.exp_log hlogLm, Real.exp_log hlogU]

/-! ## Transfer of the concrete beta sieve -/

/-- The strict prime window used by the concrete beta sieve agrees with the closed block after
shifting both endpoints by one. -/
theorem erdos387_sievePrimes_pred_succ_eq_primesInBlock
    {L U : ℕ} (hL : 0 < L) :
    Erdos387.sievePrimes (L - 1) (U + 1) = primesInBlock (L, U) := by
  ext p
  rw [Erdos387.mem_sievePrimes, mem_primesInBlock]
  constructor
  · rintro ⟨hp, hpL, hpU⟩
    exact ⟨hp, by omega, by omega⟩
  · rintro ⟨hp, hpL, hpU⟩
    exact ⟨hp, by omega, by omega⟩

theorem sievePrimeProduct_pred_succ_eq_primeBlockProduct
    {L U : ℕ} (hL : 0 < L) :
    Erdos387.sievePrimeProduct (L - 1) (U + 1) = primeBlockProduct (L, U) := by
  unfold Erdos387.sievePrimeProduct primeBlockProduct
  rw [erdos387_sievePrimes_pred_succ_eq_primesInBlock hL]

theorem erdos851_sievePrimes_pred_eq_primesInBlock
    {L U : ℕ} (hL : 0 < L) :
    Erdos851.sievePrimes (L - 1) U = primesInBlock (L, U) := by
  ext p
  rw [Erdos851.mem_sievePrimes, mem_primesInBlock]
  constructor
  · rintro ⟨hpL, hpU, hp⟩
    exact ⟨hp, by omega, hpU⟩
  · rintro ⟨hp, hpL, hpU⟩
    exact ⟨by omega, hpU, hp⟩

/-- The beta-sieve dimension-one Euler product is the block density already used above. -/
theorem oneShift_localEulerProduct_pred_eq_primeBlockDensity
    {L U : ℕ} (hL : 0 < L) :
    Erdos851.localEulerProduct Erdos851.oneShiftDensity (L - 1) U =
      primeBlockDensity (L, U) := by
  unfold Erdos851.localEulerProduct Erdos851.oneShiftDensity primeBlockDensity
  rw [erdos851_sievePrimes_pred_eq_primesInBlock hL]

/-- Translating `[1,X]` by `X` identifies a missing block with the singleton-shift sifted
candidate set on `(X,2X]`. -/
theorem siftedShiftCandidates_singleton_eq_image_missingPrimeBlockSet
    {L U X : ℕ} (hL : 0 < L) :
    Erdos851.ShiftSieve.siftedShiftCandidates {X} X (L - 1) (U + 1) =
      (missingPrimeBlockSet (L, U) X).image fun n ↦ X + n := by
  classical
  ext a
  rw [Erdos851.ShiftSieve.siftedShiftCandidates,
    sievePrimeProduct_pred_succ_eq_primeBlockProduct hL]
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image,
    mem_missingPrimeBlockSet, Erdos851.ShiftSieve.shiftedProduct,
    Finset.prod_singleton]
  constructor
  · rintro ⟨⟨haX, ha2X⟩, hcop⟩
    refine ⟨a - X, ⟨by omega, by omega, ?_⟩, by omega⟩
    rw [not_hasPrimeFactorInBlock_iff_coprime_primeBlockProduct]
    exact hcop
  · rintro ⟨n, ⟨hn1, hnX, hnmiss⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rwa [← not_hasPrimeFactorInBlock_iff_coprime_primeBlockProduct]

theorem card_siftedShiftCandidates_singleton_eq_card_missingPrimeBlockSet
    {L U X : ℕ} (hL : 0 < L) :
    #(Erdos851.ShiftSieve.siftedShiftCandidates {X} X (L - 1) (U + 1)) =
      #(missingPrimeBlockSet (L, U) X) := by
  rw [siftedShiftCandidates_singleton_eq_image_missingPrimeBlockSet hL,
    Finset.card_image_of_injective]
  exact fun a b hab ↦ Nat.add_left_cancel hab

/-- The concrete dimension-one beta sieve, transferred from a singleton shifted interval to
integers in `[1,X]` missing a prime in `[L,U]`.  Unlike the complete-period estimate below,
its endpoint error is the freely chosen sieve level `(U^S)^2`. -/
theorem exists_card_missingPrimeBlockSet_beta_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ X L U S : ℕ, 3 ≤ L → L ≤ U → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (#(missingPrimeBlockSet (L, U) X) : ℝ) ≤
          (X : ℝ) * ((1 + eta) * primeBlockDensity (L, U)) +
            ((U ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbeta⟩ := Erdos851.exists_oneShift_concrete_cardinality_bounds
  refine ⟨A, hA, ?_⟩
  intro X L U S hL hLU hS hlog
  dsimp only
  have hb := hbeta X X (L - 1) U S (le_refl X) (by omega) (by omega)
    (by omega) hS hlog
  dsimp only at hb
  rw [card_siftedShiftCandidates_singleton_eq_card_missingPrimeBlockSet (by omega),
    oneShift_localEulerProduct_pred_eq_primeBlockDensity (by omega)] at hb
  exact hb.2

/-- Fully explicit beta-sieve/Mertens bound for one missing block.  The main term has the
source-level logarithmic ratio, while the power term is the finite sieve remainder that must
be made negligible by the choice of `S` and `U`. -/
theorem exists_card_missingPrimeBlockSet_mertens_beta_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ X L U S : ℕ, 3 ≤ L → L ≤ U → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (#(missingPrimeBlockSet (L, U) X) : ℝ) ≤
          (X : ℝ) * ((1 + eta) *
            (Real.exp (2 * PrimeEstimates.mertensBound) *
              (Real.log ((L - 1 : ℕ) : ℝ) / Real.log (U : ℝ)))) +
            ((U ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbeta⟩ := exists_card_missingPrimeBlockSet_beta_bound
  refine ⟨A, hA, ?_⟩
  intro X L U S hL hLU hS hlog
  dsimp only
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have heta : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by positivity
  calc
    (#(missingPrimeBlockSet (L, U) X) : ℝ) ≤
        (X : ℝ) * ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          primeBlockDensity (L, U)) + ((U ^ S : ℕ) : ℝ) ^ 2 :=
      hbeta X L U S hL hLU hS hlog
    _ ≤ (X : ℝ) * ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (Real.exp (2 * PrimeEstimates.mertensBound) *
            (Real.log ((L - 1 : ℕ) : ℝ) / Real.log (U : ℝ)))) +
          ((U ^ S : ℕ) : ℝ) ^ 2 := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left
          (primeBlockDensity_le_mertensRatio hL hLU) (add_nonneg zero_le_one heta)
      · positivity

/-- The unconditional finite exceptional-set estimate obtained by summing the concrete
beta-sieve bound over all prime blocks.  This is the cardinality input used in the
typical-factorisation reduction: the first sum is the Mertens density contribution and the
second is the fully explicit beta-sieve remainder. -/
theorem exists_card_atypicalFactorizationSet_mertens_beta_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (blocks : Finset (ℕ × ℕ)) (X S : ℕ),
        (∀ I ∈ blocks, 3 ≤ I.1 ∧ I.1 ≤ I.2) → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (#(atypicalFactorizationSet blocks X) : ℝ) ≤
          (X : ℝ) *
              (∑ I ∈ blocks, (1 + eta) *
                (Real.exp (2 * PrimeEstimates.mertensBound) *
                  (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
            ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2) := by
  obtain ⟨A, hA, hblock⟩ := exists_card_missingPrimeBlockSet_mertens_beta_bound
  refine ⟨A, hA, ?_⟩
  intro blocks X S hblocks hS hlog
  dsimp only
  calc
    (#(atypicalFactorizationSet blocks X) : ℝ) ≤
        ((∑ I ∈ blocks, #(missingPrimeBlockSet I X) : ℕ) : ℝ) := by
      exact_mod_cast card_atypicalFactorizationSet_le_sum_card_missing blocks X
    _ = ∑ I ∈ blocks, (#(missingPrimeBlockSet I X) : ℝ) := by push_cast; rfl
    _ ≤ ∑ I ∈ blocks, (
          (X : ℝ) * ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (Real.exp (2 * PrimeEstimates.mertensBound) *
              (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
            (((I.2 ^ S : ℕ) : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hblock X I.1 I.2 S (hblocks I hI).1 (hblocks I hI).2 hS hlog
    _ = (X : ℝ) *
              (∑ I ∈ blocks, (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (Real.exp (2 * PrimeEstimates.mertensBound) *
                  (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
            ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Budget form of the exceptional-set estimate.  Once the logarithmic Mertens sum is at most
`delta` and the explicit finite-sieve remainder is at most `rho * X`, the atypical set has
density at most `delta + rho`.  Thus no unproved sieve remainder remains at the point where
source-specific block parameters are substituted. -/
theorem exists_card_atypicalFactorizationSet_le_of_mertens_beta_budgets :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (blocks : Finset (ℕ × ℕ)) (X S : ℕ) (delta rho : ℝ),
        (∀ I ∈ blocks, 3 ≤ I.1 ∧ I.1 ≤ I.2) → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (∑ I ∈ blocks, (1 + eta) *
            (Real.exp (2 * PrimeEstimates.mertensBound) *
              (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) ≤ delta →
        (∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤ rho * X →
        (#(atypicalFactorizationSet blocks X) : ℝ) ≤ (delta + rho) * X := by
  obtain ⟨A, hA, hfinite⟩ := exists_card_atypicalFactorizationSet_mertens_beta_bound
  refine ⟨A, hA, ?_⟩
  intro blocks X S delta rho hblocks hS hlog
  dsimp only
  intro hmain hrem
  have hbad := hfinite blocks X S hblocks hS hlog
  dsimp only at hbad
  calc
    (#(atypicalFactorizationSet blocks X) : ℝ) ≤
        (X : ℝ) *
            (∑ I ∈ blocks,
              (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (Real.exp (2 * PrimeEstimates.mertensBound) *
                  (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
          ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2) := hbad
    _ ≤ (X : ℝ) * delta + rho * X :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity)) hrem
    _ = (delta + rho) * X := by ring

/-- Every real beta-sieve constant admits a finite Rosser depth satisfying the concrete
fundamental-lemma parameter inequality. -/
theorem exists_admissible_betaSieveDepth (A : ℝ) :
    ∃ S : ℕ, 101 ≤ S ∧ Real.log A ≤ 2 * (S - 100 : ℕ) / 99 := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge ((99 / 2 : ℝ) * Real.log A)
  refine ⟨n + 101, by omega, ?_⟩
  rw [show n + 101 - 100 = n + 1 by omega]
  norm_num [div_eq_mul_inv] at hn ⊢
  nlinarith

/-- Unconditional finite typical-set estimate with a single admissible beta-sieve depth fixed
once and for all.  The displayed remainder depends only on the chosen finite block family, not
on `X`, so this is also the direct finite precursor of the density statement in MRT Lemma 2.2. -/
theorem exists_uniform_card_atypicalFactorizationSet_mertens_beta_bound :
    ∃ A : ℝ, ∃ S : ℕ,
      1 ≤ A ∧ 101 ≤ S ∧
      Real.log A ≤ 2 * (S - 100 : ℕ) / 99 ∧
      ∀ (blocks : Finset (ℕ × ℕ)) (X : ℕ),
        (∀ I ∈ blocks, 3 ≤ I.1 ∧ I.1 ≤ I.2) →
        (#(atypicalFactorizationSet blocks X) : ℝ) ≤
          (X : ℝ) *
              (∑ I ∈ blocks,
                (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  (Real.exp (2 * PrimeEstimates.mertensBound) *
                    (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
            ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2) := by
  obtain ⟨A, hA, hfinite⟩ := exists_card_atypicalFactorizationSet_mertens_beta_bound
  obtain ⟨S, hS, hlog⟩ := exists_admissible_betaSieveDepth A
  exact ⟨A, S, hA, hS, hlog, fun blocks X hblocks ↦
    hfinite blocks X S hblocks hS hlog⟩

theorem exists_natThreshold_remainder_le_mul {R epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → R ≤ epsilon * X := by
  refine ⟨Nat.ceil (R / epsilon), ?_⟩
  intro X hX
  have hquot : R / epsilon ≤ (X : ℝ) :=
    (Nat.le_ceil (R / epsilon)).trans (by exact_mod_cast hX)
  calc
    R = epsilon * (R / epsilon) := by field_simp
    _ ≤ epsilon * X := mul_le_mul_of_nonneg_left hquot hepsilon.le

/-- Asymptotic-density form of the preceding unconditional finite theorem.  For any fixed
finite family of source-valid blocks, the explicit beta-sieve remainder is absorbed into an
arbitrary positive density loss once `X` is large enough. -/
theorem exists_eventually_card_atypicalFactorizationSet_mertens_bound :
    ∃ A : ℝ, ∃ S : ℕ,
      1 ≤ A ∧ 101 ≤ S ∧
      Real.log A ≤ 2 * (S - 100 : ℕ) / 99 ∧
      ∀ (blocks : Finset (ℕ × ℕ)),
        (∀ I ∈ blocks, 3 ≤ I.1 ∧ I.1 ≤ I.2) →
        ∀ epsilon : ℝ, 0 < epsilon →
          ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
            (#(atypicalFactorizationSet blocks X) : ℝ) ≤
              ((∑ I ∈ blocks,
                  (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                    (Real.exp (2 * PrimeEstimates.mertensBound) *
                      (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
                epsilon) * X := by
  obtain ⟨A, S, hA, hS, hlog, hfinite⟩ :=
    exists_uniform_card_atypicalFactorizationSet_mertens_beta_bound
  refine ⟨A, S, hA, hS, hlog, ?_⟩
  intro blocks hblocks epsilon hepsilon
  obtain ⟨X₀, hrem⟩ := exists_natThreshold_remainder_le_mul
    (R := ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2)) hepsilon
  refine ⟨X₀, ?_⟩
  intro X hX
  calc
    (#(atypicalFactorizationSet blocks X) : ℝ) ≤
        (X : ℝ) *
            (∑ I ∈ blocks,
              (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (Real.exp (2 * PrimeEstimates.mertensBound) *
                  (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
          ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2) :=
      hfinite blocks X hblocks
    _ ≤ (X : ℝ) *
          (∑ I ∈ blocks,
            (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (Real.exp (2 * PrimeEstimates.mertensBound) *
                (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
        epsilon * X := add_le_add_right (hrem X hX) _
    _ = ((∑ I ∈ blocks,
            (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (Real.exp (2 * PrimeEstimates.mertensBound) *
                (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) +
          epsilon) * X := by ring

/-! ## Source-style indexed prime blocks -/

/-- The finite block family obtained from the first `J` entries of an indexed block schedule. -/
def indexedPrimeBlocks (block : ℕ → ℕ × ℕ) (J : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 J).image block

@[simp]
theorem mem_indexedPrimeBlocks {block : ℕ → ℕ × ℕ} {J : ℕ} {I : ℕ × ℕ} :
    I ∈ indexedPrimeBlocks block J ↔ ∃ j ∈ Finset.Icc 1 J, block j = I := by
  simp [indexedPrimeBlocks]

/-- The elementary summability estimate used in MRT Lemma 2.2. -/
theorem sum_Icc_one_div_sq_le_two (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, (((j : ℝ) ^ 2)⁻¹)) ≤ 2 := by
  have hset : Finset.Icc 1 J = Finset.Ioo 0 (J + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hset]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1))

/-- If the logarithmic ratio of the `j`-th source block is at most `r/j²`, the sum of
all block ratios is at most `2r`.  This is the exact finite numerical summation behind the
`log P₁ / log Q₁` exceptional-density estimate. -/
theorem sum_indexedPrimeBlocks_logRatio_le_two_mul
    {block : ℕ → ℕ × ℕ} {J : ℕ} {r : ℝ}
    (hinj : Set.InjOn block ↑(Finset.Icc 1 J)) (hr : 0 ≤ r)
    (hratio : ∀ j ∈ Finset.Icc 1 J,
      Real.log ((block j).1 - 1 : ℕ) / Real.log ((block j).2 : ℝ) ≤
        r * (((j : ℝ) ^ 2)⁻¹)) :
    (∑ I ∈ indexedPrimeBlocks block J,
        Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)) ≤ 2 * r := by
  rw [indexedPrimeBlocks, Finset.sum_image hinj]
  calc
    (∑ j ∈ Finset.Icc 1 J,
        Real.log (((block j).1 - 1 : ℕ) : ℝ) / Real.log ((block j).2 : ℝ)) ≤
        ∑ j ∈ Finset.Icc 1 J, r * (((j : ℝ) ^ 2)⁻¹) :=
      Finset.sum_le_sum fun j hj ↦ hratio j hj
    _ = r * ∑ j ∈ Finset.Icc 1 J, (((j : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left (sum_Icc_one_div_sq_le_two J) hr
    _ = 2 * r := by ring

/-- Source-level exceptional-density conclusion for any injective MRT-style block schedule.
The absolute constant includes the fully formalized beta-sieve and Mertens constants.  If the
`j`-th logarithmic block ratio is bounded by `r/j²`, then, for all sufficiently large `X`, at
most `C r X` integers in `[1,X]` miss one of the first `J` blocks. -/
theorem exists_sourceSchedule_atypical_density_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (block : ℕ → ℕ × ℕ) (J : ℕ) (r : ℝ),
        Set.InjOn block ↑(Finset.Icc 1 J) →
        (∀ j ∈ Finset.Icc 1 J, 3 ≤ (block j).1 ∧ (block j).1 ≤ (block j).2) →
        0 < r →
        (∀ j ∈ Finset.Icc 1 J,
          Real.log (((block j).1 - 1 : ℕ) : ℝ) / Real.log ((block j).2 : ℝ) ≤
            r * (((j : ℝ) ^ 2)⁻¹)) →
        ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          (#(atypicalFactorizationSet (indexedPrimeBlocks block J) X) : ℝ) ≤
            C * r * X := by
  obtain ⟨A, S, hA, _hS, _hlog, hevent⟩ :=
    exists_eventually_card_atypicalFactorizationSet_mertens_bound
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let K : ℝ := (1 + eta) * Real.exp (2 * PrimeEstimates.mertensBound)
  let C : ℝ := 2 * K + 1
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro block J r hinj hvalid hr hratio
  have hblocks : ∀ I ∈ indexedPrimeBlocks block J,
      3 ≤ I.1 ∧ I.1 ≤ I.2 := by
    intro I hI
    obtain ⟨j, hj, rfl⟩ := mem_indexedPrimeBlocks.mp hI
    exact hvalid j hj
  obtain ⟨X₀, hbad⟩ := hevent (indexedPrimeBlocks block J) hblocks r hr
  refine ⟨X₀, ?_⟩
  intro X hX
  have hsumRatio := sum_indexedPrimeBlocks_logRatio_le_two_mul hinj hr.le hratio
  have hsum :
      (∑ I ∈ indexedPrimeBlocks block J,
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (Real.exp (2 * PrimeEstimates.mertensBound) *
            (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) ≤
        K * (2 * r) := by
    calc
      (∑ I ∈ indexedPrimeBlocks block J,
          (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (Real.exp (2 * PrimeEstimates.mertensBound) *
              (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) =
          K * (∑ I ∈ indexedPrimeBlocks block J,
            Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I hI
        dsimp [K, eta]
        ring
      _ ≤ K * (2 * r) := mul_le_mul_of_nonneg_left hsumRatio hK
  calc
    (#(atypicalFactorizationSet (indexedPrimeBlocks block J) X) : ℝ) ≤
        ((∑ I ∈ indexedPrimeBlocks block J,
            (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (Real.exp (2 * PrimeEstimates.mertensBound) *
                (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) + r) * X :=
      hbad X hX
    _ ≤ (K * (2 * r) + r) * X := by
      apply mul_le_mul_of_nonneg_right
      · exact add_le_add_left hsum r
      · positivity
    _ = C * r * X := by
      dsimp [C]
      ring

theorem totient_primeBlockProduct_cast_real (I : ℕ × ℕ) :
    (Nat.totient (primeBlockProduct I) : ℝ) =
      primeBlockProduct I * primeBlockDensity I := by
  rw [totient_primeBlockProduct]
  unfold primeBlockProduct primeBlockDensity
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (mem_primesInBlock.mp hp).1.one_le
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_primesInBlock.mp hp).1.ne_zero
  rw [Nat.cast_sub hp1]
  field_simp [hp0]
  norm_num

/-- A one-block density bound with the exact complete-period endpoint error. -/
theorem card_missingPrimeBlockSet_cast_le_density_add_error
    (I : ℕ × ℕ) (X : ℕ) :
    (#(missingPrimeBlockSet I X) : ℝ) ≤
      (X : ℝ) * primeBlockDensity I + Nat.totient (primeBlockProduct I) := by
  have hNat := card_missingPrimeBlockSet_le_totient_mul I X
  have hCast : (#(missingPrimeBlockSet I X) : ℝ) ≤
      (Nat.totient (primeBlockProduct I) : ℝ) *
        ((X / primeBlockProduct I : ℕ) + 1) := by
    exact_mod_cast hNat
  calc
    (#(missingPrimeBlockSet I X) : ℝ) ≤
        (Nat.totient (primeBlockProduct I) : ℝ) *
          ((X / primeBlockProduct I : ℕ) + 1) := hCast
    _ ≤ (Nat.totient (primeBlockProduct I) : ℝ) *
          ((X : ℝ) / primeBlockProduct I + 1) := by
      gcongr
      exact Nat.cast_div_le
    _ = (X : ℝ) * primeBlockDensity I +
          Nat.totient (primeBlockProduct I) := by
      rw [totient_primeBlockProduct_cast_real]
      have hP : (primeBlockProduct I : ℝ) ≠ 0 := by
        exact_mod_cast primeBlockProduct_ne_zero I
      field_simp

/-- Summed real-density estimate for all missing blocks. -/
theorem card_atypicalFactorizationSet_cast_le_sum_density_add_error
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) :
    (#(atypicalFactorizationSet blocks X) : ℝ) ≤
      ∑ I ∈ blocks,
        ((X : ℝ) * primeBlockDensity I + Nat.totient (primeBlockProduct I)) := by
  have hNat := card_atypicalFactorizationSet_le_sum_card_missing blocks X
  have hCast : (#(atypicalFactorizationSet blocks X) : ℝ) ≤
      ∑ I ∈ blocks, (#(missingPrimeBlockSet I X) : ℝ) := by
    exact_mod_cast hNat
  exact hCast.trans <| Finset.sum_le_sum fun I _ ↦
    card_missingPrimeBlockSet_cast_le_density_add_error I X

/-- Final density-reduction form: an upper bound for the missing-block Euler products and endpoint
errors immediately yields a lower bound for the number of typical integers. -/
theorem sub_sum_density_add_error_le_card_typical
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) :
    (X : ℝ) -
        ∑ I ∈ blocks,
          ((X : ℝ) * primeBlockDensity I + Nat.totient (primeBlockProduct I)) ≤
      #(typicalFactorizationSet blocks X) := by
  have hbad := card_atypicalFactorizationSet_cast_le_sum_density_add_error blocks X
  have hpartitionNat := typical_card_add_atypical_card blocks X
  have hpartition : (#(typicalFactorizationSet blocks X) : ℝ) +
      #(atypicalFactorizationSet blocks X) = X := by
    exact_mod_cast hpartitionNat
  linarith

/-- Combining the missing-block union bound with the complete-period sieve bound. -/
theorem card_atypicalFactorizationSet_le_sum_totient_mul
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) :
    #(atypicalFactorizationSet blocks X) ≤
      ∑ I ∈ blocks,
        Nat.totient (primeBlockProduct I) * (X / primeBlockProduct I + 1) := by
  refine (card_atypicalFactorizationSet_le_sum_card_missing blocks X).trans ?_
  exact Finset.sum_le_sum fun I _ ↦ card_missingPrimeBlockSet_le_totient_mul I X

/-! ## An interval `BoundingSieve` -/

/-- The multiplicative local density `d ↦ 1/d`, with the obligatory value zero at zero. -/
def reciprocalArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun d ↦ if d = 0 then 0 else (d : ℝ)⁻¹, by simp⟩

@[simp]
theorem reciprocalArithmeticFunction_zero : reciprocalArithmeticFunction 0 = 0 := by
  rfl

@[simp]
theorem reciprocalArithmeticFunction_apply {d : ℕ} (hd : d ≠ 0) :
    reciprocalArithmeticFunction d = (d : ℝ)⁻¹ := by
  simp [reciprocalArithmeticFunction, hd]

theorem reciprocalArithmeticFunction_isMultiplicative :
    ArithmeticFunction.IsMultiplicative reciprocalArithmeticFunction := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [reciprocalArithmeticFunction], ?_⟩
  intro m n hm hn _hcop
  simp [reciprocalArithmeticFunction, hm, hn, Nat.mul_ne_zero hm hn,
    Nat.cast_mul]
  ring

/-- The elementary interval sieve attached to one prime block.  Its remainder records exactly
the discrepancy between the count of multiples of `d` in `[1,X]` and `X/d`. -/
def intervalBlockSieve (I : ℕ × ℕ) (X : ℕ) : BoundingSieve where
  support := Finset.Icc 1 X
  prodPrimes := primeBlockProduct I
  prodPrimes_squarefree := primeBlockProduct_squarefree I
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ by positivity
  totalMass := X
  nu := reciprocalArithmeticFunction
  nu_mult := reciprocalArithmeticFunction_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpdiv
    rw [reciprocalArithmeticFunction_apply hp.ne_zero]
    exact inv_pos.mpr (Nat.cast_pos.mpr hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpdiv
    rw [reciprocalArithmeticFunction_apply hp.ne_zero]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

/-- The sifted sum of `intervalBlockSieve` is literally the number of integers missing the
corresponding prime block. -/
theorem intervalBlockSieve_siftedSum_eq_card_missing (I : ℕ × ℕ) (X : ℕ) :
    (intervalBlockSieve I X).siftedSum = #(missingPrimeBlockSet I X) := by
  rw [missingPrimeBlockSet_eq_filter_coprime]
  rw [BoundingSieve.siftedSum]
  change (∑ d ∈ Finset.Icc 1 X,
    if (primeBlockProduct I).Coprime d then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp

/-- Direct bridge from the abstract Selberg upper-bound sieve to the missing-block count. -/
theorem card_missingPrimeBlockSet_cast_le_mainSum_add_errSum
    (I : ℕ × ℕ) (X : ℕ) (muPlus : ℕ → ℝ)
    (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    (#(missingPrimeBlockSet I X) : ℝ) ≤
      (X : ℝ) * (intervalBlockSieve I X).mainSum muPlus +
        (intervalBlockSieve I X).errSum muPlus := by
  rw [← intervalBlockSieve_siftedSum_eq_card_missing]
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius muPlus hmu

/-- The specialized Λ² Selberg inequality for the interval and prime block. -/
theorem card_missingPrimeBlockSet_cast_le_lambdaSquared
    (I : ℕ × ℕ) (X : ℕ) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (#(missingPrimeBlockSet I X) : ℝ) ≤
      (X : ℝ) *
          (intervalBlockSieve I X).mainSum (BoundingSieve.lambdaSquared w) +
        (intervalBlockSieve I X).errSum (BoundingSieve.lambdaSquared w) :=
  card_missingPrimeBlockSet_cast_le_mainSum_add_errSum I X _
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

end

end Erdos67b
