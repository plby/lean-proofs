/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBlockSampling
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential lower-tail bound for independent block activation

The powerset union bound is not strong enough when the activation parameter
decays with the ambient order.  Here the exact disjoint-block law is summed
with an exponential weight.  The result is a finite Chernoff estimate strong
enough for the reserve graph in KSSS Section 10.2.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Exact probability of one active-block set. -/
theorem independentBits_probability_activeBlocks_eq
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S T : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (hTS : T ⊆ S)
    (q : ℝ≥0) (hq : ∀ j ∈ S, blockProbability p blocks j = q) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ activeBlocks blocks S ω = T) =
      q ^ T.card * (1 - q) ^ (S.card - T.card) := by
  have hunion : T ∪ (S \ T) = S := by
    exact union_sdiff_of_subset hTS
  have hpair' :
      ((T ∪ (S \ T) : Finset J) : Set J).PairwiseDisjoint blocks := by
    rw [hunion]
    exact hpair
  have hdisj : Disjoint T (S \ T) := by
    rw [Finset.disjoint_left]
    intro j hjT hjST
    exact (mem_sdiff.mp hjST).2 hjT
  have hevent :
      (fun ω : I → Bool ↦ activeBlocks blocks S ω = T) =
      (fun ω ↦
        (∀ j ∈ T, IsBlockActive blocks j ω) ∧
        (∀ j ∈ S \ T, ¬ IsBlockActive blocks j ω)) := by
    funext ω
    apply propext
    constructor
    · intro heq
      constructor
      · intro j hj
        have : j ∈ activeBlocks blocks S ω := heq.symm ▸ hj
        exact (mem_activeBlocks_iff.mp this).2
      · intro j hj hactive
        have hjS := (mem_sdiff.mp hj).1
        have : j ∈ activeBlocks blocks S ω :=
          mem_activeBlocks_iff.mpr ⟨hjS, hactive⟩
        exact (mem_sdiff.mp hj).2 (heq ▸ this)
    · rintro ⟨hactive, hinactive⟩
      apply Subset.antisymm
      · intro j hj
        have hjdata := mem_activeBlocks_iff.mp hj
        by_contra hjT
        exact hinactive j (mem_sdiff.mpr ⟨hjdata.1, hjT⟩) hjdata.2
      · intro j hj
        exact mem_activeBlocks_iff.mpr ⟨hTS hj, hactive j hj⟩
  rw [hevent]
  rw [independentBits_probability_block_pattern p hp blocks T (S \ T)
    hpair' hdisj]
  calc
    (∏ j ∈ T, blockProbability p blocks j) *
        ∏ j ∈ S \ T, (1 - blockProbability p blocks j) =
      (∏ _j ∈ T, q) * ∏ _j ∈ S \ T, (1 - q) := by
        congr 1
        · apply prod_congr rfl
          intro j hj
          exact hq j (hTS hj)
        · apply prod_congr rfl
          intro j hj
          rw [hq j (mem_sdiff.mp hj).1]
    _ = q ^ T.card * (1 - q) ^ (S.card - T.card) := by
      simp [card_sdiff, inter_eq_left.mpr hTS]

/-- The binomial-product identity indexed by the powerset.  This form is
convenient because the two factors record the active and inactive blocks. -/
lemma sum_powerset_split_probabilities
    {J R : Type*} [DecidableEq J] [CommSemiring R]
    (S : Finset J) (a b : R) :
    ∑ T ∈ S.powerset, a ^ T.card * b ^ (S.card - T.card) =
      (a + b) ^ S.card := by
  rw [← prod_const, Finset.prod_add]
  apply sum_congr rfl
  intro T hT
  have hTS : T ⊆ S := mem_powerset.mp hT
  simp [card_sdiff, inter_eq_left.mpr hTS]

/-- A weighted generating-function bound for the lower tail of the number
of active blocks.  Its proof exposes the exact active set and sums over all
possible sets, rather than union-bounding choices of inactive blocks. -/
theorem independentBits_probability_activeBlocks_card_le_le_generating
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks)
    (q : ℝ≥0) (hqle : q ≤ 1)
    (huniform : ∀ j ∈ S, blockProbability p blocks j = q)
    (k : ℕ) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) ≤
      (2 : ℝ≥0) ^ k * (1 - q / 2) ^ S.card := by
  classical
  let L := FiniteLaw.independentBits p hp
  let Bad : Finset (Finset J) :=
    S.powerset.filter fun T ↦ T.card ≤ k
  let P : Finset J → (I → Bool) → Prop :=
    fun T ω ↦ activeBlocks blocks S ω = T
  have hqhalf : q / 2 ≤ 1 := by
    exact (div_le_self (by positivity : (0 : ℝ≥0) ≤ q)
      (by norm_num : (1 : ℝ≥0) ≤ 2)).trans hqle
  have hqsplit : q = 2 * (q / 2) := by
    apply NNReal.eq
    push_cast
    ring
  have honeSplit : q / 2 + (1 - q) = 1 - q / 2 := by
    apply NNReal.eq
    rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub hqle,
      NNReal.coe_sub hqhalf]
    norm_num
    ring
  calc
    L.probability (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) ≤
        L.probability (fun ω ↦ ∃ T ∈ Bad, P T ω) := by
      apply L.probability_mono
      intro ω hcard
      refine ⟨activeBlocks blocks S ω, ?_, rfl⟩
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr ?_, hcard⟩
      intro j hj
      exact (mem_activeBlocks_iff.mp hj).1
    _ ≤ ∑ T ∈ Bad, L.probability (P T) :=
      L.probability_exists_le Bad P
    _ = ∑ T ∈ Bad,
          q ^ T.card * (1 - q) ^ (S.card - T.card) := by
      apply sum_congr rfl
      intro T hT
      exact independentBits_probability_activeBlocks_eq p hp blocks S T
        hpair (mem_powerset.mp (mem_filter.mp hT).1) q huniform
    _ ≤ ∑ T ∈ Bad,
          (2 : ℝ≥0) ^ k *
            ((q / 2) ^ T.card * (1 - q) ^ (S.card - T.card)) := by
      apply sum_le_sum
      intro T hT
      have hTk : T.card ≤ k := (mem_filter.mp hT).2
      have hpower : q ^ T.card = (2 * (q / 2)) ^ T.card :=
        congrArg (fun x : ℝ≥0 ↦ x ^ T.card) hqsplit
      calc
        q ^ T.card * (1 - q) ^ (S.card - T.card) =
            (2 : ℝ≥0) ^ T.card *
              ((q / 2) ^ T.card *
                (1 - q) ^ (S.card - T.card)) := by
          rw [hpower, mul_pow]
          ac_rfl
        _ ≤ (2 : ℝ≥0) ^ k *
              ((q / 2) ^ T.card *
                (1 - q) ^ (S.card - T.card)) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right' (by norm_num : (1 : ℝ≥0) ≤ 2) hTk) (by positivity)
    _ = (2 : ℝ≥0) ^ k *
          ∑ T ∈ Bad,
            (q / 2) ^ T.card * (1 - q) ^ (S.card - T.card) := by
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ≥0) ^ k *
          ∑ T ∈ S.powerset,
            (q / 2) ^ T.card * (1 - q) ^ (S.card - T.card) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (fun T hT ↦ (mem_filter.mp hT).1)
          (fun _ _ _ ↦ by positivity)) (by positivity)
    _ = (2 : ℝ≥0) ^ k * (1 - q / 2) ^ S.card := by
      rw [sum_powerset_split_probabilities, honeSplit]

/-- Exponential lower-tail estimate.  If the cutoff is at most one quarter
of the mean `q * |S|`, then the failure probability is at most
`exp (-q * |S| / 4)`.  The constants are deliberately coarse; the master
iteration only needs an exponentially small error. -/
theorem independentBits_probability_activeBlocks_card_le_le_exp
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks)
    (q : ℝ≥0) (hqle : q ≤ 1)
    (huniform : ∀ j ∈ S, blockProbability p blocks j = q)
    (k : ℕ) (hk : (k : ℝ) ≤ (q : ℝ) * S.card / 4) :
    ((FiniteLaw.independentBits p hp).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) : ℝ) ≤
      Real.exp (-((q : ℝ) * S.card) / 4) := by
  have hqhalf : q / 2 ≤ 1 := by
    exact (div_le_self (by positivity : (0 : ℝ≥0) ≤ q)
      (by norm_num : (1 : ℝ≥0) ≤ 2)).trans hqle
  have hgen :=
    independentBits_probability_activeBlocks_card_le_le_generating
      p hp blocks S hpair q hqle huniform k
  have hgenR :
      ((FiniteLaw.independentBits p hp).probability
          (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) : ℝ) ≤
        (2 : ℝ) ^ k * (1 - (q : ℝ) / 2) ^ S.card := by
    have hgenR' :
        ((FiniteLaw.independentBits p hp).probability
            (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) : ℝ) ≤
          (2 : ℝ) ^ k * ((1 - q / 2 : ℝ≥0) : ℝ) ^ S.card := by
      exact_mod_cast hgen
    rw [NNReal.coe_sub hqhalf, NNReal.coe_div] at hgenR'
    norm_num at hgenR' ⊢
    exact hgenR'
  have htwo : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
    calc
      (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := by
        apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp (k : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hqle
  have hbase0 : 0 ≤ 1 - (q : ℝ) / 2 := by linarith
  have hbase :
      1 - (q : ℝ) / 2 ≤ Real.exp (-(q : ℝ) / 2) := by
    convert Real.one_sub_le_exp_neg ((q : ℝ) / 2) using 1 <;> ring_nf
  have hpow :
      (1 - (q : ℝ) / 2) ^ S.card ≤
        Real.exp (-((q : ℝ) * S.card) / 2) := by
    calc
      (1 - (q : ℝ) / 2) ^ S.card ≤
          (Real.exp (-(q : ℝ) / 2)) ^ S.card :=
        pow_le_pow_left₀ hbase0 hbase S.card
      _ = Real.exp ((S.card : ℝ) * (-(q : ℝ) / 2)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-((q : ℝ) * S.card) / 2) := by
        congr 1
        ring
  calc
    ((FiniteLaw.independentBits p hp).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) : ℝ) ≤
        (2 : ℝ) ^ k * (1 - (q : ℝ) / 2) ^ S.card := hgenR
    _ ≤ Real.exp (k : ℝ) * Real.exp (-((q : ℝ) * S.card) / 2) := by
      exact mul_le_mul htwo hpow (pow_nonneg hbase0 _) (Real.exp_nonneg _)
    _ = Real.exp ((k : ℝ) - (q : ℝ) * S.card / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((q : ℝ) * S.card) / 4) := by
      rw [Real.exp_le_exp]
      linarith

end

end Erdos207
