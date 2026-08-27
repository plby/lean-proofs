/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability

/-!
# Independent activation of disjoint coordinate blocks

In the reserve-edge part of the KSSS master iteration, a candidate third
vertex is usable precisely when a small block of reserve edges is present.
Blocks belonging to distinct candidates are disjoint.  This file proves,
directly from the finite product law, that their all-present indicators are
independent Bernoulli variables.  It also gives the exact union-bound tails
needed for candidate counts.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Every coordinate in the block indexed by `j` is selected. -/
def IsBlockActive
    {I J : Type*} (blocks : J → Finset I) (j : J) (ω : I → Bool) : Prop :=
  ∀ i ∈ blocks j, ω i = true

/-- Active blocks from a prescribed finite index set. -/
noncomputable def activeBlocks
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (blocks : J → Finset I) (S : Finset J) (ω : I → Bool) : Finset J := by
  classical
  exact S.filter fun j ↦ IsBlockActive blocks j ω

@[simp]
lemma mem_activeBlocks_iff
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {blocks : J → Finset I} {S : Finset J} {ω : I → Bool} {j : J} :
    j ∈ activeBlocks blocks S ω ↔
      j ∈ S ∧ IsBlockActive blocks j ω := by
  classical
  simp [activeBlocks]

/-- Success probability of one all-present block. -/
def blockProbability
    {I J : Type*} (p : I → ℝ≥0) (blocks : J → Finset I) (j : J) : ℝ≥0 :=
  ∏ i ∈ blocks j, p i

lemma blockProbability_le_one
    {I J : Type*} [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (j : J) :
    blockProbability p blocks j ≤ 1 := by
  unfold blockProbability
  induction blocks j using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [prod_insert hi]
      exact mul_le_one₀ (hp i) zero_le ih

/-- Exact joint law of active and inactive disjoint blocks.  No independence
of the derived events is assumed: the proof inducts over inactive blocks and
uses the exact product probability for the union of all active coordinates. -/
theorem independentBits_probability_block_pattern
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (A B : Finset J)
    (hpair : ((A ∪ B : Finset J) : Set J).PairwiseDisjoint blocks)
    (hAB : Disjoint A B) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦
          (∀ j ∈ A, IsBlockActive blocks j ω) ∧
          (∀ j ∈ B, ¬ IsBlockActive blocks j ω)) =
      (∏ j ∈ A, blockProbability p blocks j) *
        ∏ j ∈ B, (1 - blockProbability p blocks j) := by
  induction B using Finset.induction_on generalizing A with
  | empty =>
      have hpairA : (A : Set J).PairwiseDisjoint blocks := by
        simpa using hpair
      have hevent :
          (fun ω : I → Bool ↦
            (∀ j ∈ A, IsBlockActive blocks j ω) ∧
            (∀ j ∈ (∅ : Finset J), ¬ IsBlockActive blocks j ω)) =
          (fun ω ↦ ∀ i ∈ A.biUnion blocks, ω i = true) := by
        funext ω
        apply propext
        constructor
        · intro h i hi
          obtain ⟨j, hjA, hiBlock⟩ := mem_biUnion.mp hi
          exact h.1 j hjA i hiBlock
        · intro h
          refine ⟨?_, by simp⟩
          intro j hjA i hiBlock
          exact h i (mem_biUnion.mpr ⟨j, hjA, hiBlock⟩)
      rw [hevent, FiniteLaw.independentBits_probability_forall_true]
      rw [Finset.prod_biUnion hpairA]
      simp [blockProbability]
  | @insert j B hjB ih =>
      have hjA : j ∉ A := by
        intro hj
        exact Finset.disjoint_left.mp hAB hj (mem_insert_self j B)
      have hABsmall : Disjoint A B :=
        hAB.mono_right (subset_insert j B)
      have hpairSmall :
          ((A ∪ B : Finset J) : Set J).PairwiseDisjoint blocks := by
        apply Set.Pairwise.mono _ hpair
        intro x hx
        simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union,
          Set.mem_insert_iff] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inr hx)
      have hABinsert : Disjoint (insert j A) B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        rw [mem_insert] at hxA
        rcases hxA with rfl | hxA
        · exact hjB hxB
        · exact Finset.disjoint_left.mp hABsmall hxA hxB
      have hpairInsert :
          (((insert j A) ∪ B : Finset J) : Set J).PairwiseDisjoint blocks := by
        simpa [Finset.insert_union, Finset.union_assoc,
          Finset.union_left_comm, Finset.union_comm] using hpair
      let E : (I → Bool) → Prop := fun ω ↦
        (∀ a ∈ A, IsBlockActive blocks a ω) ∧
        (∀ b ∈ B, ¬ IsBlockActive blocks b ω)
      let Q : (I → Bool) → Prop := fun ω ↦ IsBlockActive blocks j ω
      have hevent :
          (fun ω : I → Bool ↦
            (∀ a ∈ A, IsBlockActive blocks a ω) ∧
            (∀ b ∈ insert j B, ¬ IsBlockActive blocks b ω)) =
          (fun ω ↦ E ω ∧ ¬ Q ω) := by
        funext ω
        apply propext
        simp only [E, Q, forall_mem_insert]
        tauto
      have heventInsert :
          (fun ω : I → Bool ↦ E ω ∧ Q ω) =
          (fun ω ↦
            (∀ a ∈ insert j A, IsBlockActive blocks a ω) ∧
            (∀ b ∈ B, ¬ IsBlockActive blocks b ω)) := by
        funext ω
        apply propext
        simp only [E, Q, forall_mem_insert]
        tauto
      rw [hevent, FiniteLaw.probability_and_not]
      change
        (FiniteLaw.independentBits p hp).probability E -
            (FiniteLaw.independentBits p hp).probability
              (fun ω ↦ E ω ∧ Q ω) = _
      rw [show (FiniteLaw.independentBits p hp).probability E =
          (∏ a ∈ A, blockProbability p blocks a) *
            ∏ b ∈ B, (1 - blockProbability p blocks b) by
        exact ih A hpairSmall hABsmall]
      rw [heventInsert]
      rw [show (FiniteLaw.independentBits p hp).probability
            (fun ω ↦
              (∀ a ∈ insert j A, IsBlockActive blocks a ω) ∧
              (∀ b ∈ B, ¬ IsBlockActive blocks b ω)) =
          (∏ a ∈ insert j A, blockProbability p blocks a) *
            ∏ b ∈ B, (1 - blockProbability p blocks b) by
        exact ih (insert j A) hpairInsert hABinsert]
      rw [prod_insert hjA, prod_insert hjB]
      calc
        (∏ a ∈ A, blockProbability p blocks a) *
              (∏ b ∈ B, (1 - blockProbability p blocks b)) -
            (blockProbability p blocks j *
                ∏ a ∈ A, blockProbability p blocks a) *
              ∏ b ∈ B, (1 - blockProbability p blocks b) =
          (∏ a ∈ A, blockProbability p blocks a) *
              (∏ b ∈ B, (1 - blockProbability p blocks b)) -
            ((∏ a ∈ A, blockProbability p blocks a) *
              ∏ b ∈ B, (1 - blockProbability p blocks b)) *
                blockProbability p blocks j := by
            congr 1
            ac_rfl
        _ = ((∏ a ∈ A, blockProbability p blocks a) *
              ∏ b ∈ B, (1 - blockProbability p blocks b)) *
                (1 - blockProbability p blocks j) := by
            rw [mul_tsub, mul_one]
        _ = (∏ a ∈ A, blockProbability p blocks a) *
              ((1 - blockProbability p blocks j) *
                ∏ b ∈ B, (1 - blockProbability p blocks b)) := by
            ac_rfl

/-- Exact probability that every block in a pairwise-disjoint family is
active. -/
theorem independentBits_probability_all_blocks_active
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ ∀ j ∈ S, IsBlockActive blocks j ω) =
      ∏ j ∈ S, blockProbability p blocks j := by
  have h := independentBits_probability_block_pattern p hp blocks S ∅
    (by simpa using hpair) (Finset.disjoint_empty_right S)
  simpa using h

/-- Exact probability that no block in a pairwise-disjoint family is
active. -/
theorem independentBits_probability_no_blocks_active
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ ∀ j ∈ S, ¬ IsBlockActive blocks j ω) =
      ∏ j ∈ S, (1 - blockProbability p blocks j) := by
  have h := independentBits_probability_block_pattern p hp blocks ∅ S
    (by simpa using hpair) (Finset.disjoint_empty_left S)
  simpa using h

/-- Upper tail for the number of active blocks. -/
theorem independentBits_probability_activeBlocks_card_ge_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (k : ℕ) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) ≤
      ∑ T ∈ S.powersetCard k,
        ∏ j ∈ T, blockProbability p blocks j := by
  let L := FiniteLaw.independentBits p hp
  let P : Finset J → (I → Bool) → Prop :=
    fun T ω ↦ ∀ j ∈ T, IsBlockActive blocks j ω
  calc
    L.probability (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) ≤
        L.probability (fun ω ↦ ∃ T ∈ S.powersetCard k, P T ω) := by
      apply L.probability_mono
      intro ω hcard
      obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hcard
      refine ⟨T, mem_powersetCard.mpr ⟨?_, hTcard⟩, ?_⟩
      · exact hTsub.trans fun j hj ↦ (mem_activeBlocks_iff.mp hj).1
      · intro j hj
        exact (mem_activeBlocks_iff.mp (hTsub hj)).2
    _ ≤ ∑ T ∈ S.powersetCard k, L.probability (P T) :=
      L.probability_exists_le (S.powersetCard k) P
    _ = ∑ T ∈ S.powersetCard k,
          ∏ j ∈ T, blockProbability p blocks j := by
      apply sum_congr rfl
      intro T hT
      apply independentBits_probability_all_blocks_active
      exact Set.Pairwise.mono
        (Finset.coe_subset.mpr (mem_powersetCard.mp hT).1) hpair

/-- Lower tail for the number of active blocks, expressed by exposing a
prescribed set of inactive blocks. -/
theorem independentBits_probability_activeBlocks_card_le_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (k : ℕ) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) ≤
      ∑ T ∈ S.powersetCard (S.card - k),
        ∏ j ∈ T, (1 - blockProbability p blocks j) := by
  let L := FiniteLaw.independentBits p hp
  let inactiveCount := S.card - k
  let P : Finset J → (I → Bool) → Prop :=
    fun T ω ↦ ∀ j ∈ T, ¬ IsBlockActive blocks j ω
  calc
    L.probability (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) ≤
        L.probability
          (fun ω ↦ ∃ T ∈ S.powersetCard inactiveCount, P T ω) := by
      apply L.probability_mono
      intro ω hcard
      have hpartition := card_sdiff_add_card_inter S
        (activeBlocks blocks S ω)
      have hactiveSub : activeBlocks blocks S ω ⊆ S :=
        fun j hj ↦ (mem_activeBlocks_iff.mp hj).1
      have hinter : S ∩ activeBlocks blocks S ω = activeBlocks blocks S ω :=
        inter_eq_right.mpr hactiveSub
      rw [hinter] at hpartition
      have hinactive : inactiveCount ≤
          (S \ activeBlocks blocks S ω).card := by
        dsimp only [inactiveCount]
        omega
      obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hinactive
      refine ⟨T, mem_powersetCard.mpr ⟨?_, hTcard⟩, ?_⟩
      · exact hTsub.trans sdiff_subset
      · intro j hj hactive
        have hjNot := (mem_sdiff.mp (hTsub hj)).2
        exact hjNot (mem_activeBlocks_iff.mpr
          ⟨(mem_sdiff.mp (hTsub hj)).1, hactive⟩)
    _ ≤ ∑ T ∈ S.powersetCard inactiveCount, L.probability (P T) :=
      L.probability_exists_le (S.powersetCard inactiveCount) P
    _ = ∑ T ∈ S.powersetCard (S.card - k),
          ∏ j ∈ T, (1 - blockProbability p blocks j) := by
      dsimp only [inactiveCount]
      apply sum_congr rfl
      intro T hT
      apply independentBits_probability_no_blocks_active
      exact Set.Pairwise.mono
        (Finset.coe_subset.mpr (mem_powersetCard.mp hT).1) hpair

end

end Erdos207
