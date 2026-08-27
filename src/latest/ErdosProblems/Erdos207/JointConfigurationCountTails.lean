/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointBlockUpperTail
import ErdosProblems.Erdos207.MixedConfigurationPairBlocks
import ErdosProblems.Erdos207.RealCountCutoff

/-! # The source's strict count tails under an upper joint-inclusion law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem joint_activeBlocks_card_ge_le_dyadic
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (pi : I → ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ i ∈ U, ω i = true) ≤ setWeight pi U)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0)
    (huniform : ∀ j ∈ S, blockProbability pi blocks j = q)
    (s R : ℕ) (hs : 4 * s ≤ R) (hmean : 4 * (q * S.card) ≤ (R : ℝ≥0)) :
    L.probability (fun ω ↦ R ≤ (activeBlocks blocks S ω).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  by_cases hR : R = 0
  · have hs0 : s = 0 := by omega
    rw [hs0]
    simpa only [pow_zero, inv_one] using L.probability_le_one
      (fun ω ↦ R ≤ (activeBlocks blocks S ω).card)
  · exact joint_probability_activeBlocks_card_ge_le_dyadic L pi hjoint blocks S hpair q huniform
      s R (by omega) (by omega) hmean

theorem joint_activeBlocks_card_gt_le_dyadic
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (pi : I → ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ i ∈ U, ω i = true) ≤ setWeight pi U)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q a : ℝ≥0)
    (huniform : ∀ j ∈ S, blockProbability pi blocks j = q)
    (s : ℕ) (hmean : 4 * (q * S.card) ≤ a) (hsize : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    L.probability (fun ω ↦ a < ((activeBlocks blocks S ω).card : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply L.probability_natCast_gt_le_dyadic _ (q * S.card) a s ?_ hmean hsize
  intro R hR hs
  exact joint_activeBlocks_card_ge_le_dyadic L pi hjoint blocks S hpair q huniform s R hs
    (by exact_mod_cast hR)

theorem joint_injective_filter_card_gt_le_dyadic
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (p : ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ i ∈ U, ω i = true) ≤ setWeight (fun _ ↦ p) U)
    (S : Finset J) (f : J → I) (hinj : Set.InjOn f (S : Set J)) (a : ℝ≥0) (s : ℕ)
    (hmean : 4 * (p * S.card) ≤ a) (hsize : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    L.probability (fun ω ↦ a < ((S.filter fun j ↦ ω (f j) = true).card : ℝ≥0)) ≤
      ((2 : ℝ≥0) ^ s)⁻¹ := by
  have heq (ω : I → Bool) : S.filter (fun j ↦ ω (f j) = true) =
      activeBlocks (fun j ↦ ({f j} : Finset I)) S ω := by
    ext j
    simp only [mem_filter, mem_activeBlocks_iff, IsBlockActive, mem_singleton, forall_eq]
  simp_rw [heq]
  exact joint_activeBlocks_card_gt_le_dyadic L (fun _ ↦ p) hjoint (fun j ↦ {f j}) S
    (singleton_blocks_pairwiseDisjoint_of_injOn S f hinj) p a
    (fun j _ ↦ by simp [blockProbability]) s hmean hsize

theorem joint_filter_card_gt_le_dyadic
    {I : Type*} [Fintype I] [DecidableEq I]
    (L : FiniteLaw (I → Bool)) (p : ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ i ∈ U, ω i = true) ≤ setWeight (fun _ ↦ p) U)
    (S : Finset I) (a : ℝ≥0) (s : ℕ)
    (hmean : 4 * (p * S.card) ≤ a) (hsize : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    L.probability (fun ω ↦ a < ((S.filter fun i ↦ ω i = true).card : ℝ≥0)) ≤
      ((2 : ℝ≥0) ^ s)⁻¹ :=
  joint_injective_filter_card_gt_le_dyadic L p hjoint S id (fun _ _ _ _ h ↦ h) a s hmean hsize

theorem joint_sampledConfigurationPairs_card_gt_le_dyadic
    {W : Type*} [Fintype W] [DecidableEq W]
    (L : FiniteLaw (Finset W → Bool)) (p : ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ E ∈ U, ω E = true) ≤ setWeight (fun _ ↦ p) U)
    (F : Finset (Finset W)) (T T' : W) (a : ℝ≥0) (s : ℕ)
    (hmean : 4 * (p ^ 2 * (distinctEqualRemainderPairs F T T').card) ≤ a)
    (hsize : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    L.probability (fun ω ↦ a <
      ((distinctEqualRemainderPairs (F.filter fun E ↦ ω E = true) T T').card : ℝ≥0)) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  simp_rw [distinctEqualRemainderPairs_sample_eq_activeBlocks]
  exact joint_activeBlocks_card_gt_le_dyadic L (fun _ ↦ p) hjoint
    (fun C : Finset W × Finset W ↦ {C.1, C.2}) (distinctEqualRemainderPairs F T T')
    (distinctEqualRemainderPairs_blocks_pairwiseDisjoint F T T') (p ^ 2) a
    (fun C hC ↦ distinctEqualRemainderPairs_blockProbability p C hC) s hmean hsize

end

end Erdos207
