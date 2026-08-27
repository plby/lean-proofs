/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBlockSampling
import ErdosProblems.Erdos207.JointInclusionFactorialTail
import ErdosProblems.Erdos207.WeightSystem

/-! # Upper tails for disjoint active blocks under joint inclusion alone -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem joint_probability_activeBlocks_subset_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (pi : I → ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ i ∈ U, ω i = true) ≤ setWeight pi U)
    (blocks : J → Finset I) (S A : Finset J) (hAS : A ⊆ S)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0)
    (huniform : ∀ j ∈ S, blockProbability pi blocks j = q) :
    L.probability (fun ω ↦ A ⊆ activeBlocks blocks S ω) ≤ q ^ A.card := by
  have hpairA : (A : Set J).PairwiseDisjoint blocks := by
    intro i hi j hj hij
    exact hpair (hAS hi) (hAS hj) hij
  calc
    _ ≤ L.probability (fun ω ↦ ∀ i ∈ A.biUnion blocks, ω i = true) := by
      apply L.probability_mono
      intro ω hA i hi
      obtain ⟨j, hj, hij⟩ := mem_biUnion.mp hi
      exact (mem_activeBlocks_iff.mp (hA hj)).2 i hij
    _ ≤ setWeight pi (A.biUnion blocks) := hjoint _
    _ = ∏ j ∈ A, blockProbability pi blocks j := by
      exact prod_biUnion hpairA
    _ = q ^ A.card := by
      rw [← prod_const]
      exact prod_congr rfl (fun j hj ↦ huniform j (hAS hj))

theorem joint_probability_activeBlocks_card_ge_le_dyadic
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (pi : I → ℝ≥0)
    (hjoint : ∀ U, L.probability (fun ω ↦ ∀ i ∈ U, ω i = true) ≤ setWeight pi U)
    (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0)
    (huniform : ∀ j ∈ S, blockProbability pi blocks j = q)
    (s R : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R)
    (hmean : 4 * (q * S.card) ≤ (R : ℝ≥0)) :
    L.probability (fun ω ↦ R ≤ (activeBlocks blocks S ω).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hsub : ∀ ω, activeBlocks blocks S ω ⊆ S :=
    fun ω j hj ↦ (mem_activeBlocks_iff.mp hj).1
  have htail := L.probability_card_inter_ge_le_powerMoment (activeBlocks blocks S) S s R (q ^ s)
    hR hs (fun A hA ↦ by
      have hm := mem_powersetCard.mp hA
      simpa only [hm.2] using joint_probability_activeBlocks_subset_le L pi hjoint blocks S A hm.1
        hpair q huniform)
  simp_rw [inter_eq_right.mpr (hsub _)] at htail
  apply htail.trans
  have hRreal : (0 : ℝ≥0) < R := by exact_mod_cast hR
  have hbase : 2 * (S.card : ℝ≥0) * q / R ≤ (1 / 2 : ℝ≥0) := by
    apply (div_le_iff₀ hRreal).mpr
    calc
      _ = (4 * (q * S.card)) / 2 := by ring
      _ ≤ (R : ℝ≥0) / 2 := div_le_div_of_nonneg_right hmean zero_le
      _ = _ := by ring
  calc
    (2 * (S.card : ℝ≥0) / R) ^ s * q ^ s = (2 * (S.card : ℝ≥0) * q / R) ^ s := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (1 / 2 : ℝ≥0) ^ s := pow_le_pow_left' hbase s
    _ = _ := by rw [one_div, inv_pow]

end

end Erdos207
