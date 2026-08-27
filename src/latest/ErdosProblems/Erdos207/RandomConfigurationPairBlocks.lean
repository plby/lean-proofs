/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DistinctEqualRemainders
import ErdosProblems.Erdos207.IndependentBlockSampling
import ErdosProblems.Erdos207.IndependentBlockUpperConcentration

/-! # Independent configuration-pair blocks in random WS2 regularization -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem distinctEqualRemainderPairs_snd_injOn
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) :
    Set.InjOn (fun p : Finset W × Finset W ↦ p.2)
      (distinctEqualRemainderPairs F T T' : Set (Finset W × Finset W)) := by
  intro p hp q hq hsecond
  change p.2 = q.2 at hsecond
  obtain ⟨_, _, _, hT, _, hrem⟩ := mem_distinctEqualRemainderPairs_iff.mp hp
  obtain ⟨_, _, _, hT2, _, hrem2⟩ := mem_distinctEqualRemainderPairs_iff.mp hq
  apply Prod.ext _ hsecond
  calc
    p.1 = insert T (p.1.erase T) := (insert_erase hT).symm
    _ = insert T (q.1.erase T) := by rw [hrem, hsecond, ← hrem2]
    _ = q.1 := insert_erase hT2

theorem distinctEqualRemainderPairs_blocks_pairwiseDisjoint
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) :
    (distinctEqualRemainderPairs F T T' : Set (Finset W × Finset W)).PairwiseDisjoint
      (fun p ↦ ({p.1, p.2} : Finset (Finset W))) := by
  intro p hp q hq hpq
  change Disjoint ({p.1, p.2} : Finset (Finset W)) {q.1, q.2}
  rw [Finset.disjoint_left]
  intro E hEp hEq
  have hpdata := mem_distinctEqualRemainderPairs_iff.mp hp
  have hqdata := mem_distinctEqualRemainderPairs_iff.mp hq
  have hpcross := distinctEqualRemainderPairs_cross_not_mem hp
  have hqcross := distinctEqualRemainderPairs_cross_not_mem hq
  simp only [mem_insert, mem_singleton] at hEp hEq
  rcases hEp with hEp | hEp <;> rcases hEq with hEq | hEq
  · exact hpq (distinctEqualRemainderPairs_fst_injOn F T T' hp hq (hEp.symm.trans hEq))
  · have h : p.1 = q.2 := hEp.symm.trans hEq
    exact hqcross.2 (h ▸ hpdata.2.2.2.1)
  · have h : p.2 = q.1 := hEp.symm.trans hEq
    exact hqcross.1 (h ▸ hpdata.2.2.2.2.1)
  · exact hpq (distinctEqualRemainderPairs_snd_injOn F T T' hp hq (hEp.symm.trans hEq))

theorem distinctEqualRemainderPairs_blockProbability
    {W : Type*} [DecidableEq W] {F : Finset (Finset W)} {T T' : W}
    (p : ℝ≥0) (C : Finset W × Finset W)
    (hC : C ∈ distinctEqualRemainderPairs F T T') :
    blockProbability (fun _ : Finset W ↦ p) (fun C : Finset W × Finset W ↦ {C.1, C.2}) C = p ^ 2 := by
  have hne := (mem_distinctEqualRemainderPairs_iff.mp hC).2.2.1
  simp [blockProbability, hne, pow_two]

theorem independentBits_probability_configurationPairs_card_ge_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    (FiniteLaw.independentBits (fun _ : Finset W ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (activeBlocks (fun C : Finset W × Finset W ↦ {C.1, C.2})
        (distinctEqualRemainderPairs F T T') ω).card) ≤
      ((distinctEqualRemainderPairs F T T').card.choose k : ℝ≥0) * (p ^ 2) ^ k := by
  have h := independentBits_probability_activeBlocks_card_ge_le (fun _ : Finset W ↦ p) (fun _ ↦ hp)
    (fun C : Finset W × Finset W ↦ {C.1, C.2}) (distinctEqualRemainderPairs F T T')
    (distinctEqualRemainderPairs_blocks_pairwiseDisjoint F T T') k
  apply h.trans_eq
  calc
    _ = ∑ A ∈ (distinctEqualRemainderPairs F T T').powersetCard k, (p ^ 2) ^ k := by
      apply sum_congr rfl
      intro A hA
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA
      calc
        _ = ∏ _C ∈ A, p ^ 2 := prod_congr rfl (fun C hC ↦ distinctEqualRemainderPairs_blockProbability p C (hsub hC))
        _ = _ := by rw [prod_const, hcard]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_powersetCard]

theorem distinctEqualRemainderPairs_sample_eq_activeBlocks
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) (ω : Finset W → Bool) :
    distinctEqualRemainderPairs (F.filter fun E ↦ ω E = true) T T' =
      activeBlocks (fun C : Finset W × Finset W ↦ {C.1, C.2}) (distinctEqualRemainderPairs F T T') ω := by
  ext C
  simp only [mem_distinctEqualRemainderPairs_iff, mem_filter, mem_activeBlocks_iff,
    IsBlockActive, forall_mem_insert, mem_singleton, forall_eq]
  tauto

theorem independentBits_probability_sampledConfigurationPairs_card_ge_le_dyadic
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) ^ 2 * (distinctEqualRemainderPairs F T T').card) ≤ k)
    (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : Finset W ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (distinctEqualRemainderPairs (F.filter fun E ↦ ω E = true) T T').card) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  simp_rw [distinctEqualRemainderPairs_sample_eq_activeBlocks]
  apply independentBits_probability_activeBlocks_card_ge_le_dyadic
    (fun _ : Finset W ↦ p) (fun _ ↦ hp)
    (fun C : Finset W × Finset W ↦ {C.1, C.2}) (distinctEqualRemainderPairs F T T')
    (distinctEqualRemainderPairs_blocks_pairwiseDisjoint F T T') (p ^ 2)
    (pow_le_one₀ zero_le hp) (fun C hC ↦ distinctEqualRemainderPairs_blockProbability p C hC) k s
  · simpa only [NNReal.coe_pow] using hk
  · exact hs

end

end Erdos207
