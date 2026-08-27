/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomConfigurationPairBlocks

/-! # One-bit independence for mixed old--random configuration pairs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem singleton_blocks_pairwiseDisjoint_of_injOn
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (hinj : Set.InjOn f (S : Set α)) :
    (S : Set α).PairwiseDisjoint (fun x ↦ ({f x} : Finset β)) := by
  intro x hx y hy hxy
  change Disjoint ({f x} : Finset β) {f y}
  rw [Finset.disjoint_left]
  intro b hbx hby
  exact hxy (hinj hx hy ((mem_singleton.mp hbx).symm.trans (mem_singleton.mp hby)))

theorem firstSelectedPairs_eq_activeBlocks
    {W : Type*} [DecidableEq W] (P : Finset (Finset W × Finset W)) (ω : Finset W → Bool) :
    P.filter (fun C ↦ ω C.1 = true) = activeBlocks
      (fun C : Finset W × Finset W ↦ ({C.1} : Finset (Finset W))) P ω := by
  ext C
  simp only [mem_filter, mem_activeBlocks_iff, IsBlockActive, mem_singleton, forall_eq]

theorem independentBits_probability_firstSelectedPairs_card_ge_le_dyadic
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (P : Finset (Finset W × Finset W))
    (hP : P ⊆ distinctEqualRemainderPairs F T T')
    (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) * P.card) ≤ k) (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : Finset W ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (P.filter fun C ↦ ω C.1 = true).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hinj : Set.InjOn (fun C : Finset W × Finset W ↦ C.1) (P : Set (Finset W × Finset W)) := by
    intro C hC D hD hCD
    exact distinctEqualRemainderPairs_fst_injOn F T T' (hP hC) (hP hD) hCD
  have hpair := singleton_blocks_pairwiseDisjoint_of_injOn P (fun C ↦ C.1) hinj
  simp_rw [firstSelectedPairs_eq_activeBlocks]
  exact independentBits_probability_activeBlocks_card_ge_le_dyadic
    (fun _ : Finset W ↦ p) (fun _ ↦ hp) (fun C : Finset W × Finset W ↦ {C.1}) P
    hpair p hp (fun C _hC ↦ by simp [blockProbability]) k s hk hs

theorem secondSelectedPairs_eq_activeBlocks
    {W : Type*} [DecidableEq W] (P : Finset (Finset W × Finset W)) (ω : Finset W → Bool) :
    P.filter (fun C ↦ ω C.2 = true) = activeBlocks
      (fun C : Finset W × Finset W ↦ ({C.2} : Finset (Finset W))) P ω := by
  ext C
  simp only [mem_filter, mem_activeBlocks_iff, IsBlockActive, mem_singleton, forall_eq]

theorem independentBits_probability_secondSelectedPairs_card_ge_le_dyadic
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (P : Finset (Finset W × Finset W))
    (hP : P ⊆ distinctEqualRemainderPairs F T T')
    (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) * P.card) ≤ k) (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : Finset W ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (P.filter fun C ↦ ω C.2 = true).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hinj : Set.InjOn (fun C : Finset W × Finset W ↦ C.2) (P : Set (Finset W × Finset W)) := by
    intro C hC D hD hCD
    exact distinctEqualRemainderPairs_snd_injOn F T T' (hP hC) (hP hD) hCD
  have hpair := singleton_blocks_pairwiseDisjoint_of_injOn P (fun C ↦ C.2) hinj
  simp_rw [secondSelectedPairs_eq_activeBlocks]
  exact independentBits_probability_activeBlocks_card_ge_le_dyadic
    (fun _ : Finset W ↦ p) (fun _ ↦ hp) (fun C : Finset W × Finset W ↦ {C.2}) P
    hpair p hp (fun C _hC ↦ by simp [blockProbability]) k s hk hs

end

end Erdos207
