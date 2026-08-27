/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyGainDefectPairs
import ErdosProblems.Erdos207.GreedyRootedConfigurationWeight

/-! # Monotonicity of actual rooted and gain-defect statistics -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyRootedConfigurationClass_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {J J' : ForbiddenFamilyOn V} (hJ : J ⊆ J')
    (S : GreedyStateOn V) (R : TripleSystemOn V) (c : ℕ) :
    greedyRootedConfigurationClass J S R c ⊆ greedyRootedConfigurationClass J' S R c := by
  intro E hE
  have h := mem_filter.mp hE
  exact mem_filter.mpr ⟨hJ h.1, h.2⟩

theorem greedyGainDefectPairs_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {J J' G G' : ForbiddenFamilyOn V}
    (hJ : J ⊆ J') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G')
    (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ) :
    greedyGainDefectPairs J G S T c ⊆ greedyGainDefectPairs J' G' S T c := by
  intro p hp
  have hd := mem_filter.mp hp
  have hc := mem_greedyConfigurationClass.mp (mem_product.mp hd.1).1
  have hw := mem_filter.mp hd.2.1
  have hsize : 2 ≤ p.2.card := by
    have h := card_le_card (inter_subset_left : p.2 ∩ S.available ⊆ p.2)
    rw [hw.2.2.1] at h
    exact h
  have hG' := hG p.2 hw.1 hsize
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_greedyConfigurationClass.mpr ⟨hJ hc.1, hc.2⟩, hG'⟩,
    mem_filter.mpr ⟨hG', hw.2⟩, hd.2.2⟩

theorem greedyActiveGainDefectCount_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {J J' G G' : ForbiddenFamilyOn V}
    (hJ : J ⊆ J') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G')
    (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ) :
    greedyActiveGainDefectCount J G S T c ≤ greedyActiveGainDefectCount J' G' S T c := by
  by_cases hT : T ∈ S.available
  · simp only [greedyActiveGainDefectCount, if_pos hT]
    exact card_le_card (greedyGainDefectPairs_mono hJ hG S T c)
  · simp [greedyActiveGainDefectCount, hT]

end

end Erdos207
