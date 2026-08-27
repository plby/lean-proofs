/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationJump

/-! # The unique other available member in a terminal-class loss -/

namespace Erdos207

open Finset

noncomputable section

theorem exists_terminal_configuration_other
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V} {root : TripleOn V}
    {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hC : C ∈ greedyConfigurationClass J S root c) (hcard : C.card = c + 2) :
    ∃ U, U ≠ root ∧ U ∈ C ∧ U ∈ S.available ∧
      C ∩ S.available = {root, U} ∧ C \ S.available ⊆ S.chosen := by
  have hclass := mem_greedyConfigurationClass.mp hC
  have hrootC : root ∈ C ∩ S.available := mem_inter.mpr ⟨hclass.2.1, hroot⟩
  have hc : (C ∩ S.available).card = 2 := by
    have h := greedyConfigurationClass_available_card hS hC
    omega
  have herase : ((C ∩ S.available).erase root).card = 1 := by
    rw [card_erase_of_mem hrootC, hc]
  obtain ⟨U, hUeq⟩ := card_eq_one.mp herase
  have hU : U ∈ (C ∩ S.available).erase root := by rw [hUeq]; simp
  have hd := mem_erase.mp hU
  refine ⟨U, hd.1, (mem_inter.mp hd.2).1, (mem_inter.mp hd.2).2, ?_, ?_⟩
  · calc
      C ∩ S.available = insert root ((C ∩ S.available).erase root) := (insert_erase hrootC).symm
      _ = _ := by rw [hUeq]
  · intro U hU
    rcases mem_union.mp (hclass.2.2.2 (mem_sdiff.mp hU).1) with hchosen | havail
    · exact hchosen
    · exact ((mem_sdiff.mp hU).2 havail).elim

theorem terminal_configuration_remainder_subset_chosen
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {C : TripleSystemOn V} {root U : TripleOn V}
    (hpart : C ∩ S.available = {root, U}) (hrest : C \ S.available ⊆ S.chosen) :
    (C.erase U).erase root ⊆ S.chosen := by
  intro W hW
  have hd := mem_erase.mp hW
  have hd' := mem_erase.mp hd.2
  apply hrest (mem_sdiff.mpr ⟨hd'.2, ?_⟩)
  intro hWA
  have hm : W ∈ ({root, U} : TripleSystemOn V) := hpart ▸ mem_inter.mpr ⟨hd'.2, hWA⟩
  rcases mem_insert.mp hm with hr | hu
  · exact hd.1 hr
  · exact hd'.1 (mem_singleton.mp hu)

theorem terminal_other_mem_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V} {root U : TripleOn V}
    (hC : C ∈ F) (hrootC : root ∈ C) (hUC : U ∈ C) (hUA : U ∈ S.available)
    (hne : U ≠ root) (hpart : C ∩ S.available = {root, U})
    (hrest : C \ S.available ⊆ S.chosen) : U ∈ greedyClosedThreats F S root := by
  exact mem_inter.mpr ⟨hUA, mem_union_right _ (mem_twoAwayForbiddenTriangles_iff.mpr
    ⟨hne, C, hC, hUC, hrootC, terminal_configuration_remainder_subset_chosen hpart hrest⟩)⟩

theorem terminal_root_preserving_selector_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V}
    {root U T : TripleOn V}
    (hC : C ∈ F) (hrootC : root ∈ C) (hroot : root ∈ S.available)
    (hUC : U ∈ C) (hUA : U ∈ S.available) (hne : U ≠ root)
    (hpart : C ∩ S.available = {root, U}) (hrest : C \ S.available ⊆ S.chosen)
    (hT : T ∈ S.available \ greedyClosedThreats F S root) : T ∉ C := by
  intro hTC
  have hm : T ∈ ({root, U} : TripleSystemOn V) :=
    hpart ▸ mem_inter.mpr ⟨hTC, (mem_sdiff.mp hT).1⟩
  rcases mem_insert.mp hm with hTr | hTU
  · subst T
    exact (mem_sdiff.mp hT).2 (mem_greedyClosedThreats_self F S hroot)
  · have hTU := mem_singleton.mp hTU
    subst T
    exact (mem_sdiff.mp hT).2 (terminal_other_mem_closedThreats hC hrootC hUC hUA hne hpart hrest)

theorem terminal_loss_other_mem_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V}
    {root U T : TripleOn V} {c : ℕ}
    (hS : GreedyInvariant F S) (hUA : U ∈ S.available)
    (hpart : C ∩ S.available = {root, U})
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hC : C ∈ greedyConfigurationLosses F J S root c T) : U ∈ greedyClosedThreats F S T := by
  obtain ⟨_, W, hW, hthreat⟩ := (mem_greedyConfigurationLosses_iff hS (mem_sdiff.mp hT).1).mp hC
  rw [hpart] at hW
  rcases mem_insert.mp hW with hWr | hWU
  · subst W
    exact ((mem_sdiff.mp hT).2 hthreat).elim
  · have hWU := mem_singleton.mp hWU
    subst W
    exact (mem_greedyClosedThreats_comm F S (mem_sdiff.mp hT).1 hUA).mpr hthreat

end

end Erdos207
