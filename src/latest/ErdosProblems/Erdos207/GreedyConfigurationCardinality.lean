/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationClasses

/-! # Exact numbers of available members in a tracked configuration -/

namespace Erdos207

open Finset

noncomputable section

theorem configuration_chosen_add_available_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hC : C ⊆ S.chosen ∪ S.available) :
    (C ∩ S.chosen).card + (C ∩ S.available).card = C.card := by
  have hdisjoint : Disjoint (C ∩ S.chosen) (C ∩ S.available) := by
    apply disjoint_left.mpr
    intro U hchosen havailable
    exact (hS.2.2 U (mem_inter.mp havailable).2).1 (mem_inter.mp hchosen).2
  have hunion : (C ∩ S.chosen) ∪ (C ∩ S.available) = C := by
    ext U
    simp only [mem_union, mem_inter]
    constructor
    · exact fun h ↦ h.elim And.left And.left
    · intro hU
      rcases mem_union.mp (hC hU) with hchosen | havailable
      · exact Or.inl ⟨hU, hchosen⟩
      · exact Or.inr ⟨hU, havailable⟩
  rw [← card_union_of_disjoint hdisjoint, hunion]

theorem greedyConfigurationClass_available_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hC : C ∈ greedyConfigurationClass J S root c) :
    c + (C ∩ S.available).card = C.card := by
  obtain ⟨_, _, hc, hcover⟩ := mem_greedyConfigurationClass.mp hC
  simpa only [hc] using configuration_chosen_add_available_card hS hcover

theorem greedyConfigurationClass_available_nonroot_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hC : C ∈ greedyConfigurationClass J S root c) (hcard : C.card = d + 1) :
    ((C ∩ S.available).erase root).card = d - c := by
  have hrootC := (mem_greedyConfigurationClass.mp hC).2.1
  have hsum := greedyConfigurationClass_available_card hS hC
  have herase := card_erase_add_one (mem_inter.mpr ⟨hrootC, hroot⟩)
  omega

end

end Erdos207
