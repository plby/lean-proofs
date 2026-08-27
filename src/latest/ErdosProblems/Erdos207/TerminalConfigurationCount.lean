/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailableTwoAwayWitnesses

/-! # Terminal configuration counts, with all forbidden orders retained -/

namespace Erdos207

open Finset

noncomputable section

def greedyTerminalConfigurations
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) : ForbiddenFamilyOn V :=
  F.filter fun E ↦ T ∈ E ∧ (E ∩ S.available).card = 2 ∧ E ⊆ S.chosen ∪ S.available

theorem availableTwoAwayWitness_first_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    Set.InjOn (fun u : TwoAwayThreatWitness V F T ↦ u.1.1)
      (availableTwoAwayWitnesses F S T) := by
  intro u hu v hv heq
  change u.1.1 = v.1.1 at heq
  have hupart := availableTwoAwayWitness_part hS hT hu
  have hvpart := availableTwoAwayWitness_part hS hT hv
  have hm : u.1.2 ∈ ({T, v.1.2} : TripleSystemOn V) := by
    rw [← hvpart, ← heq]
    rw [hupart]
    simp
  have hbridge : u.1.2 = v.1.2 := by
    rcases mem_insert.mp hm with h | h
    · exact (u.2.2.2.2 h).elim
    · exact mem_singleton.mp h
  exact Subtype.ext (Prod.ext heq hbridge)

theorem image_availableTwoAwayWitnesses_first
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    (availableTwoAwayWitnesses F S T).image (fun u ↦ u.1.1) =
      greedyTerminalConfigurations F S T := by
  classical
  ext E
  constructor
  · intro hE
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hE
    refine mem_filter.mpr ⟨u.2.1, u.2.2.2.1, ?_, availableTwoAwayWitness_cover hT hu⟩
    rw [availableTwoAwayWitness_part hS hT hu, card_pair (Ne.symm u.2.2.2.2)]
  · intro hE
    obtain ⟨hEF, hTE, hpart, hcover⟩ := mem_filter.mp hE
    have hsum := configuration_chosen_add_available_card hS hcover
    have hc : 2 ≤ E.card := by omega
    have hclass : E ∈ greedyConfigurationClass F S T (E.card - 2) :=
      mem_greedyConfigurationClass.mpr ⟨hEF, hTE, by omega, hcover⟩
    obtain ⟨U, hne, hUE, hUA, hsplit, hrest⟩ :=
      exists_terminal_configuration_other hS hT hclass (by omega)
    let u : TwoAwayThreatWitness V F T := ⟨(E, U), hEF, hUE, hTE, hne⟩
    refine mem_image.mpr ⟨u, mem_availableTwoAwayWitnesses.mpr ⟨?_, hUA⟩, rfl⟩
    exact terminal_configuration_remainder_subset_chosen hsplit hrest

theorem card_availableTwoAwayWitnesses_eq_terminal
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    (availableTwoAwayWitnesses F S T).card = (greedyTerminalConfigurations F S T).card := by
  rw [← image_availableTwoAwayWitnesses_first hS hT,
    card_image_of_injOn (availableTwoAwayWitness_first_injOn hS hT)]

def forbiddenFamilyOfOrder
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (j : ℕ) : ForbiddenFamilyOn V :=
  F.filter fun E ↦ E.card = j - 2

theorem mem_forbiddenFamilyOfOrder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {j : ℕ} {E : TripleSystemOn V} :
    E ∈ forbiddenFamilyOfOrder F j ↔ E ∈ F ∧ E.card = j - 2 := by
  simp [forbiddenFamilyOfOrder]

theorem greedyTerminalConfigurations_eq_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V} {q : ℕ}
    (hS : GreedyInvariant F S)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q) :
    greedyTerminalConfigurations F S T = (Icc 4 q).biUnion
      (fun j ↦ greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)) := by
  ext E
  constructor
  · intro hE
    obtain ⟨hEF, hTE, hpart, hcover⟩ := mem_filter.mp hE
    have hsum := configuration_chosen_add_available_card hS hcover
    have hc : 2 ≤ E.card := by omega
    refine mem_biUnion.mpr ⟨E.card + 2, mem_Icc.mpr ⟨by omega, hcard E hEF hc⟩, ?_⟩
    refine mem_greedyConfigurationClass.mpr ⟨mem_forbiddenFamilyOfOrder.mpr ⟨hEF, by omega⟩,
      hTE, by omega, hcover⟩
  · intro hE
    obtain ⟨j, hj, hclass⟩ := mem_biUnion.mp hE
    have hd := mem_greedyConfigurationClass.mp hclass
    have horder := mem_forbiddenFamilyOfOrder.mp hd.1
    have hsum := greedyConfigurationClass_available_card hS hclass
    have hj4 := (mem_Icc.mp hj).1
    exact mem_filter.mpr ⟨horder.1, hd.2.1, by omega, hd.2.2.2⟩

theorem terminalClasses_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) (q : ℕ) :
    (Icc 4 q : Set ℕ).PairwiseDisjoint
      (fun j ↦ greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)) := by
  intro j hj k hk hne
  apply disjoint_left.mpr
  intro E hEj hEk
  have hjcard := (mem_forbiddenFamilyOfOrder.mp (mem_greedyConfigurationClass.mp hEj).1).2
  have hkcard := (mem_forbiddenFamilyOfOrder.mp (mem_greedyConfigurationClass.mp hEk).1).2
  have hj4 := (mem_Icc.mp hj).1
  have hk4 := (mem_Icc.mp hk).1
  exact hne (by omega)

theorem card_availableTwoAwayWitnesses_eq_sum_terminalClasses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V} {q : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q) :
    (availableTwoAwayWitnesses F S T).card = ∑ j ∈ Icc 4 q,
      (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card := by
  rw [card_availableTwoAwayWitnesses_eq_terminal hS hT,
    greedyTerminalConfigurations_eq_biUnion hS hcard,
    card_biUnion (terminalClasses_pairwiseDisjoint F S T q)]

end

end Erdos207
