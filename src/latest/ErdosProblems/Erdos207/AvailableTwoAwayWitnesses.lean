/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoAwayThreatWeight
import ErdosProblems.Erdos207.TerminalConfigurationLoss

/-! # Available two-away witnesses and terminal configuration classes -/

namespace Erdos207

open Finset

noncomputable section

def availableTwoAwayWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    Finset (TwoAwayThreatWitness V F T) := by
  classical
  exact (activeTwoAwayThreatWitnesses F S.chosen T).filter fun u ↦ u.1.2 ∈ S.available

@[simp] theorem mem_availableTwoAwayWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    {u : TwoAwayThreatWitness V F T} :
    u ∈ availableTwoAwayWitnesses F S T ↔
      twoAwayThreatRemainder u ⊆ S.chosen ∧ u.1.2 ∈ S.available := by
  classical
  simp [availableTwoAwayWitnesses]

theorem image_availableTwoAwayWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    (availableTwoAwayWitnesses F S T).image (fun u ↦ u.1.2) =
      S.available ∩ twoAwayForbiddenTriangles F S.chosen T := by
  classical
  ext U
  constructor
  · rintro h
    obtain ⟨u, hu, rfl⟩ := mem_image.mp h
    have hd := mem_availableTwoAwayWitnesses.mp hu
    exact mem_inter.mpr ⟨hd.2, mem_twoAwayForbiddenTriangles_iff.mpr
      ⟨u.2.2.2.2, u.1.1, u.2.1, u.2.2.1, u.2.2.2.1, hd.1⟩⟩
  · rintro h
    obtain ⟨hne, E, hEF, hUE, hTE, hrest⟩ :=
      mem_twoAwayForbiddenTriangles_iff.mp (mem_inter.mp h).2
    let u : TwoAwayThreatWitness V F T := ⟨(E, U), hEF, hUE, hTE, hne⟩
    exact mem_image.mpr ⟨u, mem_availableTwoAwayWitnesses.mpr ⟨hrest, (mem_inter.mp h).1⟩, rfl⟩

theorem availableTwoAwayWitness_part
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    {u : TwoAwayThreatWitness V F T} (hu : u ∈ availableTwoAwayWitnesses F S T) :
    u.1.1 ∩ S.available = {T, u.1.2} := by
  have hd := mem_availableTwoAwayWitnesses.mp hu
  ext U
  constructor
  · intro hU
    by_cases hUT : U = T
    · simp [hUT]
    by_cases hUb : U = u.1.2
    · simp [hUb]
    have hchosen := hd.1 (mem_erase.mpr ⟨hUT, mem_erase.mpr ⟨hUb, (mem_inter.mp hU).1⟩⟩)
    exact ((hS.2.2 U (mem_inter.mp hU).2).1 hchosen).elim
  · intro hU
    rcases mem_insert.mp hU with rfl | h
    · exact mem_inter.mpr ⟨u.2.2.2.1, hT⟩
    · have h := mem_singleton.mp h
      subst U
      exact mem_inter.mpr ⟨u.2.2.1, hd.2⟩

theorem availableTwoAwayWitness_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hT : T ∈ S.available)
    {u : TwoAwayThreatWitness V F T} (hu : u ∈ availableTwoAwayWitnesses F S T) :
    u.1.1 ⊆ S.chosen ∪ S.available := by
  have hd := mem_availableTwoAwayWitnesses.mp hu
  intro U hU
  by_cases hUT : U = T
  · exact mem_union_right _ (hUT ▸ hT)
  by_cases hUb : U = u.1.2
  · exact mem_union_right _ (hUb ▸ hd.2)
  exact mem_union_left _ (hd.1 (mem_erase.mpr ⟨hUT, mem_erase.mpr ⟨hUb, hU⟩⟩))

theorem availableTwoAwayWitness_mem_terminal_class
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    {u : TwoAwayThreatWitness V F T} (hu : u ∈ availableTwoAwayWitnesses F S T) :
    u.1.1 ∈ greedyConfigurationClass F S T (u.1.1.card - 2) := by
  have hcover := availableTwoAwayWitness_cover hT hu
  have hpart := availableTwoAwayWitness_part hS hT hu
  have hsum := configuration_chosen_add_available_card hS hcover
  rw [hpart, card_pair (Ne.symm u.2.2.2.2)] at hsum
  exact mem_greedyConfigurationClass.mpr ⟨u.2.1, u.2.2.2.1, by omega, hcover⟩

end

end Erdos207
