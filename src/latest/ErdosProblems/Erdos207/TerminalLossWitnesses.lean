/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalConfigurationLoss
import ErdosProblems.Erdos207.CommonThreatWitness
import ErdosProblems.Erdos207.PairTwoAwayThreatWeight

/-! # Two indexed causes for each terminal-class configuration loss -/

namespace Erdos207

open Finset

noncomputable section

theorem exists_commonThreatWitness_of_terminal_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V}
    {root U T : TripleOn V}
    (hS : GreedyInvariant F S) (hC : C ∈ F) (hrootC : root ∈ C)
    (hroot : root ∈ S.available) (hUC : U ∈ C) (hUA : U ∈ S.available) (hne : U ≠ root)
    (hpart : C ∩ S.available = {root, U}) (hrest : C \ S.available ⊆ S.chosen)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (htwo : U ∈ twoAwayForbiddenTriangles F S.chosen T) :
    ∃ w : CommonThreatWitness F F root T, w.first = C ∧ w.remainder ⊆ S.chosen := by
  have hnotT := terminal_root_preserving_selector_not_mem hC hrootC hroot hUC hUA hne hpart hrest hT
  obtain ⟨hUT, D, hDF, hUD, hTD, hrem⟩ := mem_twoAwayForbiddenTriangles_iff.mp htwo
  let w : CommonThreatWitness F F root T :=
    { bridge := U
      first := C
      second := D
      first_mem := hC
      second_mem := hDF
      first_root := hrootC
      second_root := hTD
      bridge_first := hUC
      bridge_second := hUD
      bridge_ne_first := hne
      bridge_ne_second := hUT
      first_cross := fun h ↦ (hnotT h).elim
      second_cross := by
        intro hRD
        by_contra hrT
        have hc : root ∈ S.chosen := hrem (mem_erase.mpr
          ⟨hrT, mem_erase.mpr ⟨hne.symm, hRD⟩⟩)
        exact (hS.2.2 root hroot).1 hc
      different := by
        intro he
        apply hnotT
        rw [he]
        exact hTD }
  refine ⟨w, rfl, ?_⟩
  apply union_subset
  · change (C.erase root).erase U ⊆ S.chosen
    simpa only [erase_right_comm] using terminal_configuration_remainder_subset_chosen hpart hrest
  · change (D.erase T).erase U ⊆ S.chosen
    simpa only [erase_right_comm] using hrem

abbrev PairInsideSelector {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :=
  {P : PairOn V // P.1 ⊆ T.1}

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    Fintype (PairInsideSelector T) := Fintype.ofFinite _

abbrev TerminalLossWitness
    (V : Type*) [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V) (root T : TripleOn V) :=
  (Σ P : PairInsideSelector T, PairTwoAwayThreatWitness V F root P.1) ⊕
    CommonThreatWitness F F root T

def terminalLossWitnessFirst
    {V : Type*} [Fintype V] [DecidableEq V] {F : ForbiddenFamilyOn V} {root T : TripleOn V} :
    TerminalLossWitness V F root T → TripleSystemOn V
  | Sum.inl p => p.2.val.val.1
  | Sum.inr w => w.first

def terminalLossWitnessRemainder
    {V : Type*} [Fintype V] [DecidableEq V] {F : ForbiddenFamilyOn V} {root T : TripleOn V} :
    TerminalLossWitness V F root T → TripleSystemOn V
  | Sum.inl p => pairTwoAwayThreatRemainder p.2
  | Sum.inr w => w.remainder

theorem exists_terminalLossWitness_of_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V}
    {root T : TripleOn V} {c : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hJ : J ⊆ F) (hpack : IsPackingOn C) (hcard : C.card = c + 2)
    (hC : C ∈ greedyConfigurationLosses F J S root c T) :
    ∃ w : TerminalLossWitness V F root T,
      terminalLossWitnessFirst w = C ∧ terminalLossWitnessRemainder w ⊆ S.chosen := by
  have hclass := (mem_sdiff.mp hC).1
  have hdata := mem_greedyConfigurationClass.mp hclass
  have hCF := hJ hdata.1
  obtain ⟨U, hne, hUC, hUA, hpart, hrest⟩ := exists_terminal_configuration_other hS hroot hclass hcard
  have hthreat := terminal_loss_other_mem_closedThreats hS hUA hpart hT hC
  rcases mem_union.mp (mem_inter.mp hthreat).2 with hshare | htwo
  · have hge := mem_triplesSharingPair_iff.mp hshare
    obtain ⟨P, hPsub, hPcard⟩ := exists_subset_card_eq hge
    let P' : PairOn V := ⟨P, hPcard⟩
    let P'' : PairInsideSelector T := ⟨P', hPsub.trans inter_subset_left⟩
    have hnotshare : U ∉ triplesSharingPair root := by
      intro h
      have hle := hpack.inter_card_le_one hUC hdata.2.1 hne
      have hge := mem_triplesSharingPair_iff.mp h
      rw [inter_comm] at hge
      omega
    let w₀ : TwoAwayThreatWitness V F root := ⟨(C, U), hCF, hUC, hdata.2.1, hne⟩
    let w₁ : PairTwoAwayThreatWitness V F root P' := ⟨w₀, hPsub.trans inter_subset_right, hnotshare⟩
    refine ⟨Sum.inl ⟨P'', w₁⟩, rfl, ?_⟩
    exact terminal_configuration_remainder_subset_chosen hpart hrest
  · obtain ⟨w, hw, hrem⟩ := exists_commonThreatWitness_of_terminal_twoAway hS hCF hdata.2.1
      hroot hUC hUA hne hpart hrest hT htwo
    exact ⟨Sum.inr w, hw, hrem⟩

end

end Erdos207
