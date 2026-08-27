/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationGainSelectors

/-! # A distinct forbidden configuration witnesses every failed gain -/

namespace Erdos207

open Finset

noncomputable section

def greedyConfigurationRedundantWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (C : TripleSystemOn V) :
    ForbiddenFamilyOn V :=
  F.filter fun D ↦ D ≠ C ∧ (D ∩ S.available).card = 2 ∧
    D ∩ S.available ⊆ C ∩ S.available ∧ D \ S.available ⊆ S.chosen

theorem exists_redundantWitness_of_badGainSelector
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root T : TripleOn V} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hpack : IsPackingOn C)
    (hthree : 3 ≤ (C ∩ S.available).card)
    (hT : T ∈ greedyConfigurationBadGainSelectors F S root C) :
    ∃ D ∈ greedyConfigurationRedundantWitnesses F S C, T ∈ D ∩ S.available := by
  obtain ⟨hTW, U, hU, hthreat⟩ := mem_filter.mp hT
  have hTC := (mem_inter.mp (mem_erase.mp hTW).2).1
  have hTA := (mem_inter.mp (mem_erase.mp hTW).2).2
  have hUC := (mem_inter.mp (mem_erase.mp hU).2).1
  have hUA := (mem_inter.mp (mem_erase.mp hU).2).2
  have hUT := (mem_erase.mp hU).1
  have htwo : T ∈ twoAwayForbiddenTriangles F S.chosen U := by
    rcases mem_union.mp (mem_inter.mp hthreat).2 with hshare | htwo
    · have hle := hpack.inter_card_le_one hUC hTC hUT
      have hge := mem_triplesSharingPair_iff.mp hshare
      omega
    · exact htwo
  obtain ⟨_, D, hDF, hTD, hUD, hrest⟩ := mem_twoAwayForbiddenTriangles_iff.mp htwo
  have hDA : D ∩ S.available = {T, U} := by
    ext W
    constructor
    · intro hW
      by_cases hWT : W = T
      · simp [hWT]
      by_cases hWU : W = U
      · simp [hWU]
      have hchosen : W ∈ S.chosen :=
        hrest (mem_erase.mpr ⟨hWU, mem_erase.mpr ⟨hWT, (mem_inter.mp hW).1⟩⟩)
      exact ((hS.2.2 W (mem_inter.mp hW).2).1 hchosen).elim
    · intro hW
      rcases mem_insert.mp hW with rfl | hW
      · exact mem_inter.mpr ⟨hTD, hTA⟩
      · have hWU : W = U := mem_singleton.mp hW
        subst W
        exact mem_inter.mpr ⟨hUD, hUA⟩
  have hcard : (D ∩ S.available).card = 2 := by simp [hDA, hUT.symm]
  have hne : D ≠ C := by
    intro h
    rw [h] at hcard
    omega
  refine ⟨D, mem_filter.mpr ⟨hDF, hne, hcard, ?_, ?_⟩,
    mem_inter.mpr ⟨hTD, hTA⟩⟩
  · rw [hDA]
    intro W hW
    rcases mem_insert.mp hW with rfl | hW
    · exact mem_inter.mpr ⟨hTC, hTA⟩
    · have hWU : W = U := mem_singleton.mp hW
      subst W
      exact mem_inter.mpr ⟨hUC, hUA⟩
  · intro W hW
    have hWT : W ≠ T := fun h ↦ (mem_sdiff.mp hW).2 (h ▸ hTA)
    have hWU : W ≠ U := fun h ↦ (mem_sdiff.mp hW).2 (h ▸ hUA)
    exact hrest (mem_erase.mpr ⟨hWU, mem_erase.mpr ⟨hWT, (mem_sdiff.mp hW).1⟩⟩)

theorem card_badGainSelectors_le_twice_redundantWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hpack : IsPackingOn C)
    (hthree : 3 ≤ (C ∩ S.available).card) :
    (greedyConfigurationBadGainSelectors F S root C).card ≤
      2 * (greedyConfigurationRedundantWitnesses F S C).card := by
  classical
  have hsub : greedyConfigurationBadGainSelectors F S root C ⊆
      (greedyConfigurationRedundantWitnesses F S C).biUnion (fun D ↦ D ∩ S.available) := by
    intro T hT
    exact mem_biUnion.mpr (exists_redundantWitness_of_badGainSelector hS hpack hthree hT)
  calc
    _ ≤ ((greedyConfigurationRedundantWitnesses F S C).biUnion
        (fun D ↦ D ∩ S.available)).card := card_le_card hsub
    _ ≤ ∑ D ∈ greedyConfigurationRedundantWitnesses F S C,
        (D ∩ S.available).card := card_biUnion_le
    _ = 2 * (greedyConfigurationRedundantWitnesses F S C).card := by
      rw [sum_congr rfl (fun D hD ↦ (mem_filter.mp hD).2.2.1)]
      simp [mul_comm]

/-- The gain coefficient is `d-c`; the entire defect is bounded by twice
the number of distinct two-available-member forbidden witnesses. -/
theorem greedyConfigurationGainSelectors_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available) (hpack : IsPackingOn C)
    (hC : C ∈ greedyConfigurationClass J S root c) (hcard : C.card = d + 1)
    (hcd : c + 2 ≤ d) :
    |((greedyConfigurationGainSelectors F S root C).card : ℝ) - (d - c : ℕ)| ≤
      2 * (greedyConfigurationRedundantWitnesses F S C).card := by
  have hthree : 3 ≤ (C ∩ S.available).card := by
    have hsum := greedyConfigurationClass_available_card hS hC
    omega
  have hpartition := greedyConfigurationGainSelectors_card_add_bad_eq hS hroot hC hcard
  have hbad := card_badGainSelectors_le_twice_redundantWitnesses root hS hpack hthree
  have hpartitionR := congrArg (fun k : ℕ ↦ (k : ℝ)) hpartition
  push_cast at hpartitionR
  have hbadR : ((greedyConfigurationBadGainSelectors F S root C).card : ℝ) ≤
      2 * (greedyConfigurationRedundantWitnesses F S C).card := by exact_mod_cast hbad
  have hdifference : ((greedyConfigurationGainSelectors F S root C).card : ℝ) -
      (d - c : ℕ) = -((greedyConfigurationBadGainSelectors F S root C).card : ℝ) := by
    linarith only [hpartitionR]
  rw [hdifference, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hbadR

end

end Erdos207
