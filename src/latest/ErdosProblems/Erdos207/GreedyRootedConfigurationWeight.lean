/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OmittedFamilyWeight
import ErdosProblems.Erdos207.GreedyConfigurationCardinality

/-! # Tracking a configuration class through an omitted-family weight system -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Configurations with prescribed available roots and `c` chosen members.
For two roots this is the first KSSS crude statistic. -/
def greedyRootedConfigurationClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (R : TripleSystemOn V) (c : ℕ) : ForbiddenFamilyOn V :=
  J.filter fun C ↦ R ⊆ C ∩ S.available ∧ (C ∩ S.chosen).card = c ∧
    C ⊆ S.chosen ∪ S.available

theorem configuration_sdiff_available_eq_inter_chosen
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hC : C ⊆ S.chosen ∪ S.available) :
    C \ S.available = C ∩ S.chosen := by
  ext T
  constructor
  · intro hT
    have hTC := (mem_sdiff.mp hT).1
    refine mem_inter.mpr ⟨hTC, ?_⟩
    rcases mem_union.mp (hC hTC) with hchosen | havailable
    · exact hchosen
    · exact ((mem_sdiff.mp hT).2 havailable).elim
  · intro hT
    refine mem_sdiff.mpr ⟨(mem_inter.mp hT).1, ?_⟩
    intro hA
    exact (hS.2.2 T hA).1 (mem_inter.mp hT).2

def rootedConfigurationOmittedIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (R : TripleSystemOn V) (c m : ℕ)
    (hS : GreedyInvariant F S) (hcard : ∀ C ∈ J, C.card = m)
    (C : greedyRootedConfigurationClass J S R c) :
    OmittedFamilyIndex J R (m - c - R.card) := by
  have hdata := mem_filter.mp C.2
  refine ⟨(C.1, (C.1 ∩ S.available) \ R), hdata.1,
    hdata.2.1.trans inter_subset_left, ?_, ?_⟩
  · intro T hT
    exact mem_sdiff.mpr ⟨(mem_inter.mp (mem_sdiff.mp hT).1).1, (mem_sdiff.mp hT).2⟩
  · rw [card_sdiff_of_subset hdata.2.1]
    have hsum := configuration_chosen_add_available_card hS hdata.2.2.2
    rw [hdata.2.2.1, hcard _ hdata.1] at hsum
    omega

theorem rootedConfigurationOmittedIndex_remainder
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (R : TripleSystemOn V) (c m : ℕ)
    (hS : GreedyInvariant F S) (hcard : ∀ C ∈ J, C.card = m)
    (C : greedyRootedConfigurationClass J S R c) :
    omittedFamilyRemainder (rootedConfigurationOmittedIndex R c m hS hcard C) =
      C.1 ∩ S.chosen := by
  have hdata := mem_filter.mp C.2
  have hset : R ∪ ((C.1 ∩ S.available) \ R) = C.1 ∩ S.available :=
    union_sdiff_of_subset hdata.2.1
  change C.1 \ (R ∪ ((C.1 ∩ S.available) \ R)) = _
  rw [hset]
  have hsdiff : C.1 \ (C.1 ∩ S.available) = C.1 \ S.available := by
    ext T
    simp only [mem_sdiff, mem_inter]
    tauto
  rw [hsdiff, configuration_sdiff_available_eq_inter_chosen hS hdata.2.2.2]

theorem rootedConfigurationOmittedIndex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (R : TripleSystemOn V) (c m : ℕ)
    (hS : GreedyInvariant F S) (hcard : ∀ C ∈ J, C.card = m) :
    Function.Injective (rootedConfigurationOmittedIndex R c m hS hcard) := by
  intro C D h
  apply Subtype.ext
  exact congrArg (fun u ↦ u.1.1) h

theorem greedyRootedConfigurationClass_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (R : TripleSystemOn V) (c m : ℕ)
    (hS : GreedyInvariant F S) (hcard : ∀ C ∈ J, C.card = m) :
    ((greedyRootedConfigurationClass J S R c).card : ℝ≥0) ≤
      selectedCount
        (fun u : OmittedFamilyIndex J R (m - c - R.card) ↦ omittedFamilyRemainder u)
          S.chosen := by
  classical
  let active : Finset (OmittedFamilyIndex J R (m - c - R.card)) :=
    univ.filter fun u ↦ omittedFamilyRemainder u ⊆ S.chosen
  let f : greedyRootedConfigurationClass J S R c → active := fun C ↦
    ⟨rootedConfigurationOmittedIndex R c m hS hcard C, by
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [rootedConfigurationOmittedIndex_remainder]
      exact inter_subset_right⟩
  have hfin : (greedyRootedConfigurationClass J S R c).card ≤ active.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    apply Fintype.card_le_of_injective f
    intro C D h
    apply rootedConfigurationOmittedIndex_injective R c m hS hcard
    exact congrArg Subtype.val h
  have hselected : selectedCount
      (fun u : OmittedFamilyIndex J R (m - c - R.card) ↦ omittedFamilyRemainder u)
        S.chosen = (active.card : ℝ≥0) := by
    unfold selectedCount active
    simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
    apply sum_congr rfl
    intro u _
    by_cases h : omittedFamilyRemainder u ⊆ S.chosen <;> simp [h]
  rw [hselected]
  exact_mod_cast hfin

end

end Erdos207
