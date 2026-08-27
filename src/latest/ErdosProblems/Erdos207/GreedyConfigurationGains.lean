/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationClasses

/-! # Exact gain and loss partition for a configuration class -/

namespace Erdos207

open Finset

noncomputable section

def greedyConfigurationRetained
    {V : Type*} [Fintype V] [DecidableEq V]
    (F J : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (c : ℕ) (T : TripleOn V) : ForbiddenFamilyOn V :=
  (greedyConfigurationClass J S root c).filter fun C ↦ T ∉ C ∧
    C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available

def greedyConfigurationGains
    {V : Type*} [Fintype V] [DecidableEq V]
    (F J : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (c : ℕ) (T : TripleOn V) : ForbiddenFamilyOn V :=
  (greedyConfigurationClass J S root c).filter fun C ↦ T ∈ C ∧
    C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available

def greedyConfigurationLosses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F J : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (c : ℕ) (T : TripleOn V) : ForbiddenFamilyOn V :=
  greedyConfigurationClass J S root c \ greedyConfigurationRetained F J S root c T

theorem greedyConfigurationClass_step_succ_eq_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} (c : ℕ)
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    greedyConfigurationClass J (greedyStep F S T) root (c + 1) =
      greedyConfigurationRetained F J S root (c + 1) T ∪
        greedyConfigurationGains F J S root c T := by
  ext C
  rw [greedyConfigurationClass_step_succ_iff hS hT]
  simp only [greedyConfigurationRetained, greedyConfigurationGains, mem_union, mem_filter]
  tauto

theorem greedyConfigurationRetained_disjoint_gains
    {V : Type*} [Fintype V] [DecidableEq V]
    (F J : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (c c' : ℕ) (T : TripleOn V) :
    Disjoint (greedyConfigurationRetained F J S root c T)
      (greedyConfigurationGains F J S root c' T) := by
  apply disjoint_left.mpr
  intro C hret hgain
  exact (mem_filter.mp hret).2.1 (mem_filter.mp hgain).2.1

theorem greedyConfigurationClass_step_zero_eq_retained
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    greedyConfigurationClass J (greedyStep F S T) root 0 =
      greedyConfigurationRetained F J S root 0 T := by
  ext C
  rw [greedyConfigurationClass_step_zero_iff hS hT]
  simp only [greedyConfigurationRetained, mem_filter]

theorem greedyConfigurationClass_increment_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} (c : ℕ)
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    ((greedyConfigurationClass J (greedyStep F S T) root (c + 1)).card : ℝ) -
      (greedyConfigurationClass J S root (c + 1)).card =
        (greedyConfigurationGains F J S root c T).card -
          (greedyConfigurationLosses F J S root (c + 1) T).card := by
  have hnew := congrArg Finset.card
    (greedyConfigurationClass_step_succ_eq_union (J := J) (root := root) c hS hT)
  rw [card_union_of_disjoint (greedyConfigurationRetained_disjoint_gains
    F J S root (c + 1) c T)] at hnew
  have hold : (greedyConfigurationLosses F J S root (c + 1) T).card +
      (greedyConfigurationRetained F J S root (c + 1) T).card =
        (greedyConfigurationClass J S root (c + 1)).card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  have hn := congrArg (fun k : ℕ ↦ (k : ℝ)) hnew
  have ho := congrArg (fun k : ℕ ↦ (k : ℝ)) hold
  push_cast at hn ho
  linarith only [hn, ho]

theorem greedyConfigurationClass_increment_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    ((greedyConfigurationClass J (greedyStep F S T) root 0).card : ℝ) -
      (greedyConfigurationClass J S root 0).card =
        -((greedyConfigurationLosses F J S root 0 T).card : ℝ) := by
  rw [greedyConfigurationClass_step_zero_eq_retained hS hT]
  have hold : (greedyConfigurationLosses F J S root 0 T).card +
      (greedyConfigurationRetained F J S root 0 T).card =
        (greedyConfigurationClass J S root 0).card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  have ho := congrArg (fun k : ℕ ↦ (k : ℝ)) hold
  push_cast at ho
  linarith only [ho]

end

end Erdos207
