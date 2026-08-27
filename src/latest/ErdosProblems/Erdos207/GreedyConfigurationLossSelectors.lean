/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationThreats

/-! # Root-preserving selectors which destroy a tracked configuration -/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

def greedyConfigurationLossSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (C : TripleSystemOn V) : TripleSystemOn V :=
  ((C ∩ S.available).erase root).biUnion fun U ↦
    greedyClosedThreats F S U \ greedyClosedThreats F S root

theorem root_preserving_configuration_loss_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) :
    (T ∈ S.available \ greedyClosedThreats F S root ∧
      C ∈ greedyConfigurationLosses F J S root c T) ↔
      (C ∈ greedyConfigurationClass J S root c ∧
        T ∈ greedyConfigurationLossSelectors F S root C) := by
  constructor
  · rintro ⟨hT, hC⟩
    obtain ⟨hclass, U, hU, hthreat⟩ :=
      (mem_greedyConfigurationLosses_iff hS (mem_sdiff.mp hT).1).mp hC
    refine ⟨hclass, mem_biUnion.mpr ⟨U, ?_, ?_⟩⟩
    · refine mem_erase.mpr ⟨?_, hU⟩
      intro h
      exact (mem_sdiff.mp hT).2 (h ▸ hthreat)
    · exact mem_sdiff.mpr ⟨hthreat, (mem_sdiff.mp hT).2⟩
  · rintro ⟨hclass, hT⟩
    obtain ⟨U, hU, hthreat⟩ := mem_biUnion.mp hT
    have hUA := (mem_inter.mp (mem_erase.mp hU).2).2
    have hTA : T ∈ S.available := (mem_inter.mp (mem_sdiff.mp hthreat).1).1
    refine ⟨mem_sdiff.mpr ⟨hTA, (mem_sdiff.mp hthreat).2⟩, ?_⟩
    exact (mem_greedyConfigurationLosses_iff hS hTA).mpr
      ⟨hclass, U, (mem_erase.mp hU).2, (mem_sdiff.mp hthreat).1⟩

theorem filter_root_preserving_configuration_loss_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hC : C ∈ greedyConfigurationClass J S root c) :
    {T ∈ S.available \ greedyClosedThreats F S root |
      C ∈ greedyConfigurationLosses F J S root c T} =
        greedyConfigurationLossSelectors F S root C := by
  classical
  ext T
  simpa only [mem_filter, hC, true_and] using
    (root_preserving_configuration_loss_iff (J := J) (root := root)
      (c := c) (C := C) (T := T) hS)

theorem sum_root_preserving_configuration_losses_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c : ℕ) (hS : GreedyInvariant F S) :
    ∑ T ∈ S.available \ greedyClosedThreats F S root,
        (greedyConfigurationLosses F J S root c T).card =
      ∑ C ∈ greedyConfigurationClass J S root c,
        (greedyConfigurationLossSelectors F S root C).card := by
  classical
  let R := S.available \ greedyClosedThreats F S root
  let X := greedyConfigurationClass J S root c
  calc
    (∑ T ∈ R, (greedyConfigurationLosses F J S root c T).card) =
        ∑ T ∈ R, ∑ C ∈ X,
          if C ∈ greedyConfigurationLosses F J S root c T then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro T _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have hset : {C ∈ X | C ∈ greedyConfigurationLosses F J S root c T} =
          greedyConfigurationLosses F J S root c T := by
        ext C
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun h ↦ (mem_sdiff.mp h).1)
      rw [hset]
      rfl
    _ = ∑ C ∈ X, ∑ T ∈ R,
          if C ∈ greedyConfigurationLosses F J S root c T then (1 : ℕ) else 0 := sum_comm
    _ = ∑ C ∈ X, (greedyConfigurationLossSelectors F S root C).card := by
      apply sum_congr rfl
      intro C hC
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [filter_root_preserving_configuration_loss_eq hS hC]
      rfl

end

end Erdos207
