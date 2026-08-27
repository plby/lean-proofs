/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClosedThreats
import ErdosProblems.Erdos207.GreedyConfigurationGains

/-! # Configuration loss as a union of actual closed threat sets -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyStep_available_eq_sdiff_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    (greedyStep F S T).available = S.available \ greedyClosedThreats F S T := by
  have hdel := greedyDeletedIn_eq_inter_closedThreats hS hT (univ : TripleSystemOn V)
  simp only [greedyDeletedIn, greedyAvailableIn, inter_univ, univ_inter] at hdel
  ext U
  constructor
  · intro hnext
    refine mem_sdiff.mpr ⟨greedyStep_available_subset F S T hnext, ?_⟩
    rw [← hdel]
    exact fun h ↦ (mem_sdiff.mp h).2 hnext
  · intro hU
    have h := mem_sdiff.mp hU
    by_contra hnot
    exact h.2 (hdel ▸ mem_sdiff.mpr ⟨h.1, hnot⟩)

theorem configuration_covered_after_step_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    {C : TripleSystemOn V} (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hC : C ⊆ S.chosen ∪ S.available) :
    C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available ↔
      ∀ U ∈ C ∩ S.available, U ≠ T → U ∉ greedyClosedThreats F S T := by
  rw [greedyStep_available_eq_sdiff_closedThreats hS hT]
  change C ⊆ insert T S.chosen ∪ (S.available \ greedyClosedThreats F S T) ↔ _
  constructor
  · intro hnext U hU hUT hthreat
    have hUC := (mem_inter.mp hU).1
    have hUA := (mem_inter.mp hU).2
    rcases mem_union.mp (hnext hUC) with hchosen | havailable
    · rcases mem_insert.mp hchosen with h | h
      · exact hUT h
      · exact (hS.2.2 U hUA).1 h
    · exact (mem_sdiff.mp havailable).2 hthreat
  · intro hsafe U hUC
    by_cases hUT : U = T
    · subst U
      exact mem_union_left _ (mem_insert_self _ _)
    rcases mem_union.mp (hC hUC) with hchosen | havailable
    · exact mem_union_left _ (mem_insert_of_mem hchosen)
    · exact mem_union_right _ (mem_sdiff.mpr
        ⟨havailable, hsafe U (mem_inter.mpr ⟨hUC, havailable⟩) hUT⟩)

theorem mem_greedyConfigurationLosses_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    C ∈ greedyConfigurationLosses F J S root c T ↔
      C ∈ greedyConfigurationClass J S root c ∧
        ∃ U ∈ C ∩ S.available, T ∈ greedyClosedThreats F S U := by
  classical
  constructor
  · intro hC
    obtain ⟨hclass, hnot⟩ := mem_sdiff.mp hC
    refine ⟨hclass, ?_⟩
    have hcover := (mem_greedyConfigurationClass.mp hclass).2.2.2
    by_cases hTC : T ∈ C
    · exact ⟨T, mem_inter.mpr ⟨hTC, hT⟩, mem_greedyClosedThreats_self F S hT⟩
    have hnext : ¬ C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available := by
      intro h
      exact hnot (mem_filter.mpr ⟨hclass, hTC, h⟩)
    rw [configuration_covered_after_step_iff hS hT hcover] at hnext
    push_neg at hnext
    obtain ⟨U, hU, _, hthreat⟩ := hnext
    exact ⟨U, hU, (mem_greedyClosedThreats_comm F S hT (mem_inter.mp hU).2).mp hthreat⟩
  · rintro ⟨hclass, U, hU, hthreat⟩
    refine mem_sdiff.mpr ⟨hclass, ?_⟩
    intro hret
    obtain ⟨_, hTC, hcover⟩ := mem_filter.mp hret
    have hUT : U ≠ T := fun h ↦ hTC (h ▸ (mem_inter.mp hU).1)
    have hcoverOld := (mem_greedyConfigurationClass.mp hclass).2.2.2
    have hsafe := (configuration_covered_after_step_iff hS hT hcoverOld).mp hcover
    exact hsafe U hU hUT
      ((mem_greedyClosedThreats_comm F S hT (mem_inter.mp hU).2).mpr hthreat)

theorem mem_greedyConfigurationGains_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    C ∈ greedyConfigurationGains F J S root c T ↔
      C ∈ greedyConfigurationClass J S root c ∧ T ∈ C ∧
        ∀ U ∈ C ∩ S.available, U ≠ T → T ∉ greedyClosedThreats F S U := by
  classical
  simp only [greedyConfigurationGains, mem_filter]
  constructor
  · rintro ⟨hclass, hTC, hnext⟩
    refine ⟨hclass, hTC, ?_⟩
    have hsafe := (configuration_covered_after_step_iff hS hT
      (mem_greedyConfigurationClass.mp hclass).2.2.2).mp hnext
    intro U hU hUT hthreat
    exact hsafe U hU hUT
      ((mem_greedyClosedThreats_comm F S hT (mem_inter.mp hU).2).mpr hthreat)
  · rintro ⟨hclass, hTC, hsafe⟩
    refine ⟨hclass, hTC, (configuration_covered_after_step_iff hS hT
      (mem_greedyConfigurationClass.mp hclass).2.2.2).mpr ?_⟩
    intro U hU hUT hthreat
    exact hsafe U hU hUT
      ((mem_greedyClosedThreats_comm F S hT (mem_inter.mp hU).2).mp hthreat)

end

end Erdos207
