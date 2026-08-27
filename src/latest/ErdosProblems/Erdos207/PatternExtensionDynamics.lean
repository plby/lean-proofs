/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ProperPatternExtensions
import ErdosProblems.Erdos207.PatternSurvivalKernel
import ErdosProblems.Erdos207.GreedyConfigurationThreats

/-! # Exact deletion incidences and drift for proper pattern extensions -/

namespace Erdos207

open Finset

noncomputable section

def patternExtensionLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V)
    (S : GreedyStateOn V) (T : TripleOn V) : Finset V :=
  properPatternExtensions S.available Q U \
    properPatternExtensions (greedyStep F S T).available Q U

def patternExtensionKillers
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V)
    (S : GreedyStateOn V) (u : V) : TripleSystemOn V := by
  classical
  exact (patternSurvivalSelectors Q S).filter fun T ↦ u ∈ patternExtensionLoss F Q U S T

def patternExtensionClosedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (u : V) (hu : u ∉ graphSupportFinset Q) : TripleSystemOn V :=
  (graphEdges Q).attach.biUnion fun e ↦
    greedyClosedThreats F S (patternExtensionTriangle Q e u hu)

theorem properPatternExtensions_greedyStep_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    properPatternExtensions (greedyStep F S T).available Q U ⊆
      properPatternExtensions S.available Q U :=
  properPatternExtensions_mono_available (greedyStep_available_subset F S T) Q U

theorem properPatternExtensions_step_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    ((properPatternExtensions (greedyStep F S T).available Q U).card : ℝ) -
      (properPatternExtensions S.available Q U).card =
      -((patternExtensionLoss F Q U S T).card : ℝ) := by
  have hnat := card_sdiff_add_card_eq_card
    (properPatternExtensions_greedyStep_subset F Q U S T)
  have hreal : ((patternExtensionLoss F Q U S T).card : ℝ) +
      (properPatternExtensions (greedyStep F S T).available Q U).card =
        (properPatternExtensions S.available Q U).card := by exact_mod_cast hnat
  linarith only [hreal]

theorem mem_patternExtensionLoss_iff_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (T : TripleOn V) (hT : T ∈ S.available)
    (u : V) (hu : u ∉ graphSupportFinset Q)
    (huY : u ∈ properPatternExtensions S.available Q U) :
    u ∈ patternExtensionLoss F Q U S T ↔ T ∈ patternExtensionClosedThreats F Q S u hu := by
  classical
  have hold := (mem_properPatternExtensions_iff_triangles S.available Q U u hu).mp huY
  rw [patternExtensionLoss, mem_sdiff, and_iff_right huY,
    mem_properPatternExtensions_iff_triangles _ Q U u hu, and_iff_right hold.1]
  rw [greedyStep_available_eq_sdiff_closedThreats hS hT]
  constructor
  · intro hnot
    push_neg at hnot
    obtain ⟨e, he⟩ := hnot
    have hthreat : patternExtensionTriangle Q e u hu ∈ greedyClosedThreats F S T := by
      by_contra h
      exact he (mem_sdiff.mpr ⟨hold.2 e, h⟩)
    apply mem_biUnion.mpr
    exact ⟨e, mem_attach _ _, (mem_greedyClosedThreats_comm F S hT (hold.2 e)).mp hthreat⟩
  · intro hmem hnext
    obtain ⟨e, _, he⟩ := mem_biUnion.mp hmem
    exact (mem_sdiff.mp (hnext e)).2
      ((mem_greedyClosedThreats_comm F S hT (hold.2 e)).mpr he)

theorem patternExtensionKillers_eq_inter_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (huY : u ∈ properPatternExtensions S.available Q U) :
    patternExtensionKillers F Q U S u =
      patternSurvivalSelectors Q S ∩ patternExtensionClosedThreats F Q S u hu := by
  classical
  ext T
  simp only [patternExtensionKillers, mem_filter, mem_inter]
  by_cases hR : T ∈ patternSurvivalSelectors Q S
  · rw [and_iff_right hR, and_iff_right hR]
    exact mem_patternExtensionLoss_iff_closedThreats hS Q U T
      (mem_patternSurvivalSelectors_iff Q S T |>.mp hR).1 u hu huY
  · simp only [hR, false_and]

theorem sum_patternExtensionLoss_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V) :
    ∑ T ∈ patternSurvivalSelectors Q S, (patternExtensionLoss F Q U S T).card =
      ∑ u ∈ properPatternExtensions S.available Q U, (patternExtensionKillers F Q U S u).card := by
  classical
  simp only [patternExtensionLoss, sdiff_eq_filter, patternExtensionKillers,
    card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  simp only [mem_filter, hu, true_and]

theorem restrictedGreedyKernel_properPatternExtension_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
      ((properPatternExtensions S'.available Q U).card : ℝ) -
        (properPatternExtensions S.available Q U).card) =
      -(∑ u ∈ properPatternExtensions S.available Q U,
          ((patternExtensionKillers F Q U S u).card : ℝ)) /
        (patternSurvivalSelectors Q S).card := by
  rw [restrictedGreedyKernel_expectationReal]
  simp_rw [properPatternExtensions_step_increment]
  have hsum : (∑ T ∈ patternSurvivalSelectors Q S,
      ((patternExtensionLoss F Q U S T).card : ℝ)) =
      ∑ u ∈ properPatternExtensions S.available Q U,
        ((patternExtensionKillers F Q U S u).card : ℝ) := by
    exact_mod_cast sum_patternExtensionLoss_card F Q U S
  rw [sum_neg_distrib, hsum]
  ring

end

end Erdos207
