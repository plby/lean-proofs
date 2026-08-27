/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternSurvivalKernel
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-! # The excluded selectors are exactly the union of the base-edge stars -/

namespace Erdos207

open Finset

noncomputable section

def patternBasePairStars
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) : TripleSystemOn V :=
  (graphEdges Q).biUnion fun e ↦ availableTrianglesContainingPair S e.toFinset

theorem patternBasePairStars_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) : patternBasePairStars Q S ⊆ S.available := by
  intro T hT
  obtain ⟨e, _, he⟩ := mem_biUnion.mp hT
  exact (mem_availableTrianglesContainingPair_iff.mp he).1

theorem patternSurvivalSelectors_eq_sdiff_base
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) :
    patternSurvivalSelectors Q S = S.available \ patternBasePairStars Q S := by
  ext T
  rw [mem_patternSurvivalSelectors_iff, mem_sdiff]
  constructor
  · rintro ⟨hTA, hdis⟩
    refine ⟨hTA, ?_⟩
    intro hbase
    obtain ⟨e, he, hT⟩ := mem_biUnion.mp hbase
    exact disjoint_left.mp hdis he
      ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T
        (Q.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))).mpr
          (mem_availableTrianglesContainingPair_iff.mp hT).2)
  · rintro ⟨hTA, hnot⟩
    refine ⟨hTA, disjoint_left.mpr ?_⟩
    intro e he heT
    apply hnot
    exact mem_biUnion.mpr ⟨e, he, mem_availableTrianglesContainingPair_iff.mpr
      ⟨hTA, (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T
        (Q.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))).mp heT⟩⟩

theorem card_patternBasePairStars_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) :
    (patternBasePairStars Q S).card ≤
      ∑ e ∈ graphEdges Q, (availableTrianglesContainingPair S e.toFinset).card :=
  card_biUnion_le

theorem card_patternBasePairStars_le_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) :
    (patternBasePairStars Q S).card ≤ (graphEdges Q).card * Fintype.card V := by
  refine (card_patternBasePairStars_le_sum Q S).trans ?_
  calc
    _ ≤ ∑ _e ∈ graphEdges Q, Fintype.card V := by
      apply sum_le_sum
      intro e he
      have hc : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e
        (Q.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))
      apply (card_le_card ?_).trans (card_universeTriplesContainingPair_le V e.toFinset hc)
      intro T hT
      exact mem_universeTriplesContainingPair_iff.mpr
        (mem_availableTrianglesContainingPair_iff.mp hT).2
    _ = _ := by simp

theorem patternSurvivalSelectors_card_add_base
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) :
    (patternSurvivalSelectors Q S).card + (patternBasePairStars Q S).card = S.available.card := by
  rw [patternSurvivalSelectors_eq_sdiff_base]
  exact card_sdiff_add_card_eq_card (patternBasePairStars_subset Q S)

theorem patternSurvivalSelectors_nonempty_of_order_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V)
    (h : (graphEdges Q).card * Fintype.card V < S.available.card) :
    (patternSurvivalSelectors Q S).Nonempty := by
  have hsum := patternSurvivalSelectors_card_add_base Q S
  have hbase := card_patternBasePairStars_le_order Q S
  exact card_pos.mp (by omega)

end

end Erdos207
