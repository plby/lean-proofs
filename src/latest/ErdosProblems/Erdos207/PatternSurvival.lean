/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationTypical
import ErdosProblems.Erdos207.UncoveredPairKernel

/-! # Extension statistics must be tracked only while all base edges survive -/

namespace Erdos207

open Finset

noncomputable section

def PatternUncovered
    {V : Type*} [Fintype V] [DecidableEq V] (Q : SimpleGraph V) (S : GreedyStateOn V) : Prop :=
  ∀ e ∈ graphEdges Q, e ∉ (coveredGraph S.chosen).edgeSet

noncomputable instance patternUncoveredDecidable
    {V : Type*} [Fintype V] [DecidableEq V] (Q : SimpleGraph V) (S : GreedyStateOn V) :
    Decidable (PatternUncovered Q S) := Classical.propDecidable _

theorem GreedyInvariant.available_edge_not_covered
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    {T : TripleOn V} (hT : T ∈ S.available) {e : Sym2 V} (he : e ∈ tripleEdgeFinset T) :
    e ∉ (coveredGraph S.chosen).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hdata := mk_mem_tripleEdgeFinset_iff.mp he
    have hlegal := hS.2.2 T hT
    have havoid := (packing_insert_iff_avoids_coveredGraph hS.1 T hlegal.1).mp hlegal.2.1
    exact havoid u hdata.1 v hdata.2.1 hdata.2.2

theorem iterationExtensionVertices_eq_empty_of_covered_pattern_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) {e : Sym2 V}
    (heQ : e ∈ graphEdges Q) (heC : e ∈ (coveredGraph S.chosen).edgeSet) :
    iterationExtensionVertices S.available Q U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨T, hT, _huT, heT⟩ := (mem_iterationExtensionVertices_iff.mp hu).2 e heQ
  exact hS.available_edge_not_covered hT heT heC

theorem iterationExtensionVertices_nonempty_implies_patternUncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (hU : (iterationExtensionVertices S.available Q U).Nonempty) :
    PatternUncovered Q S := by
  intro e heQ heC
  exact hU.ne_empty (iterationExtensionVertices_eq_empty_of_covered_pattern_edge hS Q U heQ heC)

theorem patternUncovered_greedyStep_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V) (T : TripleOn V) :
    PatternUncovered Q (greedyStep F S T) ↔
      PatternUncovered Q S ∧ Disjoint (graphEdges Q) (tripleEdgeFinset T) := by
  constructor
  · intro h
    refine ⟨?_, disjoint_left.mpr ?_⟩
    · intro e heQ heC
      apply h e heQ
      rw [coveredGraph_edgeSet_eq_biUnion] at heC ⊢
      obtain ⟨R, hR, heR⟩ := mem_biUnion.mp heC
      exact mem_biUnion.mpr ⟨R, mem_insert_of_mem hR, heR⟩
    · intro e heQ heT
      apply h e heQ
      rw [coveredGraph_edgeSet_eq_biUnion]
      exact mem_biUnion.mpr ⟨T, mem_insert_self _ _, heT⟩
  · rintro ⟨h, hdisjoint⟩ e heQ heC
    rw [coveredGraph_edgeSet_eq_biUnion] at heC
    obtain ⟨R, hR, heR⟩ := mem_biUnion.mp heC
    rcases mem_insert.mp hR with rfl | hR
    · exact disjoint_left.mp hdisjoint heQ heR
    · exact h e heQ (by rw [coveredGraph_edgeSet_eq_biUnion]; exact mem_biUnion.mpr ⟨R, hR, heR⟩)

def patternSurvivalSelectors
    {V : Type*} [Fintype V] [DecidableEq V] (Q : SimpleGraph V) (S : GreedyStateOn V) : TripleSystemOn V := by
  classical
  exact S.available.filter fun T ↦ Disjoint (graphEdges Q) (tripleEdgeFinset T)

theorem mem_patternSurvivalSelectors_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) (T : TripleOn V) :
    T ∈ patternSurvivalSelectors Q S ↔ T ∈ S.available ∧ Disjoint (graphEdges Q) (tripleEdgeFinset T) := by
  classical
  simp only [patternSurvivalSelectors, mem_filter]

theorem patternUncovered_greedyStep_iff_selector
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V) (T : TripleOn V)
    (hQ : PatternUncovered Q S) (hT : T ∈ S.available) :
    PatternUncovered Q (greedyStep F S T) ↔ T ∈ patternSurvivalSelectors Q S := by
  classical
  rw [patternUncovered_greedyStep_iff]
  simp only [patternSurvivalSelectors, mem_filter, hQ, hT, true_and]

end

end Erdos207
