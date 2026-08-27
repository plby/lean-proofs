/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternExtensionDynamics

/-! # Surviving selectors see vertical pair stars, not base pair stars -/

namespace Erdos207

open Finset

noncomputable section

theorem mem_triplesSharingPair_thirdVertexTriple_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {a b : V} (hab : a ≠ b) (u : ThirdVertex a b) (T : TripleOn V) :
    T ∈ triplesSharingPair (thirdVertexTriple hab u) ↔
      (a ∈ T.1 ∧ b ∈ T.1) ∨ (a ∈ T.1 ∧ u.1 ∈ T.1) ∨ (b ∈ T.1 ∧ u.1 ∈ T.1) := by
  rw [mem_triplesSharingPair_iff]
  by_cases ha : a ∈ T.1 <;> by_cases hb : b ∈ T.1 <;> by_cases hu : u.1 ∈ T.1 <;>
    simp [thirdVertexTriple, tripleOfThree, ha, hb, hu, hab, u.2.1.symm, u.2.2.symm]

def patternVerticalPairStars
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) (u : V) : TripleSystemOn V :=
  (graphSupportFinset Q).biUnion fun x ↦ availableTrianglesContainingPair S {u, x}

def patternTwoAwayThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (u : V) (hu : u ∉ graphSupportFinset Q) : TripleSystemOn V :=
  (graphEdges Q).attach.biUnion fun e ↦ S.available ∩
    twoAwayForbiddenTriangles F S.chosen (patternExtensionTriangle Q e u hu)

theorem pattern_pairSharing_iff_vertical
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (S : GreedyStateOn V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (T : TripleOn V) (hT : T ∈ patternSurvivalSelectors Q S) :
    (∃ e : graphEdges Q, T ∈ triplesSharingPair (patternExtensionTriangle Q e u hu)) ↔
      T ∈ patternVerticalPairStars Q S u := by
  have hdata := (mem_patternSurvivalSelectors_iff Q S T).mp hT
  constructor
  · rintro ⟨e, he⟩
    have hcases := (mem_triplesSharingPair_thirdVertexTriple_iff
      (out_fst_ne_snd_of_mem_graphEdges e.2)
      (⟨u, fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).1),
        fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).2)⟩ : ThirdVertex e.1.out.1 e.1.out.2) T).mp he
    have hbase : ¬ (e.1.out.1 ∈ T.1 ∧ e.1.out.2 ∈ T.1) := by
      rintro ⟨ha, hb⟩
      apply disjoint_left.mp hdata.2 e.2
      rw [← e.1.out_eq, mk_mem_tripleEdgeFinset_iff]
      exact ⟨ha, hb, out_fst_ne_snd_of_mem_graphEdges e.2⟩
    rcases hcases with h | h | h
    · exact (hbase h).elim
    · exact mem_biUnion.mpr ⟨e.1.out.1, (endpoint_mem_graphSupportFinset e.2).1,
        mem_availableTrianglesContainingPair_iff.mpr
          ⟨hdata.1, insert_subset h.2 (singleton_subset_iff.mpr h.1)⟩⟩
    · exact mem_biUnion.mpr ⟨e.1.out.2, (endpoint_mem_graphSupportFinset e.2).2,
        mem_availableTrianglesContainingPair_iff.mpr
          ⟨hdata.1, insert_subset h.2 (singleton_subset_iff.mpr h.1)⟩⟩
  · intro hvertical
    obtain ⟨x, hx, hxT⟩ := mem_biUnion.mp hvertical
    obtain ⟨y, hxy⟩ := mem_graphSupportFinset_iff.mp hx
    have he : s(x, y) ∈ graphEdges Q := mem_graphEdges_iff.mpr hxy
    let e : graphEdges Q := ⟨s(x, y), he⟩
    have hxR : x ∈ (patternExtensionTriangle Q e u hu).1 := by
      have hb := patternExtensionTriangle_base_mem Q e u hu
      exact (mk_mem_tripleEdgeFinset_iff.mp hb).1
    have huR := patternExtensionTriangle_vertex_mem Q e u hu
    have hux : u ≠ x := fun h ↦ hu (h ▸ hx)
    refine ⟨e, mem_triplesSharingPair_iff.mpr ?_⟩
    have hpair : ({u, x} : Finset V).card = 2 := by simp [hux]
    rw [← hpair]
    apply card_le_card
    exact subset_inter (insert_subset huR (singleton_subset_iff.mpr hxR))
      (mem_availableTrianglesContainingPair_iff.mp hxT).2

theorem patternClosedThreats_surviving_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (u : V) (hu : u ∉ graphSupportFinset Q)
    (T : TripleOn V) (hT : T ∈ patternSurvivalSelectors Q S) :
    T ∈ patternExtensionClosedThreats F Q S u hu ↔
      T ∈ patternVerticalPairStars Q S u ∪ patternTwoAwayThreats F Q S u hu := by
  have hTA := ((mem_patternSurvivalSelectors_iff Q S T).mp hT).1
  constructor
  · intro h
    obtain ⟨e, _, he⟩ := mem_biUnion.mp h
    rcases mem_union.mp (mem_inter.mp he).2 with hpair | htwo
    · exact mem_union_left _ ((pattern_pairSharing_iff_vertical Q S u hu T hT).mp ⟨e, hpair⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_attach _ _, mem_inter.mpr ⟨hTA, htwo⟩⟩)
  · intro h
    rcases mem_union.mp h with hpair | htwo
    · obtain ⟨e, he⟩ := (pattern_pairSharing_iff_vertical Q S u hu T hT).mpr hpair
      exact mem_biUnion.mpr ⟨e, mem_attach _ _, mem_inter.mpr ⟨hTA, mem_union_left _ he⟩⟩
    · obtain ⟨e, _, he⟩ := mem_biUnion.mp htwo
      exact mem_biUnion.mpr ⟨e, mem_attach _ _, mem_inter.mpr ⟨hTA, mem_union_right _ (mem_inter.mp he).2⟩⟩

theorem patternExtensionKillers_eq_vertical_union_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (huY : u ∈ properPatternExtensions S.available Q U) :
    patternExtensionKillers F Q U S u = patternSurvivalSelectors Q S ∩
      (patternVerticalPairStars Q S u ∪ patternTwoAwayThreats F Q S u hu) := by
  rw [patternExtensionKillers_eq_inter_closedThreats hS Q U u hu huY]
  ext T
  simp only [mem_inter]
  by_cases hT : T ∈ patternSurvivalSelectors Q S
  · rw [and_iff_right hT, and_iff_right hT]
    exact patternClosedThreats_surviving_iff F Q S u hu T hT
  · simp only [hT, false_and]

end

end Erdos207
