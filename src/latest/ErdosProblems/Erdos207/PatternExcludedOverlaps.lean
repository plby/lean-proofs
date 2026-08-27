/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternThreatFamily

/-! # Each extension hazard has small intersection with excluded base stars -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem graphEdge_toFinset_subset_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {Q : SimpleGraph V} {e : Sym2 V} (he : e ∈ graphEdges Q) :
    e.toFinset ⊆ graphSupportFinset Q := by
  intro x hx
  rw [← e.out_eq, Sym2.toFinset_mk_eq] at hx
  rcases mem_insert.mp hx with rfl | hx
  · exact (endpoint_mem_graphSupportFinset he).1
  · exact mem_singleton.mp hx ▸ (endpoint_mem_graphSupportFinset he).2

theorem patternThreatFamily_inter_base_edge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (hpack : ∀ E ∈ F, IsPackingOn E)
    (Q : SimpleGraph V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (K : ℕ) (hK : 1 ≤ K)
    (hpair : ∀ T : TripleOn V, ∀ P : PairOn V,
      selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ K)
    (i : PatternThreatIndex Q) (e : graphEdges Q) :
    (patternThreatFamily F Q S u hu i ∩ availableTrianglesContainingPair S e.1.toFinset).card ≤ K := by
  have hecard : e.1.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e.1
    (Q.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp e.2))
  cases i with
  | inl x =>
    have hux : u ≠ x.1 := fun h ↦ hu (h ▸ x.2)
    have huxcard : ({u, x.1} : Finset V).card = 2 := by simp [hux]
    have hne : ({u, x.1} : Finset V) ≠ e.1.toFinset := by
      intro h
      have humem : u ∈ e.1.toFinset := h ▸ mem_insert_self u {x.1}
      exact hu (graphEdge_toFinset_subset_support e.2 humem)
    have hsub : availableTrianglesContainingPair S {u, x.1} ∩
        availableTrianglesContainingPair S e.1.toFinset ⊆
        universeTriplesContainingPair {u, x.1} ∩ universeTriplesContainingPair e.1.toFinset := by
      intro T hT
      exact mem_inter.mpr
        ⟨mem_universeTriplesContainingPair_iff.mpr
          (mem_availableTrianglesContainingPair_iff.mp (mem_inter.mp hT).1).2,
         mem_universeTriplesContainingPair_iff.mpr
          (mem_availableTrianglesContainingPair_iff.mp (mem_inter.mp hT).2).2⟩
    exact ((card_le_card hsub).trans (card_triplesContaining_distinct_pairs_le_one huxcard hecard hne)).trans hK
  | inr f =>
    let P : PairOn V := ⟨e.1.toFinset, hecard⟩
    have h := (card_pairStar_inter_twoAway_le_selected F S P
      (patternExtensionTriangle Q f u hu) hpack).trans (hpair _ P)
    rw [inter_comm]
    exact_mod_cast h

theorem patternThreatFamily_inter_base_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (hpack : ∀ E ∈ F, IsPackingOn E)
    (Q : SimpleGraph V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (K : ℕ) (hK : 1 ≤ K)
    (hpair : ∀ T : TripleOn V, ∀ P : PairOn V,
      selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ K)
    (i : PatternThreatIndex Q) :
    (patternThreatFamily F Q S u hu i ∩ patternBasePairStars Q S).card ≤ (graphEdges Q).card * K := by
  rw [patternBasePairStars, inter_biUnion]
  refine card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _e ∈ graphEdges Q, K := by
      apply sum_le_sum
      intro e he
      exact patternThreatFamily_inter_base_edge_le F S hpack Q u hu K hK hpair i ⟨e, he⟩
    _ = _ := by simp

end

end Erdos207
