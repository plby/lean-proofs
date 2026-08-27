/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternVerticalThreats
import ErdosProblems.Erdos207.LocalizedTwoAwaySelectedVertices

/-! # The extension jump is bounded by localized two-away counts plus three -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem patternExtensionLoss_subset_localized_vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (T : TripleOn V)
    (hT : T ∈ patternSurvivalSelectors Q S) :
    patternExtensionLoss F Q U S T ⊆ T.1 ∪
      (graphEdges Q).attach.biUnion (fun e ↦
        localizedTwoAwaySelectedVertices F S.chosen T e.1.out.1 e.1.out.2 U) := by
  classical
  intro u hu
  have huY := (mem_sdiff.mp hu).1
  have huout := (mem_properPatternExtensions_iff.mp huY).2
  have hkill : T ∈ patternExtensionKillers F Q U S u := by
    exact mem_filter.mpr ⟨hT, hu⟩
  rw [patternExtensionKillers_eq_vertical_union_twoAway hS Q U u huout huY] at hkill
  rcases mem_union.mp (mem_inter.mp hkill).2 with hvertical | htwo
  · obtain ⟨x, _, hx⟩ := mem_biUnion.mp hvertical
    exact mem_union_left _ ((mem_availableTrianglesContainingPair_iff.mp hx).2 (mem_insert_self _ _))
  · obtain ⟨e, _, he⟩ := mem_biUnion.mp htwo
    have hpartners := mem_twoAwayForbiddenTriangles_comm.mp (mem_inter.mp he).2
    have hends := patternExtensionTriangle_base_mem Q e u huout
    rw [← e.1.out_eq, mk_mem_tripleEdgeFinset_iff] at hends
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨e, mem_attach _ _, mem_localizedTwoAwaySelectedVertices_of_twoAway
      (out_fst_ne_snd_of_mem_graphEdges e.2) hends.1 hends.2.1
      (patternExtensionTriangle_vertex_mem Q e u huout)
      (properPatternExtensions_subset S.available Q U huY) ?_ ?_ hpartners⟩
    · exact fun h ↦ huout (h ▸ (endpoint_mem_graphSupportFinset e.2).1)
    · exact fun h ↦ huout (h ▸ (endpoint_mem_graphSupportFinset e.2).2)

theorem patternExtensionLoss_card_le_localized_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (T : TripleOn V)
    (hT : T ∈ patternSurvivalSelectors Q S) :
    ((patternExtensionLoss F Q U S T).card : ℝ≥0) ≤ 3 +
      ∑ e : graphEdges Q, selectedCount
        (fun w : LocalizedTwoAwayWitness V F T e.1.out.1 e.1.out.2 U ↦ localizedTwoAwayRemainder w) S.chosen := by
  have hnat := (card_le_card (patternExtensionLoss_subset_localized_vertices hS Q U T hT)).trans
    (card_union_le _ _)
  rw [T.2] at hnat
  have hsum : ((patternExtensionLoss F Q U S T).card : ℝ≥0) ≤ 3 +
      ∑ e ∈ (graphEdges Q).attach,
        ((localizedTwoAwaySelectedVertices F S.chosen T e.1.out.1 e.1.out.2 U).card : ℝ≥0) := by
    exact_mod_cast hnat.trans (Nat.add_le_add_left card_biUnion_le 3)
  refine hsum.trans (add_le_add le_rfl ?_)
  rw [← Finset.univ_eq_attach]
  exact sum_le_sum fun e _ ↦ card_localizedTwoAwaySelectedVertices_le_selectedCount F S.chosen T _ _ U

theorem patternExtensionLoss_card_le_localized_cutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (T : TripleOn V)
    (hT : T ∈ patternSurvivalSelectors Q S) (K : ℝ≥0)
    (hK : ∀ e : graphEdges Q, selectedCount
      (fun w : LocalizedTwoAwayWitness V F T e.1.out.1 e.1.out.2 U ↦ localizedTwoAwayRemainder w) S.chosen ≤ K) :
    ((patternExtensionLoss F Q U S T).card : ℝ≥0) ≤ 3 + (graphEdges Q).card * K := by
  refine (patternExtensionLoss_card_le_localized_sum hS Q U T hT).trans ?_
  simpa only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using
    add_le_add (le_rfl : (3 : ℝ≥0) ≤ 3)
      (sum_le_sum (s := (univ : Finset (graphEdges Q))) fun e _ ↦ hK e)

end

end Erdos207
