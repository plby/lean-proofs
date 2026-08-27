/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyExactAvailability
import ErdosProblems.Erdos207.InitialRootTypicality
import ErdosProblems.Erdos207.OuterSharpCubicSchedule
import ErdosProblems.Erdos207.InitialPowerVortexPackage

/-!
# The initial eligible-pair count

The exact long-phase clock is the number of edges of the ambient remainder
whose endpoints both lie outside the first protected vortex level.  This file
records its elementary cardinal estimates.
-/

namespace Erdos207

open Finset

noncomputable section

lemma outerSharpEligiblePairs_internalOuter_compl_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    outerSharpEligiblePairs (internalOuterGraph G U)ᶜ U 0 =
      (internalOuterEdges G U).card := by
  classical
  letI : DecidableRel (internalOuterGraph G U).Adj := Classical.decRel _
  have hle : (internalOuterEdges G U).card ≤
      Nat.choose (Fintype.card V) 2 := by
    rw [← graphEdges_internalOuterGraph G U, graphEdges_eq_edgeFinset]
    exact SimpleGraph.card_edgeFinset_le_card_choose_two
  unfold outerSharpEligiblePairs
  rw [card_graphEdges_compl_eq_choose_sub,
    graphEdges_internalOuterGraph]
  omega

lemma internalOuterEdges_completeGraph_card
    {V : Type*} [Fintype V] [DecidableEq V] (U : Finset V) :
    (internalOuterEdges (SimpleGraph.completeGraph V) U).card =
      Nat.choose (univ \ U).card 2 := by
  classical
  let O : Finset V := univ \ U
  have hfilter : internalOuterEdges (SimpleGraph.completeGraph V) U =
      (SimpleGraph.completeGraph V).edgeFinset.filter
        (fun e ↦ e.toFinset ⊆ O) := by
    ext e
    simp only [mem_internalOuterEdges_iff, graphEdges_eq_edgeFinset,
      mem_filter, O]
    constructor
    · rintro ⟨he, hfst, hsnd⟩
      refine ⟨he, ?_⟩
      intro v hv
      have hv' := Sym2.mem_toFinset.mp hv
      rw [← e.out_eq] at hv'
      have hvout : v = e.out.1 ∨ v = e.out.2 :=
        Sym2.mem_iff.mp hv'
      rcases hvout with rfl | rfl <;> simp_all
    · rintro ⟨he, hsub⟩
      refine ⟨he, ?_, ?_⟩
      · have := hsub (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e))
        simpa using this
      · have := hsub (Sym2.mem_toFinset.mpr (Sym2.out_snd_mem e))
        simpa using this
  rw [hfilter]
  have hinduce := SimpleGraph.card_filter_edgeFinset_toFinset_subset
    (G := SimpleGraph.completeGraph V) O
  calc
    ((SimpleGraph.completeGraph V).edgeFinset.filter
        (fun e ↦ e.toFinset ⊆ O)).card =
        ((SimpleGraph.completeGraph V).induce (O : Set V)).edgeFinset.card :=
      hinduce
    _ = Nat.choose (Fintype.card O) 2 := by
      let GI := (SimpleGraph.completeGraph V).induce (O : Set V)
      let GO := SimpleGraph.completeGraph O
      have hgraph : GI = GO := by
        exact SimpleGraph.induce_top (O : Set V)
      have hedge : GI.edgeSet = GO.edgeSet := congrArg SimpleGraph.edgeSet hgraph
      calc
        GI.edgeFinset.card = Fintype.card GI.edgeSet :=
          SimpleGraph.edgeFinset_card
        _ = Fintype.card GO.edgeSet :=
          Fintype.card_congr (Equiv.setCongr hedge)
        _ = GO.edgeFinset.card := SimpleGraph.card_edgeSet
        _ = Nat.choose (Fintype.card O) 2 :=
          SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose O.card 2 := by simp

/-- The exact initial eligible budget is at most the complete graph on the
outside vertices. -/
lemma outerSharpEligiblePairs_internalOuter_compl_zero_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    outerSharpEligiblePairs (internalOuterGraph G U)ᶜ U 0 ≤
      Nat.choose (univ \ U).card 2 := by
  rw [outerSharpEligiblePairs_internalOuter_compl_zero]
  rw [← internalOuterEdges_completeGraph_card (U := U)]
  apply card_le_card
  intro e he
  rw [mem_internalOuterEdges_iff] at he ⊢
  exact ⟨by
    apply mem_graphEdges_iff.mpr
    rw [← e.out_eq]
    exact (graph_adj_out_of_mem_graphEdges he.1).ne,
    he.2.1, he.2.2⟩

lemma card_internalOuterEdges_graphDifference_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (U : Finset V) :
    Nat.choose (univ \ U).card 2 - (graphEdges H).card ≤
      (internalOuterEdges
        (graphDifference (SimpleGraph.completeGraph V) H) U).card := by
  classical
  have hEq : internalOuterEdges
      (graphDifference (SimpleGraph.completeGraph V) H) U =
      internalOuterEdges (SimpleGraph.completeGraph V) U \ graphEdges H := by
    ext e
    simp only [mem_internalOuterEdges_iff, mem_sdiff]
    constructor
    · rintro ⟨he, hout⟩
      have hadj := graph_adj_out_of_mem_graphEdges he
      change (SimpleGraph.completeGraph V).Adj e.out.1 e.out.2 ∧
        (e.out.1 ≠ e.out.2 ∧ ¬ H.Adj e.out.1 e.out.2) at hadj
      refine ⟨⟨?_, hout⟩, ?_⟩
      · apply mem_graphEdges_iff.mpr
        rw [← e.out_eq]
        exact hadj.1
      intro hH
      exact hadj.2.2 (graph_adj_out_of_mem_graphEdges hH)
    · rintro ⟨⟨he, hout⟩, hH⟩
      have hadj := graph_adj_out_of_mem_graphEdges he
      have hnot : ¬ H.Adj e.out.1 e.out.2 := by
        intro hAdj
        exact hH (mem_graphEdges_iff.mpr (e.out_eq ▸ hAdj))
      refine ⟨?_, hout⟩
      apply mem_graphEdges_iff.mpr
      rw [← e.out_eq]
      exact ⟨hadj, hadj.ne, hnot⟩
  rw [hEq]
  rw [Finset.card_sdiff (s := graphEdges H)
    (t := internalOuterEdges (SimpleGraph.completeGraph V) U)]
  have hinter :
      (graphEdges H ∩
        internalOuterEdges (SimpleGraph.completeGraph V) U).card ≤
          (graphEdges H).card := card_le_card inter_subset_left
  rw [← internalOuterEdges_completeGraph_card (U := U)]
  omega

/-- Power-vortex specialization: the only eligible outside pairs missing
from the complete outside graph are absorber edges, whose number is bounded
by the square of the packaged absorber support bound. -/
theorem InitialPowerVortexPackage.initialEligiblePairs_lower
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156
    Nat.choose (univ \ U).card 2 - absorberBound ^ 2 ≤
      outerSharpEligiblePairs (internalOuterGraph G U)ᶜ U 0 := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
    (2 * t ^ rootPower) ^ 156
  have hH : (graphEdges P.H).card ≤ absorberBound ^ 2 := by
    calc
      (graphEdges P.H).card ≤ (graphSupportFinset P.H).card ^ 2 :=
        card_graphEdges_le_graphSupportFinset_sq P.H
      _ ≤ absorberBound ^ 2 := Nat.pow_le_pow_left P.graphSupport 2
  rw [outerSharpEligiblePairs_internalOuter_compl_zero]
  exact (Nat.sub_le_sub_left hH _).trans
    (card_internalOuterEdges_graphDifference_lower P.H U)

end

end Erdos207
