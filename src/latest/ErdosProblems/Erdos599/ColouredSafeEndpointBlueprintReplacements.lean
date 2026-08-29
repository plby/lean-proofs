/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprint
import ErdosProblems.Erdos599.ColouredSafeEndpointFiniteRoofCutSplice
import ErdosProblems.Erdos599.ColouredSafeEndpointInfiniteRoofCutSplice
import ErdosProblems.Erdos599.ColouredSafeAugmentedFullAccounting
import ErdosProblems.Erdos599.ColouredSafeAugmentedPredecessorRefinement

/-!
# Actual finite and infinite replacements of endpoint-pruned blueprints

All six blueprint fields survive the proved roof-cut insertions. The
working region is the limiting roof, so no eligible large hammock is
required to lie in a preselected small closing set. A later small closure
can subsequently be chosen from the actual output carrier by the previous
module. No initial blueprint or global fair history is assumed to exist.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {W : Set (web C).DPath}

theorem IsBlueprint.exists_finiteReplacement (hW : IsBlueprint C a W)
    (ha : a ∈ C.club) {s t : V} (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    {extra : Occurrence (reference C.ladder.limitWarp s (some t)) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t) extra (succ kappa)) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s (some t)) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra ∧
      ∃ (p : FinitePath Gamma.graph) (U : Set (web C).DPath), IsBlueprint C a U ∧
        p.start = s ∧ p.start ≠ p.finish ∧ (p.finish ∈ C.ladder.frontier a ∨ p.finish = t) ∧
        p.edgeSet ⊆ familyEdges U ∧ (familyEdges W \ {(s, t)}) ⊆ familyEdges U ∧
        (web C).vertexSet W ⊆ (web C).vertexSet U ∧
        (web C).initialSet W ⊆ (web C).initialSet U ∧
        (web C).terminalFrontier W ⊆ (web C).terminalFrontier U ∧
        (¬A.HasFiniteSwitchedPathTo t →
          p.finish ∈ C.ladder.frontier a ∧ p.finish ∈ (web C).terminalFrontier U) ∧
        (IsRealTerminal (Gamma := web C) Gamma.graph.Adj W s →
          RealEdges (Gamma := web C) Gamma.graph.Adj W ⊆
            RealEdges (Gamma := web C) Gamma.graph.Adj U ∧
          (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
            IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
          ¬IsRealTerminal (Gamma := web C) Gamma.graph.Adj U s) ∧
        p.support ⊆ (web C).vertexSet U ∧ RealReach Gamma (web C) U s p.finish ∧
        FullAccount Gamma (web C) W U {p.finish} ∧
        SourcePredecessorRefines Gamma (web C) W U ∧
        (p.finish ≠ t → p.finish ∈ (web C).terminalFrontier U) ∧
        (IsRealTerminal (Gamma := web C) Gamma.graph.Adj W s →
          RealAdvance Gamma (web C) W U (C.ladder.frontier a)) ∧
        (web C).vertexSet U ⊆ (web C).vertexSet W ∪ A.referenceClosure := by
  obtain ⟨A, hA, P, p, U, hP, hPfinite, hpP, hps, hpne, hpEnd, hPX, hU,
      hUE, hUV, hUI, hUT, hpE, hpTerminal, hpNondeg, hUcard, hURoof, hUmarked,
      hUterminal, hUcover, hProots, hledger, hPClosure⟩ :=
    C.endpoint_finite_exists_sourceCovered_roofCut_splice (D := web C)
      (real_adj (C := C)) ha hW.isWarp hW.card_vertices hW.vertices_roofed hW.covers_source
      hW.infinitely_many_marked hedge hne hsStrict h
  have hBlueprint : IsBlueprint C a U := of_roofed_fields hU hURoof hUcover hUcard hUmarked (by
    intro x hx
    rcases hUterminal hx with hxOld | hxT
    · exact hW.terminals_popular hxOld
    · exact Or.inr hxT)
  have hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U := by
    rw [hUE]
    exact Set.subset_union_left
  have hV : (web C).vertexSet W ⊆ (web C).vertexSet U := by
    rw [hUV]
    exact Set.subset_union_left
  have hI : (web C).initialSet W ⊆ (web C).initialSet U := by
    rw [hUI]
    exact Set.subset_union_left.trans Set.subset_union_left
  have hT : (web C).terminalFrontier W ⊆ (web C).terminalFrontier U := by
    rw [hUT]
    exact Set.subset_union_left
  have hpV : p.support ⊆ (web C).vertexSet U := by
    rw [hUV]
    exact fun _ hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
  have hreach : RealReach Gamma (web C) U s p.finish :=
    hps ▸ RealReach.of_path p hpV hpE
  have haccount : FullAccount Gamma (web C) W U {p.finish} :=
    fullAccount_of_cut_and_path hW.isWarp hcut (Set.sdiff_subset.trans hT) p hps hpV hpE
  have hpred : SourcePredecessorRefines Gamma (web C) W U :=
    sourcePredecessorRefines_of_twoPortSplice hP hPfinite
      ⟨Sum.inl p, hpP, hps⟩ hProots hedge hPX hUE hUV
  exact ⟨A, hA, p, U, hBlueprint, hps, hpne, hpEnd, hpE, hcut, hV, hI, hT,
    (fun hn ↦ (hpNondeg hn).2), hledger, hpV, hreach, haccount, hpred, hpTerminal,
    (fun hs ↦ ⟨hI, hV, (hledger hs).1, hUterminal⟩), by
      rw [hUV]
      exact Set.union_subset_union_right _ hPClosure⟩

theorem IsBlueprint.exists_infiniteReplacement (hW : IsBlueprint C a W)
    (ha : a ∈ C.club) {s : V} (hsTerminal : s ∈ (web C).terminalFrontier W)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    {extra : Occurrence (reference C.ladder.limitWarp s none) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s none) s none extra (succ kappa)) :
    ∃ (p : FinitePath Gamma.graph) (U : Set (web C).DPath), IsBlueprint C a U ∧
      p.start = s ∧ p.start ≠ p.finish ∧ p.finish ∈ C.ladder.frontier a ∧
      p.finish ∈ (web C).terminalFrontier U ∧ p.edgeSet ⊆ familyEdges U ∧
      familyEdges W ⊆ familyEdges U ∧ (web C).vertexSet W ⊆ (web C).vertexSet U ∧
      (web C).initialSet W ⊆ (web C).initialSet U ∧
      ((web C).terminalFrontier W \ {s}) ⊆ (web C).terminalFrontier U ∧
      RealEdges (Gamma := web C) Gamma.graph.Adj W ⊆
        RealEdges (Gamma := web C) Gamma.graph.Adj U ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
      ¬IsRealTerminal (Gamma := web C) Gamma.graph.Adj U s ∧
      p.support ⊆ (web C).vertexSet U ∧ RealReach Gamma (web C) U s p.finish ∧
      FullAccount Gamma (web C) W U {p.finish} ∧
      SourcePredecessorRefines Gamma (web C) W U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      ∃ A : Occurrence (reference C.ladder.limitWarp s none) s,
        A ∈ goodRoutes (reference C.ladder.limitWarp s none) s none extra ∧
        (web C).vertexSet U ⊆ (web C).vertexSet W ∪ A.referenceClosure := by
  obtain ⟨P, p, U, _hP, _hPfinite, hpP, hps, hpT, hpne, hU,
      hUE, hUV, hUI, hUT, hpE, hpTerminal, hUcard, hURoof, hUmarked, hUterminal, hUcover,
      _hProots, hrealE, hrealT, hsNot, A, hA, hPClosure⟩ :=
    C.endpoint_infinite_exists_sourceCovered_roofCut_splice (D := web C)
      (real_adj (C := C)) ha hW.isWarp hW.card_vertices hW.vertices_roofed hW.covers_source
      hW.infinitely_many_marked hsTerminal hsStrict h
  have hBlueprint : IsBlueprint C a U := of_roofed_fields hU hURoof hUcover hUcard hUmarked (by
    intro x hx
    rcases hUterminal hx with hxOld | hxT
    · exact hW.terminals_popular hxOld.1
    · exact Or.inr hxT)
  have hE : familyEdges W ⊆ familyEdges U := by
    rw [hUE]
    exact Set.subset_union_left
  have hV : (web C).vertexSet W ⊆ (web C).vertexSet U := by
    rw [hUV]
    exact Set.subset_union_left
  have hI : (web C).initialSet W ⊆ (web C).initialSet U := by
    rw [hUI]
    exact Set.subset_union_left
  have hT : (web C).terminalFrontier W \ {s} ⊆ (web C).terminalFrontier U := by
    rw [hUT]
    exact Set.subset_union_left
  have hpV : p.support ⊆ (web C).vertexSet U := by
    rw [hUV]
    exact fun _ hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
  have hreach : RealReach Gamma (web C) U s p.finish :=
    hps ▸ RealReach.of_path p hpV hpE
  have haccount : FullAccount Gamma (web C) W U {p.finish} :=
    fullAccount_of_cut_and_path hW.isWarp (s := s) (t := s)
      (Set.sdiff_subset.trans hE) hT p hps hpV hpE
  have hpred : SourcePredecessorRefines Gamma (web C) W U :=
    sourcePredecessorRefines_of_edge_initial_extension hW.isWarp hU hE hI
  exact ⟨p, U, hBlueprint, hps, hpne, hpT, hpTerminal, hpE, hE, hV, hI, hT,
    hrealE, hrealT, hsNot, hpV, hreach, haccount, hpred,
    ⟨hI, hV, hrealE, hUterminal.trans (Set.union_subset_union_left _ Set.sdiff_subset)⟩,
    A, hA, by
      rw [hUV]
      exact Set.union_subset_union_right _ hPClosure⟩

#print axioms IsBlueprint.exists_finiteReplacement
#print axioms IsBlueprint.exists_infiniteReplacement

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
