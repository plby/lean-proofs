/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointFrontierResolution
import ErdosProblems.Erdos599.ColouredSafeEndpointClosedCarrier

/-!
# Carrier-preserving endpoint edge and terminal resolution

Choose large native witnesses inside the successor-closed carrier, then
use the exact reference-closure bound retained by the actual splice.
All previous real-path, accounting, terminal, and predecessor conclusions
hold on the same output, now also certified to stay in that carrier.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeEndpointReference
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {W : Set (web C).DPath} {Z : Set V}

theorem IsBlueprint.exists_nonrealEdge_resolution_within (hW : IsBlueprint C a W)
    (hZ : ClosedCarrier C Z) (hWZ : (web C).vertexSet W ⊆ Z)
    (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    (hedge : (s, t) ∈ familyEdges W) (hn : ¬Gamma.graph.Adj s t) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧ (web C).vertexSet U ⊆ Z ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      ((∃ z ∈ C.ladder.frontier a,
          z ∈ (web C).terminalFrontier U ∧ RealReach Gamma (web C) U s z ∧
          FullAccount Gamma (web C) W U {z}) ∨
        (RealReach Gamma (web C) U s t ∧ FullAccount Gamma (web C) W U {t} ∧
          familyEdges W \ {(s, t)} ⊆ familyEdges U ∧
          (web C).terminalFrontier W ⊆ (web C).terminalFrontier U)) ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  by_cases hsFrontier : s ∈ C.ladder.frontier a
  · obtain ⟨U, hU, hAdvance, hsTerminal, hreach, haccount, hpred, hterms, hUV⟩ :=
      hW.exists_frontierCut hedge hne hn hsFrontier
    exact ⟨U, hU, hUV.subset.trans hWZ, hAdvance,
      Or.inl ⟨s, hsFrontier, hsTerminal, hreach, haccount⟩,
      (fun x hx _ ↦ hterms x hx), hpred⟩
  · have hendsW := familyEdges_subset_vertexSet_prod W hedge
    have hsStrict := strictRoof_of_roof_not_frontier (hW.vertices_roofed hendsW.1) hsFrontier
    have hadj : (web C).graph.Adj s t := familyEdges_subset_adj W hedge
    have hHuge : ColouredSafeEndpointHammock.IsImaginary C.ladder.limitWarp
        (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa s t :=
      hadj.resolve_left hn
    have hends : endpoints s (some t) ⊆ Z := by
      rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hWZ hendsW.1, hWZ hendsW.2⟩
    obtain ⟨A, hA, p, U, hU, _hps, _hpne, hpEnd, _hpE, hcut, _hV, _hI, hT,
        _hpNondeg, hledger, _hpV, hreach, haccount, hpred, hpTerminal, hAdvance,
        hCarrier⟩ :=
      hW.exists_finiteReplacement ha hedge hne hsStrict (hZ.ordinary_hasCard_within hends hHuge)
    have hUZ := hCarrier.trans
      (Set.union_subset hWZ (hZ.referenceClosure_subset A hA.2.2.2.2.2))
    have hsReal := isRealTerminal_of_nonreal_outgoing hW.isWarp hedge hn
    refine ⟨U, hU, hUZ, hAdvance hsReal, ?_, (hledger hsReal).2.1, hpred⟩
    by_cases hpt : p.finish = t
    · exact Or.inr ⟨hpt ▸ hreach, hpt ▸ haccount, hcut, hT⟩
    · exact Or.inl ⟨p.finish, hpEnd.resolve_right hpt, hpTerminal hpt, hreach, haccount⟩

theorem IsBlueprint.exists_terminalOrMarked_resolution_within (hW : IsBlueprint C a W)
    (hZ : ClosedCarrier C Z) (hWZ : (web C).vertexSet W ⊆ Z)
    (ha : a ∈ C.club) (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hend : s ∈ (web C).terminalFrontier W ∨
      ∃ t, (s, t) ∈ familyEdges W ∧ marked C s t) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧ (web C).vertexSet U ⊆ Z ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      (∃ z ∈ C.ladder.frontier a, z ∈ (web C).terminalFrontier U ∧
        RealReach Gamma (web C) U s z ∧ FullAccount Gamma (web C) W U {z}) ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  rcases hend with hterminal | ⟨t, hedge, hmarked⟩
  · have hsV := terminalFrontier_subset_vertexSet W hterminal
    by_cases hsT : s ∈ C.ladder.frontier a
    · exact ⟨W, hW, hWZ, RealAdvance.refl W _,
        ⟨s, hsT, hterminal, RealReach.refl hsV, FullAccount.refl hW.isWarp {s}⟩,
        (fun _ hx _ ↦ hx), SourcePredecessorRefines.refl W⟩
    · have hsRoof := hW.vertices_roofed hsV
      have hsStrict := strictRoof_of_roof_not_frontier hsRoof hsT
      have hpopular := (hW.terminals_popular hterminal).resolve_right hsT
      have hinfinite : HasCard (reference C.ladder.limitWarp s none) s none
          (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s none) (succ kappa) :=
        hpopular.resolve_left (fun hp ↦ hsT (mem_frontier_of_persistent_of_roof hp hsRoof))
      have hends : endpoints s none ⊆ Z := by
        simpa only [endpoints_none, Set.singleton_subset_iff] using hWZ hsV
      obtain ⟨p, U, hU, _hps, _hpne, hpT, hpTerminal, _hpE, _hE, _hV, _hI, _hT,
          _hrealE, hrealT, _hsNot, _hpV, hreach, haccount, hpred, hadvance,
          A, hA, hCarrier⟩ :=
        hW.exists_infiniteReplacement ha hterminal hsStrict
          (hZ.ordinary_hasCard_within hends hinfinite)
      have hUZ := hCarrier.trans
        (Set.union_subset hWZ (hZ.referenceClosure_subset A hA.2.2.2.2.2))
      exact ⟨U, hU, hUZ, hadvance,
        ⟨p.finish, hpT, hpTerminal, hreach, haccount⟩, hrealT, hpred⟩
  · have hnonreal := marked_not_real hinc hmarked
    have hne := marked_ne hmarked
    by_cases hsT : s ∈ C.ladder.frontier a
    · obtain ⟨U, hU, hadvance, hsTerminal, hreach, haccount, hpred, hrealT, hUV⟩ :=
        hW.exists_frontierCut hedge hne hnonreal hsT
      exact ⟨U, hU, hUV.subset.trans hWZ, hadvance,
        ⟨s, hsT, hsTerminal, hreach, haccount⟩,
        (fun x hx _ ↦ hrealT x hx), hpred⟩
    · have hendsW := familyEdges_subset_vertexSet_prod W hedge
      have hsStrict := strictRoof_of_roof_not_frontier (hW.vertices_roofed hendsW.1) hsT
      have hends : endpoints s (some t) ⊆ Z := by
        rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hWZ hendsW.1, hWZ hendsW.2⟩
      obtain ⟨A, hA, p, U, hU, _hps, _hpne, _hpEnd, _hpE, _hcut, _hV, _hI, _hT,
          hpNondeg, hledger, _hpV, hreach, haccount, hpred, _hpTerminal, hAdvance,
          hCarrier⟩ :=
        hW.exists_finiteReplacement ha hedge hne hsStrict
          (hZ.nondegenerate_hasCard_within hends hmarked)
      have hnondeg : ¬A.HasFiniteSwitchedPathTo t := hA.2.2.2.2.1.2
      have hUZ := hCarrier.trans
        (Set.union_subset hWZ (hZ.referenceClosure_subset A hA.2.2.2.2.2))
      have hsReal := isRealTerminal_of_nonreal_outgoing hW.isWarp hedge hnonreal
      exact ⟨U, hU, hUZ, hAdvance hsReal,
        ⟨p.finish, (hpNondeg hnondeg).1, (hpNondeg hnondeg).2, hreach, haccount⟩,
        (hledger hsReal).2.1, hpred⟩

#print axioms IsBlueprint.exists_nonrealEdge_resolution_within
#print axioms IsBlueprint.exists_terminalOrMarked_resolution_within

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
