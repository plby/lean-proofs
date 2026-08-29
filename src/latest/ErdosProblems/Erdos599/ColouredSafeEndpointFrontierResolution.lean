/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointFiniteSkeletonResolution
import ErdosProblems.Erdos599.ColouredSafeEndpointMarkedBoundary
import ErdosProblems.Erdos599.ColouredSafeMarkedForwardSkeleton

/-!
# Actual endpoint-pruned completion to the current frontier

Resolve a finite unmarked forward skeleton and then its full terminal or
marked tail. The endpoint boundary case is an actual edge cut; persistent
vertices are used only after checking current roof membership. Every
completion has a real path to one actual full frontier terminal, together
with the composed full account and original-source predecessor refinement.
No uniform capture or small fixed closing-set premise is imposed.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeEndpointReference
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {W : Set (web C).DPath}

theorem IsBlueprint.exists_terminalOrMarked_resolution (hW : IsBlueprint C a W)
    (ha : a ∈ C.club) (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hend : s ∈ (web C).terminalFrontier W ∨
      ∃ t, (s, t) ∈ familyEdges W ∧ marked C s t) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      (∃ z ∈ C.ladder.frontier a, z ∈ (web C).terminalFrontier U ∧
        RealReach Gamma (web C) U s z ∧ FullAccount Gamma (web C) W U {z}) ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  rcases hend with hterminal | ⟨t, hedge, hmarked⟩
  · have hsV : s ∈ (web C).vertexSet W := terminalFrontier_subset_vertexSet W hterminal
    by_cases hsT : s ∈ C.ladder.frontier a
    · exact ⟨W, hW, RealAdvance.refl W _,
        ⟨s, hsT, hterminal, RealReach.refl hsV, FullAccount.refl hW.isWarp {s}⟩,
        (fun _ hx _ ↦ hx), SourcePredecessorRefines.refl W⟩
    · have hsRoof := hW.vertices_roofed hsV
      have hsStrict := strictRoof_of_roof_not_frontier hsRoof hsT
      have hpopular := (hW.terminals_popular hterminal).resolve_right hsT
      have hinfinite : HasCard (reference C.ladder.limitWarp s none) s none
          (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s none) (succ kappa) :=
        hpopular.resolve_left (fun hp ↦ hsT (mem_frontier_of_persistent_of_roof hp hsRoof))
      obtain ⟨p, U, hU, _hps, _hpne, hpT, hpTerminal, _hpE, _hE, _hV, _hI, _hT,
          _hrealE, hrealT, _hsNot, _hpV, hreach, haccount, hpred, hadvance, _hCarrier⟩ :=
        hW.exists_infiniteReplacement ha hterminal hsStrict hinfinite
      exact ⟨U, hU, hadvance, ⟨p.finish, hpT, hpTerminal, hreach, haccount⟩, hrealT, hpred⟩
  · have hnonreal : ¬Gamma.graph.Adj s t := marked_not_real hinc hmarked
    have hne : s ≠ t := marked_ne hmarked
    by_cases hsT : s ∈ C.ladder.frontier a
    · obtain ⟨U, hU, hadvance, hsTerminal, hreach, haccount, hpred, hrealT, _hUV⟩ :=
        hW.exists_frontierCut hedge hne hnonreal hsT
      exact ⟨U, hU, hadvance, ⟨s, hsT, hsTerminal, hreach, haccount⟩,
        (fun x hx _ ↦ hrealT x hx), hpred⟩
    · have hsV := (familyEdges_subset_vertexSet_prod W hedge).1
      have hsStrict := strictRoof_of_roof_not_frontier (hW.vertices_roofed hsV) hsT
      obtain ⟨A, hA, p, U, hU, _hps, _hpne, _hpEnd, _hpE, _hcut, _hV, _hI, _hT,
          hpNondeg, hledger, _hpV, hreach, haccount, hpred, _hpTerminal, hAdvance,
          _hCarrier⟩ :=
        hW.exists_finiteReplacement ha hedge hne hsStrict hmarked
      have hnondeg : ¬A.HasFiniteSwitchedPathTo t := hA.2.2.2.2.2
      have hsReal := isRealTerminal_of_nonreal_outgoing hW.isWarp hedge hnonreal
      exact ⟨U, hU, hAdvance hsReal,
        ⟨p.finish, (hpNondeg hnondeg).1, (hpNondeg hnondeg).2, hreach, haccount⟩,
        (hledger hsReal).2.1, hpred⟩

/-- Every current carrier vertex has a finite real continuation to one
actual full terminal on the frontier, with the old real-terminal ledger. -/
theorem IsBlueprint.exists_realAdvance_to_frontier (hW : IsBlueprint C a W)
    (ha : a ∈ C.club) (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hs : s ∈ (web C).vertexSet W) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      (∃ z ∈ C.ladder.frontier a, z ∈ (web C).terminalFrontier U ∧
        RealReach Gamma (web C) U s z ∧ FullAccount Gamma (web C) W U {z}) ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x ∨
          RealReaches Gamma (web C) U x (C.ladder.frontier a)) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  obtain ⟨p, hps, hpE, hpUnmarked, hpEnd⟩ :=
    hW.isWarp.exists_unmarkedForwardPath_to_terminal_or_markedTail
      hW.infinitely_many_marked hs
  have hpV : p.support ⊆ (web C).vertexSet W := by
    intro x hx
    by_cases hxs : x = p.start
    · exact (hxs.trans hps).symm ▸ hs
    · obtain ⟨y, hy⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p hx hxs
      exact (familyEdges_subset_vertexSet_prod W (hpE hy)).2
  obtain ⟨U, hU, hadv, hresult, _haccount, hpred⟩ :=
    exists_finiteSkeleton_resolution C ha hW p hpV hpE
  rcases hresult with ⟨hearly, haccountT⟩ |
    ⟨hreachEnd, hAccount, hretain, htermRetain⟩
  · exact ⟨U, hU, hadv, hps ▸ hearly, haccountT, hpred⟩
  · have hendU : p.finish ∈ (web C).terminalFrontier U ∨
        ∃ t, (p.finish, t) ∈ familyEdges U ∧ marked C p.finish t := by
      rcases hpEnd with hpTerm | ⟨t, he, hmark⟩
      · exact Or.inl (htermRetain hpTerm)
      · exact Or.inr ⟨t, hretain ⟨he, fun hp ↦ hpUnmarked _ hp hmark⟩, hmark⟩
    obtain ⟨U', hU', hadv', hfinish, _hterms, hpred'⟩ :=
      hU.exists_terminalOrMarked_resolution ha hinc hendU
    obtain ⟨z, hz, hzTerminal, hfinish, hAccount'⟩ := hfinish
    have hsource := (hreachEnd.mono hadv'.vertices hadv'.edges).trans hfinish
    have hAccountFinal := hAccount.trans_singleton hU.isWarp hAccount'
      hadv.vertices hadv'.vertices hadv'.edges hfinish
    refine ⟨U', hU', hadv.trans hadv',
      ⟨z, hz, hzTerminal, hps ▸ hsource, hAccountFinal⟩, ?_,
      hpred.trans hpred' hadv.vertices hadv'.vertices hadv'.edges⟩
    intro x hx
    exact (hAccountFinal.realTerminal_pending_or_completed hU'.isWarp hx).imp_right
      (fun hdone ↦ hdone.target_mono (Set.singleton_subset_iff.mpr hz))

#print axioms IsBlueprint.exists_terminalOrMarked_resolution
#print axioms IsBlueprint.exists_realAdvance_to_frontier

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
