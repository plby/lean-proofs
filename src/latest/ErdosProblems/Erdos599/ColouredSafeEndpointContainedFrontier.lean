/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointContainedResolution

/-!
# Frontier completion inside the closed causal carrier

The finite skeleton induction now retains carrier containment as an actual
invariant. Its terminal or marked-tail completion uses a contained native
replacement on the same output. The resulting frontier terminal therefore
belongs to the carrier on which safe target paths are available.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {W : Set (web C).DPath} {Z : Set V}

theorem IsBlueprint.exists_realAdvance_to_frontier_within (hW : IsBlueprint C a W)
    (hZ : ClosedCarrier C Z) (hWZ : (web C).vertexSet W ⊆ Z)
    (ha : a ∈ C.club) (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hs : s ∈ (web C).vertexSet W) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧ (web C).vertexSet U ⊆ Z ∧
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
  obtain ⟨U, hU, hUZ, hadv, hresult, _haccount, hpred⟩ :=
    exists_finiteSkeleton_resolution_of_invariant C
      (fun U ↦ (web C).vertexSet U ⊆ Z) hW hWZ
      (by
        intro W hU hUZ s t hne he hn
        exact hU.exists_nonrealEdge_resolution_within hZ hUZ ha hne he hn)
      p hpV hpE
  rcases hresult with ⟨hearly, haccountT⟩ |
    ⟨hreachEnd, hAccount, hretain, htermRetain⟩
  · exact ⟨U, hU, hUZ, hadv, hps ▸ hearly, haccountT, hpred⟩
  · have hendU : p.finish ∈ (web C).terminalFrontier U ∨
        ∃ t, (p.finish, t) ∈ familyEdges U ∧ marked C p.finish t := by
      rcases hpEnd with hpTerm | ⟨t, he, hmark⟩
      · exact Or.inl (htermRetain hpTerm)
      · exact Or.inr ⟨t, hretain ⟨he, fun hp ↦ hpUnmarked _ hp hmark⟩, hmark⟩
    obtain ⟨U', hU', hUZ', hadv', hfinish, _hterms, hpred'⟩ :=
      hU.exists_terminalOrMarked_resolution_within hZ hUZ ha hinc hendU
    obtain ⟨z, hz, hzTerminal, hfinish, hAccount'⟩ := hfinish
    have hsource := (hreachEnd.mono hadv'.vertices hadv'.edges).trans hfinish
    have hAccountFinal := hAccount.trans_singleton hU.isWarp hAccount'
      hadv.vertices hadv'.vertices hadv'.edges hfinish
    refine ⟨U', hU', hUZ', hadv.trans hadv',
      ⟨z, hz, hzTerminal, hps ▸ hsource, hAccountFinal⟩, ?_,
      hpred.trans hpred' hadv.vertices hadv'.vertices hadv'.edges⟩
    intro x hx
    exact (hAccountFinal.realTerminal_pending_or_completed hU'.isWarp hx).imp_right
      (fun hdone ↦ hdone.target_mono (Set.singleton_subset_iff.mpr hz))

#print axioms IsBlueprint.exists_realAdvance_to_frontier_within

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
