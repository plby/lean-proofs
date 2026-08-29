/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFiniteSkeletonResolution
import ErdosProblems.Erdos599.ColouredSafeMarkedForwardSkeleton
import ErdosProblems.Erdos599.ColouredSafeStrongRoofCutBlueprintRealTransaction
import ErdosProblems.Erdos599.ColouredSafeInfiniteRoofCutTransaction
import ErdosProblems.Erdos599.ColouredSafeNativeNoStrongReal

/-!
# Finite native completion from a carrier vertex to the stage frontier

An actual finite unmarked skeleton ends at a full terminal or a strong
edge. Resolve its finite prefix, then use the genuine infinite or strong
roof-cut transaction. Subdivision incidence makes the strong edge nonreal.
The completed-or-pending terminal ledger is proved through the composition.
No initial blueprint, global closing set, or fair infinite limit is assumed
to have been constructed by this local theorem.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeHammockOmegaClosure
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Every self-connection is degenerate, witnessed by the trivial path. -/
theorem IsStrong.ne {s t : V} (h : IsStrong Y kappa s t) : s ≠ t := by
  intro heq
  subst t
  obtain ⟨H, hH, hcard⟩ := h
  obtain ⟨A, _hAH, hgood, _hdisjoint⟩ :=
    exists_mem_avoiding (X := (∅ : Set V)) hH hcard (by simp)
  apply hgood.2.2.2.2
  refine ⟨FinitePath.trivial Gamma.graph s, rfl, rfl, ?_⟩
  simp [FinitePath.edgeSet, FinitePath.trivial]

/-- Complete the last terminal or strong tail after finite skeleton
resolution. All other intermediate pending real terminals are retained. -/
theorem exists_terminalOrStrong_resolution
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    (hclosed : OmegaClosed C.ladder.limitWarp (succ kappa) Z)
    (hpersistent : persistent ⊆ C.ladder.frontier a)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s : V}
    (hend : s ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∨
      ∃ t, (s, t) ∈ familyEdges W ∧ IsStrong C.ladder.limitWarp kappa s t) :
    ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      RealAdvance W U (C.ladder.frontier a) ∧
      (∃ z ∈ C.ladder.frontier a,
        z ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ∧
        RealReach U s z ∧ FullAccount W U {z}) ∧
      (∀ x, IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj U x) ∧ SourcePredecessorRefines W U := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  rcases hend with hterminal | ⟨t, hedge, hstrong⟩
  · have hsV : s ∈ D.vertexSet W := terminalFrontier_subset_vertexSet W hterminal
    by_cases hsT : s ∈ C.ladder.frontier a
    · exact ⟨W, hW, RealAdvance.refl W _,
        ⟨s, hsT, hterminal, RealReach.refl hsV, FullAccount.refl hW.isWarp {s}⟩,
        (fun _ hx _ ↦ hx), SourcePredecessorRefines.refl W⟩
    · have hpopular := (hW.terminals_popular hterminal).resolve_right hsT
      have hinfinite : HasCard C.ladder.limitWarp s none (fun _ ↦ True) (succ kappa) :=
        hpopular.resolve_left (fun hs ↦ hsT (hpersistent hs))
      have hinside := hclosed.infinite_hasCard_within C.capacity_infinite
        (hW.vertices_closed hsV) hinfinite
      obtain ⟨p, U, hps, hpT, hpE, hpV, hU, hI, hV, hT, hR, hterms, _,
          hPred, hAccount, hfinishTerminal⟩ :=
        exists_infiniteRoofCutBlueprintRealTransaction C ha hZ hW hterminal
          hinside (fun _ h ↦ h)
      have hT' : D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a := by
        intro x hx
        exact (hT hx).imp_left (fun h ↦ h.1)
      exact ⟨U, hU, ⟨hI, hV, hR, hT'⟩,
        ⟨p.finish, hpT, hfinishTerminal, hps ▸ RealReach.of_path p hpV hpE, hAccount⟩,
        hterms, hPred⟩
  · have hY : Gamma.IsWarp C.ladder.limitWarp :=
      C.legal.warpStages (Ladder.finalStage (succ kappa))
    have hnonreal : ¬Gamma.graph.Adj s t :=
      fun hreal ↦ not_isStrong_of_subdivisionIncidence hY (hinc hreal) hstrong
    have hsReal := isRealTerminal_of_nonreal_outgoing hW.isWarp hedge hnonreal
    have htV := (familyEdges_subset_vertexSet_prod W hedge).2
    have hinside : HasCard C.ladder.limitWarp s (some t)
        (fun A ↦ A.vertexSet ⊆ Z ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa) := by
      simpa only [and_comm] using
        (hclosed.nondegenerate_hasCard_within C.capacity_infinite
          (hW.vertices_closed hsReal.1) (hW.vertices_closed htV) hstrong)
    obtain ⟨p, U, hps, hpT, hpE, hpV, hU, hI, hV, hT, hR, hterms, _,
        hPred, hAccount, hfinishTerminal⟩ :=
      exists_strongRoofCutBlueprintRealTransaction C ha hZ hW hstrong.ne hedge
        hsReal hinside (fun _ h ↦ h)
    exact ⟨U, hU, ⟨hI, hV, hR, hT⟩,
      ⟨p.finish, hpT, hfinishTerminal, hps ▸ RealReach.of_path p hpV hpE, hAccount⟩,
      hterms, hPred⟩

/-- Under the actual local geometry, every carrier vertex can be genuinely
real-linked to the frontier by finitely many native transactions. Every
old pending real terminal remains pending or is already real-linked there. -/
theorem exists_realAdvance_to_frontier
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    (hclosed : OmegaClosed C.ladder.limitWarp (succ kappa) Z)
    (hpersistent : persistent ⊆ C.ladder.frontier a)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s : V} (hs : s ∈ (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W) :
    ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      RealAdvance W U (C.ladder.frontier a) ∧
      (∃ z ∈ C.ladder.frontier a,
        z ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ∧
        RealReach U s z ∧ FullAccount W U {z}) ∧
      (∀ x, IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj U x ∨ RealReaches U x (C.ladder.frontier a)) ∧
      SourcePredecessorRefines W U := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  obtain ⟨p, hps, hpE, hpUnmarked, hpEnd⟩ :=
    hW.isWarp.exists_unmarkedForwardPath_to_terminal_or_markedTail
      hW.infinitely_many_strong hs
  have hpV : p.support ⊆ D.vertexSet W := by
    intro x hx
    by_cases hxs : x = p.start
    · exact (hxs.trans hps).symm ▸ hs
    · obtain ⟨y, hy⟩ :=
        Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p hx hxs
      exact (familyEdges_subset_vertexSet_prod W (hpE hy)).2
  obtain ⟨U, hU, hadv, hresult, _haccount, hPred⟩ :=
    exists_finiteSkeleton_resolution C ha hZ hclosed hW p hpV hpE
  rcases hresult with ⟨hearly, haccountT⟩ |
    ⟨hreachEnd, hAccount, hretain, htermRetain⟩
  · exact ⟨U, hU, hadv, hps ▸ hearly, haccountT, hPred⟩
  · have hendU : p.finish ∈ D.terminalFrontier U ∨
        ∃ t, (p.finish, t) ∈ familyEdges U ∧
          IsStrong C.ladder.limitWarp kappa p.finish t := by
      rcases hpEnd with hpTerm | ⟨t, he, hstrong⟩
      · exact Or.inl (htermRetain hpTerm)
      · refine Or.inr ⟨t, hretain ⟨he, ?_⟩, hstrong⟩
        exact fun hp ↦ hpUnmarked _ hp hstrong
    obtain ⟨U', hU', hadv', hfinish, _hterms, hPred'⟩ :=
      exists_terminalOrStrong_resolution C ha hZ hclosed hpersistent hinc hU hendU
    obtain ⟨z, hz, hzTerminal, hfinish, hAccount'⟩ := hfinish
    have hsource := (hreachEnd.mono hadv'.vertices hadv'.edges).trans hfinish
    have hAccountFinal := hAccount.trans_singleton hU.isWarp hAccount'
      hadv.vertices hadv'.vertices hadv'.edges hfinish
    refine ⟨U', hU', hadv.trans hadv',
      ⟨z, hz, hzTerminal, hps ▸ hsource, hAccountFinal⟩, ?_,
      hPred.trans hPred' hadv.vertices hadv'.vertices hadv'.edges⟩
    intro x hx
    exact (hAccountFinal.realTerminal_pending_or_completed hU'.isWarp hx).imp_right
      (fun hdone ↦ hdone.target_mono (Set.singleton_subset_iff.mpr hz))

#print axioms IsStrong.ne
#print axioms exists_terminalOrStrong_resolution
#print axioms exists_realAdvance_to_frontier

end Erdos599.Blueprint.ColouredSafeShortcutGraph
