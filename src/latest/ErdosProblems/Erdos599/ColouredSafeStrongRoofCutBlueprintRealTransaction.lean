/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutSwitch
import ErdosProblems.Erdos599.ColouredSafeStageRoofCutStrictSource
import ErdosProblems.Erdos599.ColouredSafeRoofCutPorts
import ErdosProblems.Erdos599.ColouredSafeRoofCutBlueprint
import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.ColouredSafeOneSidedEdgeRealLedger
import ErdosProblems.Erdos599.ColouredSafeSourceRootedRoofCut
import ErdosProblems.Erdos599.ColouredSafeSourcePredecessorRefinement
import ErdosProblems.Erdos599.ColouredSafeFullAccounting

/-!
# Strong finite native roof-cut transaction with the real ledger

A successor-sized nondegenerate native hammock is selected globally, but
only its actual rooted fixed-stage roof cut is inserted.  If the exposed
finite end survives in that cut, the exact two-port splice is used.  If it
does not, the one-sided splice cuts the old represented edge and leaves its
head as a new initial.  In both cases the same output has all six blueprint
properties, preserves all old real edges and all other old real terminals,
and removes the scheduled source from the real-terminal worklist.

There is no uniform roof hypothesis on the selected global occurrence.
The only roof premise at selection time is that its source is strictly
roofed at the chosen stage.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock
open ColouredSafeStageRoofCutRelation ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The actual finite-end strong roof-cut transaction.  The selected global
occurrence need not be uniformly roofed: only its pruned rooted stage warp
is inserted into the old blueprint. -/
theorem exists_strongRoofCutBlueprintRealTransaction
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} (hne : s ≠ t) (hedge : (s, t) ∈ familyEdges W)
    (hsReal : IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
      Gamma.graph.Adj W s)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    (hclosed : ∀ A, extra A → A.vertexSet ⊆ Z) :
    ∃ (p : FinitePath Gamma.graph)
      (U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath),
      p.start = s ∧ p.finish ∈ C.ladder.frontier a ∧
      p.edgeSet ⊆ familyEdges U ∧
      p.support ⊆ (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ∧
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).initialSet U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∪
          C.ladder.frontier a ∧
      RealEdges (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
        Gamma.graph.Adj W ⊆
        RealEdges (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj U ∧
      (∀ x : V,
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj W x →
          x ≠ s →
          IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj U x) ∧
      ¬IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
        Gamma.graph.Adj U s ∧ SourcePredecessorRefines W U ∧
      FullAccount W U {p.finish} ∧
      p.finish ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U := by
  let G := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(G.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  have hsCarrier : s ∈ G.vertexSet W :=
    (familyEdges_subset_vertexSet_prod W hedge).1
  have hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a) :=
    h.source_mem_strictRoof C.legal (hW.vertices_roofed hsCarrier)
  obtain ⟨A, hA, _hAX, _hAbad, P, hP, hPfinite, hPI, hPT,
      hProof, hPcarrier, hPclosure, hPX, hPcountable, hPE, _hIrefSource, hPsource⟩ :=
    C.native_global_hasCard_exists_sourceRootedRoofCut ha h hWcard hsStrict (by
      intro x hx
      have hxt : t = x := Option.some.inj hx
      exact hxt ▸ hne)
  have hnondeg : ∀ x, A.terminal? = some x → ¬A.HasFiniteSwitchedPathTo x := by
    intro x hx
    have hxt : x = t := Option.some.inj (hx.symm.trans hA.2.1)
    subst x
    exact hA.2.2.2.2.2
  have hsource : s ∈ Gamma.initialSet P :=
    hPI.symm ▸ Or.inr (Set.mem_singleton s)
  have hPTA : Gamma.terminalFrontier P ⊆
      C.ladder.frontier a ∪ {x | A.terminal? = some x} := by
    intro x hx
    rcases hPT hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hA.2.1.trans hx)
  obtain ⟨p, hpP, hps, hpFrontier, hpne, hpSwitched⟩ :=
    exists_source_frontierPath_of_nondegenerate C.legal A hA.2.2.1 hPfinite
      hsource hPTA hPE hnondeg
  let K : Set G.DPath := liftRealFamily P
  let ps : FinitePath G.graph := p.lift (fun he ↦ Or.inl he)
  have hpsK : (Sum.inl ps : G.DPath) ∈ K := ⟨Sum.inl p, hpP, rfl⟩
  have hpE : ps.edgeSet = p.edgeSet :=
    LinkageBlueprint.walk_edgeSet_lift _ p.walk
  have hpsReal : ∀ e ∈ ps.edgeSet, Gamma.graph.Adj e.1 e.2 := by
    intro e he
    exact p.edgeSet_subset_adj (hpE ▸ he)
  have hKX : G.vertexSet K ∩ G.vertexSet W ⊆ {s, t} := by
    change G.vertexSet (liftRealFamily P) ∩ G.vertexSet W ⊆ {s, t}
    rw [liftRealFamily_vertexSet]
    simpa only [endpoints_some] using hPX
  have hIreference : Gamma.initialSet (stageTouchedReference (a := a) A) =
      Gamma.initialSet P \ {s} := by
    exact (roofCut_initials_sdiff_source C.legal A hA.2.2.1 hPI).symm
  have hAclosed : A.vertexSet ⊆ Z := hclosed A hA.2.2.2.2.1
  by_cases htP : t ∈ Gamma.vertexSet P
  · obtain ⟨q, hqP, hqt, hqI⟩ :=
      exists_terminalPort_of_mem_carrier C.legal A hA.1 hA.2.1 hne
        (hA.2.2.2.1 t rfl) hP hPfinite hPI hPE hA.2.2.2.2.2 htP
    have hpq : p ≠ q := by
      intro heq
      subst q
      exact hA.2.2.2.2.2 ⟨p, hps, hqt, hpSwitched⟩
    let qt : FinitePath G.graph := q.lift (fun he ↦ Or.inl he)
    have hqtK : (Sum.inl qt : G.DPath) ∈ K := ⟨Sum.inl q, hqP, rfl⟩
    have hportsDisjoint : Disjoint p.support q.support :=
      hP hpP hqP (fun he ↦ hpq (Sum.inl.inj he))
    have hpV : ps.support = p.support := FinitePath.support_lift _ _
    have hqV : qt.support = q.support := FinitePath.support_lift _ _
    have hdistinct : (Sum.inl ps : G.DPath) ≠ Sum.inl qt := by
      intro he
      have heq : ps = qt := Sum.inl.inj he
      have hv : p.support = q.support :=
        hpV.symm.trans ((congrArg FinitePath.support heq).trans hqV)
      exact Set.disjoint_left.mp hportsDisjoint p.start_mem_support
        (hv ▸ p.start_mem_support)
    have htK : t ∈ G.terminalFrontier K := by
      rw [liftRealFamily_terminalFrontier]
      refine ⟨Sum.inl q, hqP, ?_⟩
      change some q.finish = some t
      rw [hqt]
    obtain ⟨U, hU, hUE, hUV0, hUI0, hUT0, hpsEdges,
        hRealEdges, hRealTerminals, hsNotReal, htrace⟩ :=
      _root_.Erdos599.ColouredSafeLocalTransactionRealLedger.TwoPort.exists_realLedger
        hW.isWarp (liftRealFamily_isWarp hP)
        (liftRealFamily_finiteCharacter hPfinite) hedge ps qt hpsK hqtK
        hdistinct hps hqt hKX htK hsReal hpsReal hpne
    have hUV : G.vertexSet U = G.vertexSet W ∪ Gamma.vertexSet P := by
      rw [hUV0]
      change G.vertexSet W ∪ G.vertexSet (liftRealFamily P) = _
      rw [liftRealFamily_vertexSet]
    have hUI : G.initialSet U = G.initialSet W ∪
        (Gamma.initialSet P \ {s}) := by
      rw [hUI0]
      change G.initialSet W ∪ (G.initialSet (liftRealFamily P) \ {s}) = _
      rw [liftRealFamily_initialSet]
    have hUT : G.terminalFrontier U = G.terminalFrontier W ∪
        (Gamma.terminalFrontier P \ {t}) := by
      rw [hUT0]
      change G.terminalFrontier W ∪
        (G.terminalFrontier (liftRealFamily P) \ {t}) = _
      rw [liftRealFamily_terminalFrontier]
    have hIold : G.initialSet W ⊆ G.initialSet U := by
      rw [hUI]
      exact Set.subset_union_left
    have hIref : Gamma.initialSet (stageTouchedReference (a := a) A) ⊆
        G.initialSet U := by
      rw [hIreference, hUI]
      exact Set.subset_union_right
    have hterminals : G.terminalFrontier U ⊆
        G.terminalFrontier W ∪ C.ladder.frontier a := by
      rw [hUT]
      apply Set.union_subset Set.subset_union_left
      rintro x ⟨hxP, hxt⟩
      rcases hPT hxP with hx | hx
      · exact Or.inr hx
      · exact False.elim (hxt (Option.some.inj hx).symm)
    have hBlueprint := isLinkageBlueprint_of_roofCutInsertion C hZ hW A hAclosed
      hProof hPcarrier hPcountable hU hIold hIref hterminals
      (le_of_eq hUV) htrace
    have hPred : SourcePredecessorRefines W U :=
      sourcePredecessorRefines_of_twoPortSplice hP hPfinite hsource hPsource hedge
        (by simpa only [endpoints_some] using hPX)
        (by simpa only [K, liftRealFamily_familyEdges] using hUE) hUV
    have hAccount : FullAccount W U {p.finish} := by
      refine fullAccount_of_cut_and_path hW.isWarp (s := s) (t := t) ?_ ?_ p hps ?_ ?_
      · rw [hUE]
        exact Set.subset_union_left
      · rw [hUT]
        exact Set.sdiff_subset.trans Set.subset_union_left
      · rw [hUV]
        exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
      · simpa only [hpE] using hpsEdges
    have hfinishTerminal : p.finish ∈ G.terminalFrontier U := by
      rw [hUT]
      refine Or.inr ⟨⟨Sum.inl p, hpP, rfl⟩, ?_⟩
      intro he
      exact hA.2.2.2.1 t rfl
        (DWeb.KappaLadder.Deferred.frontier_subset_vertexSet_limitWarp
          C.legal a (he ▸ hpFrontier))
    refine ⟨p, U, hps, hpFrontier, ?_, ?_, hBlueprint, hIold, ?_, hterminals,
      hRealEdges, hRealTerminals, hsNotReal, hPred, hAccount, hfinishTerminal⟩
    · simpa only [hpE] using hpsEdges
    · rw [hUV]
      exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
    · rw [hUV]
      exact Set.subset_union_left
  · have htK : t ∉ G.vertexSet K := by
      change t ∉ G.vertexSet (liftRealFamily P)
      rw [liftRealFamily_vertexSet]
      exact htP
    have hKXone : G.vertexSet K ∩ G.vertexSet W ⊆ ({s} : Set V) := by
      intro x hx
      rcases Set.mem_insert_iff.mp (hKX hx) with hxs | hxt
      · exact hxs
      · have hxeq : x = t := Set.mem_singleton_iff.mp hxt
        subst x
        exact False.elim (htK hx.1)
    obtain ⟨U, hU, hUE, hUV0, hUI0, hUT0, hpsEdges,
        hRealEdges, hRealTerminals, hsNotReal, htrace⟩ :=
      _root_.Erdos599.ColouredSafeOneSidedEdgeRealLedger.exists_oneSidedEdgeSplice_realLedger
        hW.isWarp (liftRealFamily_isWarp hP)
        (liftRealFamily_finiteCharacter hPfinite) hedge ps hpsK hps htK hKXone
        hsReal hpsReal hpne
    have hUV : G.vertexSet U = G.vertexSet W ∪ Gamma.vertexSet P := by
      rw [hUV0]
      change G.vertexSet W ∪ G.vertexSet (liftRealFamily P) = _
      rw [liftRealFamily_vertexSet]
    have hUI : G.initialSet U =
        (G.initialSet W ∪ (Gamma.initialSet P \ {s})) ∪ {t} := by
      rw [hUI0]
      change (G.initialSet W ∪ (G.initialSet (liftRealFamily P) \ {s})) ∪ {t} = _
      rw [liftRealFamily_initialSet]
    have hUT : G.terminalFrontier U =
        G.terminalFrontier W ∪ Gamma.terminalFrontier P := by
      rw [hUT0]
      change G.terminalFrontier W ∪
        G.terminalFrontier (liftRealFamily P) = _
      rw [liftRealFamily_terminalFrontier]
    have hIold : G.initialSet W ⊆ G.initialSet U := by
      rw [hUI]
      exact Set.subset_union_left.trans Set.subset_union_left
    have hIref : Gamma.initialSet (stageTouchedReference (a := a) A) ⊆
        G.initialSet U := by
      rw [hIreference, hUI]
      exact Set.subset_union_right.trans Set.subset_union_left
    have hterminals : G.terminalFrontier U ⊆
        G.terminalFrontier W ∪ C.ladder.frontier a := by
      rw [hUT]
      apply Set.union_subset Set.subset_union_left
      intro x hxP
      rcases hPT hxP with hx | hx
      · exact Or.inr hx
      · have hxt : x = t := (Option.some.inj hx).symm
        exact False.elim (htP (hxt ▸ terminalFrontier_subset_vertexSet P hxP))
    have hBlueprint := isLinkageBlueprint_of_roofCutInsertion C hZ hW A hAclosed
      hProof hPcarrier hPcountable hU hIold hIref hterminals
      (le_of_eq hUV) htrace
    have hPred : SourcePredecessorRefines W U :=
      sourcePredecessorRefines_of_twoPortSplice hP hPfinite hsource hPsource hedge
        (by simpa only [endpoints_some] using hPX)
        (by simpa only [K, liftRealFamily_familyEdges] using hUE) hUV
    have hAccount : FullAccount W U {p.finish} := by
      refine fullAccount_of_cut_and_path hW.isWarp (s := s) (t := t) ?_ ?_ p hps ?_ ?_
      · rw [hUE]
        exact Set.subset_union_left
      · rw [hUT]
        exact Set.sdiff_subset.trans Set.subset_union_left
      · rw [hUV]
        exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
      · simpa only [hpE] using hpsEdges
    have hfinishTerminal : p.finish ∈ G.terminalFrontier U := by
      rw [hUT]
      exact Or.inr ⟨Sum.inl p, hpP, rfl⟩
    refine ⟨p, U, hps, hpFrontier, ?_, ?_, hBlueprint, hIold, ?_, hterminals,
      hRealEdges, hRealTerminals, hsNotReal, hPred, hAccount, hfinishTerminal⟩
    · simpa only [hpE] using hpsEdges
    · rw [hUV]
      exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
    · rw [hUV]
      exact Set.subset_union_left

#print axioms exists_strongRoofCutBlueprintRealTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
