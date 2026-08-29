/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutStrictSource
import ErdosProblems.Erdos599.ColouredSafeRoofCutPorts
import ErdosProblems.Erdos599.ColouredSafeRoofCutBlueprint
import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.ColouredSafeOneSidedEdgeRealLedger
import ErdosProblems.Erdos599.ColouredSafeSourcePredecessorRefinement
import ErdosProblems.Erdos599.ColouredSafeFullAccounting

/-!
# Inserting an actual roof cut whose source path reaches the frontier

This is the post-selection constructor shared by finite strong and weak
native occurrences.  Its input is the actual rooted finite-character
stage-roof cut, together with one displayed component from the exposed
source to the stage frontier.  It does not assume that the ambient
occurrence is nondegenerate.

If the exposed finite end belongs to the rooted cut, its terminal component
is the second port.  Otherwise the old suffix at the represented edge head
is retained as a new component.  Both branches preserve all six blueprint
conditions and the original-real-edge ledger.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock
open ColouredSafeStageRoofCutRelation ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Insert a concrete pruned roof cut once its exposed source component is
known to reach the stage frontier.  No global nondegeneracy condition on
`A` is used. -/
theorem exists_roofCutFrontierInsertion
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)}
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} (hne : s ≠ t) (hedge : (s, t) ∈ familyEdges W)
    (hsReal : IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
      Gamma.graph.Adj W s)
    (A : Occurrence C.ladder.limitWarp s)
    (hA : Valid A) (hend : A.terminal? = some t)
    (hsOff : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (htOff : t ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hAclosed : A.vertexSet ⊆ Z)
    {P : Set Gamma.DPath}
    (hP : Gamma.IsWarp P) (hPfinite : Gamma.HasFiniteCharacter P)
    (hPsource : Gamma.initialSet P ⊆ Gamma.source ∪ {s})
    (hPI : Gamma.initialSet P =
      Gamma.initialSet (stageTouchedReference (a := a) A) ∪ {s})
    (hPT : Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {t})
    (hProof : Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a))
    (hPcarrier : Gamma.vertexSet P ⊆
      Gamma.vertexSet (stageTouchedReference (a := a) A) ∪ A.vertexSet)
    (hPcountable : (Gamma.vertexSet P).Countable)
    (hPE : familyEdges P ⊆ A.switchedEdges)
    (hPavoid : Gamma.vertexSet P ∩
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ⊆ {s, t})
    (p : FinitePath Gamma.graph)
    (hpP : (Sum.inl p : Gamma.DPath) ∈ P)
    (hps : p.start = s) (hpFrontier : p.finish ∈ C.ladder.frontier a) :
    ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
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
  let K : Set G.DPath := liftRealFamily P
  let ps : FinitePath G.graph := p.lift (fun he ↦ Or.inl he)
  have hpsK : (Sum.inl ps : G.DPath) ∈ K := ⟨Sum.inl p, hpP, rfl⟩
  have hpE : ps.edgeSet = p.edgeSet :=
    LinkageBlueprint.walk_edgeSet_lift _ p.walk
  have hpsReal : ∀ e ∈ ps.edgeSet, Gamma.graph.Adj e.1 e.2 := by
    intro e he
    exact p.edgeSet_subset_adj (hpE ▸ he)
  have hpne : ps.start ≠ ps.finish := by
    intro he
    apply hsOff
    apply DWeb.KappaLadder.Deferred.frontier_subset_vertexSet_limitWarp C.legal a
    exact hps ▸ he ▸ hpFrontier
  have hKavoid : G.vertexSet K ∩ G.vertexSet W ⊆ {s, t} := by
    change G.vertexSet (liftRealFamily P) ∩ G.vertexSet W ⊆ {s, t}
    rw [liftRealFamily_vertexSet]
    exact hPavoid
  have hIreference : Gamma.initialSet (stageTouchedReference (a := a) A) =
      Gamma.initialSet P \ {s} := by
    exact (roofCut_initials_sdiff_source C.legal A hsOff hPI).symm
  have hsP : s ∈ Gamma.initialSet P := ⟨Sum.inl p, hpP, hps⟩
  by_cases htP : t ∈ Gamma.vertexSet P
  · have htTerminal : t ∈ Gamma.terminalFrontier P :=
      mem_terminalFrontier_of_mem_carrier_at_terminal C.legal A hA hend hne htOff
        hP hPE htP
    obtain ⟨q0, hqP, hqt0⟩ := htTerminal
    obtain ⟨q, rfl⟩ := hPfinite hqP
    have hqt : q.finish = t := Option.some.inj hqt0
    have hpq : p ≠ q := by
      intro heq
      subst q
      apply htOff
      apply DWeb.KappaLadder.Deferred.frontier_subset_vertexSet_limitWarp C.legal a
      exact hqt ▸ hpFrontier
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
        hdistinct hps hqt hKavoid htK hsReal hpsReal hpne
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
      · exact False.elim (hxt (Set.mem_singleton_iff.mp hx))
    have hBlueprint := isLinkageBlueprint_of_roofCutInsertion C hZ hW A hAclosed
      hProof hPcarrier hPcountable hU hIold hIref hterminals
      (le_of_eq hUV) htrace
    have hPred : SourcePredecessorRefines W U :=
      sourcePredecessorRefines_of_twoPortSplice hP hPfinite hsP hPsource hedge hPavoid
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
      exact htOff (DWeb.KappaLadder.Deferred.frontier_subset_vertexSet_limitWarp
        C.legal a (he ▸ hpFrontier))
    refine ⟨U, ?_, ?_, hBlueprint, hIold, ?_, hterminals,
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
      rcases Set.mem_insert_iff.mp (hKavoid hx) with hxs | hxt
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
      · have hxt : x = t := Set.mem_singleton_iff.mp hx
        exact False.elim (htP (hxt ▸ terminalFrontier_subset_vertexSet P hxP))
    have hBlueprint := isLinkageBlueprint_of_roofCutInsertion C hZ hW A hAclosed
      hProof hPcarrier hPcountable hU hIold hIref hterminals
      (le_of_eq hUV) htrace
    have hPred : SourcePredecessorRefines W U :=
      sourcePredecessorRefines_of_twoPortSplice hP hPfinite hsP hPsource hedge hPavoid
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
    refine ⟨U, ?_, ?_, hBlueprint, hIold, ?_, hterminals,
      hRealEdges, hRealTerminals, hsNotReal, hPred, hAccount, hfinishTerminal⟩
    · simpa only [hpE] using hpsEdges
    · rw [hUV]
      exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
    · rw [hUV]
      exact Set.subset_union_left

#print axioms exists_roofCutFrontierInsertion

end Erdos599.Blueprint.ColouredSafeShortcutGraph
