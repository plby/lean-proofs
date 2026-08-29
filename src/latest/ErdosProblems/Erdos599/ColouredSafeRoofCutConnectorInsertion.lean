/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRoofCutBlueprint
import ErdosProblems.Erdos599.ColouredSafeConnectorRealLedger
import ErdosProblems.Erdos599.ColouredSafeSourcePredecessorRefinement
import ErdosProblems.Erdos599.ColouredSafeFullAccounting

/-!
# Inserting a roof-cut source component that reaches the old head

This is the connector branch of a finite roof-cut transaction. Its actual
finite source member replaces the represented edge and every other rooted
member is retained as a companion. All old edges except the cut survive;
the six native blueprint conditions and real-terminal ledger hold together.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability
open ColouredSafeStageRoofCutRelation ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Insert a concrete roof-cut connector and all its rooted companions.
The constructor does not assume uniform roofedness of the original word. -/
theorem exists_roofCutConnectorInsertion
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} (hne : s ≠ t) (hedge : (s, t) ∈ familyEdges W)
    (hsReal : IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
      Gamma.graph.Adj W s)
    (A : Occurrence C.ladder.limitWarp s)
    (hsOff : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hAclosed : A.vertexSet ⊆ Z)
    {P : Set Gamma.DPath} (hP : Gamma.IsWarp P)
    (hPfinite : Gamma.HasFiniteCharacter P)
    (hPsource : Gamma.initialSet P ⊆ Gamma.source ∪ {s})
    (hPI : Gamma.initialSet P =
      Gamma.initialSet (stageTouchedReference (a := a) A) ∪ {s})
    (hPT : Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {t})
    (hProof : Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a))
    (hPcarrier : Gamma.vertexSet P ⊆
      Gamma.vertexSet (stageTouchedReference (a := a) A) ∪ A.vertexSet)
    (hPcountable : (Gamma.vertexSet P).Countable)
    (hPavoid : Gamma.vertexSet P ∩
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ⊆ {s, t})
    (p : FinitePath Gamma.graph) (hpP : (Sum.inl p : Gamma.DPath) ∈ P)
    (hps : p.start = s) (hpt : p.finish = t) :
    ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
      p.edgeSet ⊆ familyEdges U ∧
      p.support ⊆ (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ∧
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).initialSet U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∪ C.ladder.frontier a ∧
      RealEdges (Gamma := imaginaryWeb C.ladder.limitWarp kappa) Gamma.graph.Adj W ⊆
        RealEdges (Gamma := imaginaryWeb C.ladder.limitWarp kappa) Gamma.graph.Adj U ∧
      (∀ x : V,
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj W x → x ≠ s →
          IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj U x) ∧
      ¬IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
        Gamma.graph.Adj U s ∧
      familyEdges W \ {(s, t)} ⊆ familyEdges U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ∧
      SourcePredecessorRefines W U ∧ FullAccount W U {p.finish} := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  let K : Set D.DPath := liftRealFamily P
  let ps : FinitePath D.graph := p.lift (fun he ↦ Or.inl he)
  have hpsK : (Sum.inl ps : D.DPath) ∈ K := ⟨Sum.inl p, hpP, rfl⟩
  have hpE : ps.edgeSet = p.edgeSet := LinkageBlueprint.walk_edgeSet_lift _ p.walk
  have hpReal : ∀ e ∈ ps.edgeSet, Gamma.graph.Adj e.1 e.2 := by
    intro e he
    exact p.edgeSet_subset_adj (hpE ▸ he)
  have hKavoid : D.vertexSet K ∩ D.vertexSet W ⊆ {s, t} := by
    change D.vertexSet (liftRealFamily P) ∩ D.vertexSet W ⊆ {s, t}
    rw [liftRealFamily_vertexSet]
    exact hPavoid
  obtain ⟨U, hU, hUI0, hUT0, hUV0, hUE, hpUE,
      hRealEdges, hRealTerminals, hsNotReal, htrace⟩ :=
    ColouredSafeConnectorRealLedger.exists_connectorSplice_realLedger
      hW.isWarp (liftRealFamily_isWarp hP) (liftRealFamily_finiteCharacter hPfinite)
      hedge ps hpsK hps hpt hne hKavoid hsReal hpReal
  have hUV : D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet P := by
    rw [hUV0]
    change D.vertexSet W ∪ D.vertexSet (liftRealFamily P) = _
    rw [liftRealFamily_vertexSet]
  have hUI : D.initialSet U = D.initialSet W ∪
      Gamma.initialSet (stageTouchedReference (a := a) A) := by
    rw [hUI0]
    change D.initialSet W ∪ (D.initialSet (liftRealFamily P) \ {s}) = _
    rw [liftRealFamily_initialSet, roofCut_initials_sdiff_source C.legal A hsOff hPI]
  have hUT : D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a := by
    rw [hUT0]
    change D.terminalFrontier W ∪
      (D.terminalFrontier (liftRealFamily P) \ {t}) ⊆ _
    rw [liftRealFamily_terminalFrontier]
    apply Set.union_subset Set.subset_union_left
    rintro x ⟨hx, hxt⟩
    exact Or.inr ((hPT hx).resolve_right hxt)
  have hIold : D.initialSet W ⊆ D.initialSet U := by
    rw [hUI]
    exact Set.subset_union_left
  have hIref : Gamma.initialSet (stageTouchedReference (a := a) A) ⊆ D.initialSet U := by
    rw [hUI]
    exact Set.subset_union_right
  have htraceFinite : ∀ r : Ray D.graph, Sum.inr r ∈ U →
      ∃ r0 : Ray D.graph, Sum.inr r0 ∈ W ∧
        ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet := by
    intro r hr
    obtain ⟨r0, hr0, hretain⟩ := htrace r hr
    exact ⟨r0, hr0, {(s, t)}, Set.finite_singleton _, hretain⟩
  have hBlueprint := isLinkageBlueprint_of_roofCutInsertion C hZ hW A hAclosed
    hProof hPcarrier hPcountable hU hIold hIref hUT (le_of_eq hUV) htraceFinite
  have hPred : SourcePredecessorRefines W U :=
    sourcePredecessorRefines_of_twoPortSplice hP hPfinite ⟨Sum.inl p, hpP, hps⟩
      hPsource hedge hPavoid
      (by simpa only [K, liftRealFamily_familyEdges] using hUE) hUV
  have hAccount : FullAccount W U {p.finish} := by
    refine fullAccount_of_cut_and_path hW.isWarp (s := s) (t := t) ?_ ?_ p hps ?_ ?_
    · rw [hUE]
      exact Set.subset_union_left
    · rw [hUT0]
      exact Set.sdiff_subset.trans Set.subset_union_left
    · rw [hUV]
      exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
    · simpa only [hpE] using hpUE
  refine ⟨U, ?_, ?_, hBlueprint, hIold, ?_, hUT,
    hRealEdges, hRealTerminals, hsNotReal, ?_, ?_, hPred, hAccount⟩
  · simpa only [hpE] using hpUE
  · rw [hUV]
    exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpP, hx⟩
  · rw [hUV]
    exact Set.subset_union_left
  · rw [hUE]
    exact Set.subset_union_left
  · rw [hUT0]
    exact Set.subset_union_left

#print axioms exists_roofCutConnectorInsertion

end Erdos599.Blueprint.ColouredSafeShortcutGraph
