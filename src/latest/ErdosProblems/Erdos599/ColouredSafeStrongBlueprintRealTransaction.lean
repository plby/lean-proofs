/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStrongBlueprintTransaction
import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger

/-!
# Strong native blueprint transaction with the real-terminal ledger

This is the combined high-level transaction.  It selects the actual strong
native switch, performs its exact two-port insertion, and proves on the same
output warp both:

* all six conditions of `IsLinkageBlueprint`; and
* retention of every old real edge and every old real terminal other than
  the scheduled source, while the scheduled source acquires a genuine real
  outgoing path and is no longer pending.

Here real means adjacency in the original web `Gamma`; it is not an
arbitrary predicate supplied by the caller.  Non-reality of the cut edge is
derived from the old real-terminal hypothesis, and nontriviality of the new
source path is derived from source exposure and its endpoint on the touched
reference frontier.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The actual finite-end strong transaction, simultaneously carrying its
six blueprint conditions and its original-real-edge ledger. -/
theorem exists_strongBlueprintRealTransaction
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
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
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
      ¬ IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
        Gamma.graph.Adj U s := by
  let G := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(G.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  obtain ⟨A, hA, hARoof, T, hTX, _hsourceX, _hterminalX, _hcompX,
      hTRoof, hEss, hfinish⟩ :=
    C.native_global_hasCard_exists_strongTouchedSwitch_avoiding
      ha hne h hroof hWcard
  have hstageV : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨q, hq, hxq⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨q, hq⟩).1, (E.owner ⟨q, hq⟩).2,
      E.support_subset ⟨q, hq⟩ hxq⟩
  have hs : s ∉ Gamma.vertexSet (C.ladder.warpAt a) :=
    fun hv ↦ hA.2.2.1 (hstageV hv)
  have ht : t ∉ Gamma.vertexSet (C.ladder.warpAt a) :=
    fun hv ↦ hA.2.2.2.1 t rfl (hstageV hv)
  let K : Set G.DPath := liftRealFamily T.paths
  let ps : FinitePath G.graph := T.sourcePath.lift (fun he ↦ Or.inl he)
  let qt : FinitePath G.graph := T.terminalPath.lift (fun he ↦ Or.inl he)
  have hpV : ps.support = T.sourcePath.support := FinitePath.support_lift _ _
  have hqV : qt.support = T.terminalPath.support := FinitePath.support_lift _ _
  have hdistinct : (Sum.inl ps : G.DPath) ≠ Sum.inl qt := by
    intro he
    have heq : ps = qt := Sum.inl.inj he
    have hv : T.sourcePath.support = T.terminalPath.support :=
      hpV.symm.trans ((congrArg FinitePath.support heq).trans hqV)
    exact Set.disjoint_left.mp T.port_supports_disjoint
      T.sourcePath.start_mem_support (hv ▸ T.sourcePath.start_mem_support)
  have hpsK : (Sum.inl ps : G.DPath) ∈ K :=
    ⟨Sum.inl T.sourcePath, T.source_mem, rfl⟩
  have hqtK : (Sum.inl qt : G.DPath) ∈ K :=
    ⟨Sum.inl T.terminalPath, T.terminal_mem, rfl⟩
  have htK : t ∈ G.terminalFrontier K := by
    rw [liftRealFamily_terminalFrontier, T.terminals]
    exact Or.inr (Set.mem_singleton t)
  have hsourceOffTouched :
      s ∉ Gamma.vertexSet (A.retypeStageReference C.legal hARoof).touchedReference := by
    rintro ⟨q, hq, hsq⟩
    exact hs ⟨q, hq.1, hsq⟩
  have hsourceNontrivial : T.sourcePath.start ≠ T.sourcePath.finish :=
    ColouredSafeLocalTransactionRealLedger.Strong.sourcePath_nontrivial_of_source_off
      T hsourceOffTouched
  have hpsNontrivial : ps.start ≠ ps.finish := hsourceNontrivial
  have hpE : ps.edgeSet = T.sourcePath.edgeSet :=
    LinkageBlueprint.walk_edgeSet_lift _ T.sourcePath.walk
  have hpsReal : ∀ e ∈ ps.edgeSet, Gamma.graph.Adj e.1 e.2 := by
    intro e he
    exact T.sourcePath.edgeSet_subset_adj (hpE ▸ he)
  obtain ⟨U, hU, hUE, hUV0, hUI0, hUT0, hpsEdges,
      hrealEdges, hrealTerminals, hsNotReal, htrace⟩ :=
    _root_.Erdos599.ColouredSafeLocalTransactionRealLedger.TwoPort.exists_realLedger
      hW.isWarp (liftRealFamily_isWarp T.isWarp)
      (liftRealFamily_finiteCharacter T.finiteCharacter) hedge ps qt hpsK hqtK
      hdistinct T.source_start T.terminal_finish (by
        change G.vertexSet (liftRealFamily T.paths) ∩ G.vertexSet W ⊆ {s, t}
        rw [liftRealFamily_vertexSet]
        exact hTX) htK hsReal hpsReal hpsNontrivial
  have hUI : G.initialSet U = G.initialSet W ∪ (Gamma.initialSet T.paths \ {s}) := by
    rw [hUI0]
    change G.initialSet W ∪
      (G.initialSet (liftRealFamily T.paths) \ {s}) = _
    rw [liftRealFamily_initialSet]
  have hUT : G.terminalFrontier U =
      G.terminalFrontier W ∪ (Gamma.terminalFrontier T.paths \ {t}) := by
    rw [hUT0]
    change G.terminalFrontier W ∪
      (G.terminalFrontier (liftRealFamily T.paths) \ {t}) = _
    rw [liftRealFamily_terminalFrontier]
  have hUV : G.vertexSet U = G.vertexSet W ∪ Gamma.vertexSet T.paths := by
    rw [hUV0]
    change G.vertexSet W ∪ G.vertexSet (liftRealFamily T.paths) = _
    rw [liftRealFamily_vertexSet]
  have hBlueprint := isLinkageBlueprint_of_stageStrongSwitch C hZ hW hARoof T hs ht
    hTRoof (hclosed A hA.2.2.2.2) hEss hU hUI hUT hUV htrace
  have hSourceEdges : T.sourcePath.edgeSet ⊆ familyEdges U := by
    simpa only [hpE] using hpsEdges
  refine ⟨T.sourcePath, U, T.source_start, hfinish, hSourceEdges, ?_,
    hBlueprint, ?_, ?_, ?_, hrealEdges, hrealTerminals, hsNotReal⟩
  · rw [hUV]
    intro x hx
    exact Or.inr ⟨Sum.inl T.sourcePath, T.source_mem, hx⟩
  · rw [hUI]
    exact Set.subset_union_left
  · rw [hUV]
    exact Set.subset_union_left
  · rw [hUT, T.terminals_sdiff_end ht]
    apply Set.union_subset Set.subset_union_left
    rintro x ⟨q, hq, hqx⟩
    right
    rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq C.legal]
    exact ⟨q, hEss hq, hqx⟩

#print axioms exists_strongBlueprintRealTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
