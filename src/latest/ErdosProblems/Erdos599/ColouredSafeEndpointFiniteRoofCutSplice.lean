/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointSourceRootedRoofCut
import ErdosProblems.Erdos599.ColouredSafeReferenceRoofCutPorts
import ErdosProblems.Erdos599.ColouredSafeFinitePortSplice
import ErdosProblems.Erdos599.ColouredSafeGraphLift
import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability
import ErdosProblems.Erdos599.ColouredSafePortEquationsRealLedger

/-!
# Actual source-covered finite endpoint replacements without uniform capture

The source component of the protected rooted roof cut either connects the
old endpoints or reaches the cutting frontier. The finite endpoint, if
present, is a genuine terminal port. Insert every component using the
common exact finite-port splice. Full-reference source coverage, the small
roofed carrier and every fixed marked-ray predicate are retained.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference ColouredSafeGraphLift
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma D : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_finite_exists_sourceCovered_roofCut_splice
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {W : Set D.DPath} (hW : D.IsWarp W) (hWcard : #(D.vertexSet W) ≤ kappa)
    (hWRoof : D.vertexSet W ⊆ Gamma.roof (C.ladder.frontier a))
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp (D.vertexSet W)))
    {marked : V → V → Prop} (hmarked : D.InfinitelyManyMarkedEdges W marked)
    {s t : V} (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    {extra : Occurrence (reference C.ladder.limitWarp s (some t)) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t) extra (succ kappa)) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s (some t)) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra ∧
      ∃ (P : Set Gamma.DPath) (p : FinitePath Gamma.graph) (U : Set D.DPath),
        Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧ (Sum.inl p : Gamma.DPath) ∈ P ∧
        p.start = s ∧ p.start ≠ p.finish ∧ (p.finish ∈ C.ladder.frontier a ∨ p.finish = t) ∧
        Gamma.vertexSet P ∩ D.vertexSet W ⊆ {s, t} ∧ D.IsWarp U ∧
        familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges P ∧
        D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet P ∧
        D.initialSet U = (D.initialSet W ∪ (Gamma.initialSet P \ {s})) ∪
          ({t} \ Gamma.vertexSet P) ∧
        D.terminalFrontier U = D.terminalFrontier W ∪ (Gamma.terminalFrontier P \ {t}) ∧
        p.edgeSet ⊆ familyEdges U ∧
        (p.finish ≠ t → p.finish ∈ D.terminalFrontier U) ∧
        (¬A.HasFiniteSwitchedPathTo t → p.finish ≠ t ∧
          p.finish ∈ C.ladder.frontier a ∧ p.finish ∈ D.terminalFrontier U) ∧
        #(D.vertexSet U) ≤ kappa ∧ D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
        D.InfinitelyManyMarkedEdges U marked ∧
        D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a ∧
        Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
          (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
            referencePathsMeeting C.ladder.limitWarp (D.vertexSet U)) ∧
        Gamma.initialSet P ⊆ Gamma.source ∪ {s} ∧
        (IsRealTerminal (Gamma := D) Gamma.graph.Adj W s →
          RealEdges (Gamma := D) Gamma.graph.Adj W ⊆ RealEdges (Gamma := D) Gamma.graph.Adj U ∧
          (∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x → x ≠ s →
            IsRealTerminal (Gamma := D) Gamma.graph.Adj U x) ∧
          ¬IsRealTerminal (Gamma := D) Gamma.graph.Adj U s) ∧
        Gamma.vertexSet P ⊆ A.referenceClosure := by
  obtain ⟨A, hA, P, hP, hPfinite, hPI, hPT0, hPRoof, hPCarrier,
      hPClosure, hPX, hPcountable, hPE, hProots⟩ :=
    C.endpoint_hasCard_exists_sourceRooted_roofCut ha h hWcard hsStrict (by
      intro x hx
      exact Option.some.inj hx ▸ hne)
  have hG : Gamma.IsWarp (reference C.ladder.limitWarp s (some t)) :=
    ColouredSafeEndpointReference.isWarp (C.legal.warpStages (finalStage (succ kappa)))
  have hsource : s ∈ Gamma.initialSet P := hPI.symm ▸ Or.inr (Set.mem_singleton s)
  have hPT : Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {x | A.terminal? = some x} := by
    simpa only [hA.2.1] using hPT0
  have hsNotT : s ∉ C.ladder.frontier a := by
    intro hsT
    apply hsStrict.2
    rw [C.ladder.frontiersAreEssential_of_roofsSourceAtStages C.legal.roofsSourceAtStages a]
    exact hsT
  obtain ⟨p, hpP, hps, hpEnd, hpne, _hpSwitched, hpNotEnd⟩ :=
    ColouredSafeReferenceRoofCut.exists_finite_sourcePort A hPfinite hsource hPT hPE hsNotT
      (fun x hx ↦ Option.some.inj (hA.2.1.symm.trans hx) ▸ hne)
  have hpEnd' : p.finish ∈ C.ladder.frontier a ∨ p.finish = t := by
    rcases hpEnd with hpT | hpEnd
    · exact Or.inl hpT
    · exact Or.inr (Option.some.inj (hpEnd.symm.trans hA.2.1))
  have hhead : t ∈ Gamma.vertexSet P → t ∈ Gamma.terminalFrontier P := by
    apply ColouredSafeReferenceRoofCut.mem_terminalFrontier_of_mem_carrier_at_terminal
      hG A hA.1 hA.2.1 hne
    · intro ht
      exact Set.disjoint_left.mp ColouredSafeEndpointReference.vertexSet_disjoint_endpoints
        ht (Or.inr rfl)
    · exact hP
    · exact hPE
  let K : Set D.DPath := liftFamily hAdj P
  let ps : FinitePath D.graph := p.lift hAdj
  have hpsK : (Sum.inl ps : D.DPath) ∈ K := ⟨.inl p, hpP, rfl⟩
  have hKX : D.vertexSet K ∩ D.vertexSet W ⊆ {s, t} := by
    simpa only [K, liftFamily_vertexSet, endpoints_some] using hPX
  have hKhead : t ∈ D.vertexSet K → t ∈ D.terminalFrontier K := by
    simpa only [K, liftFamily_vertexSet, liftFamily_terminalFrontier] using hhead
  obtain ⟨U, hU, hUE0, hUV0, hUI0, hUT0, hpE0, hpTerminal, htrace⟩ :=
    ColouredSafeFinitePortSplice.exists_finitePortSplice_exact hW
      (liftFamily_isWarp hAdj hP) (liftFamily_finiteCharacter hAdj hPfinite)
      hedge hne ps hpsK hps hKhead hKX
  have hUE : familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges P := by
    simpa only [K, liftFamily_edges] using hUE0
  have hUV : D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet P := by
    simpa only [K, liftFamily_vertexSet] using hUV0
  have hUI : D.initialSet U = (D.initialSet W ∪ (Gamma.initialSet P \ {s})) ∪
      ({t} \ Gamma.vertexSet P) := by
    simpa only [K, liftFamily_initialSet, liftFamily_vertexSet] using hUI0
  have hUT : D.terminalFrontier U = D.terminalFrontier W ∪
      (Gamma.terminalFrontier P \ {t}) := by
    simpa only [K, liftFamily_terminalFrontier] using hUT0
  have hpE : p.edgeSet ⊆ familyEdges U := by
    have heq : ps.edgeSet = p.edgeSet := path_edges_lift hAdj (.inl p : Gamma.DPath)
    exact heq ▸ hpE0
  have hends : endpoints s (some t) ⊆ D.vertexSet W := by
    rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact familyEdges_subset_vertexSet_prod W hedge
  have hsourceU := ColouredSafeEndpointRoofCut.sourceCondition_of_roofCut
    C.legal A hPRoof hPCarrier hends hcover
    (by
      rw [hUI]
      exact Set.subset_union_left.trans Set.subset_union_left)
    (by
      intro x hx
      rw [hUI]
      refine Or.inl (Or.inr ⟨hPI.symm ▸ Or.inl hx, ?_⟩)
      intro hxs
      obtain ⟨q, hq, hqx⟩ := hx
      exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
        ⟨q, hq.1, hqx ▸ q.initial_mem_support⟩ (Or.inl hxs))
    (le_of_eq hUV)
  have hUcard : #(D.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      hWcard (hPcountable.le_aleph0.trans C.capacity_infinite))
  refine ⟨A, hA, P, p, U, hP, hPfinite, hpP, hps, hpne, hpEnd', ?_, hU,
    hUE, hUV, hUI, hUT, hpE, hpTerminal, ?_, hUcard, ?_,
    DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace hmarked htrace, ?_, hsourceU,
    hProots, ?_, hPClosure⟩
  · simpa only [endpoints_some] using hPX
  · intro hnondeg
    have hpt := hpNotEnd t hA.2.1 hnondeg
    exact ⟨hpt, hpEnd'.resolve_right hpt, hpTerminal hpt⟩
  · rw [hUV]
    exact Set.union_subset hWRoof hPRoof
  · rw [hUT]
    apply Set.union_subset Set.subset_union_left
    rintro x ⟨hxP, hxt⟩
    rcases hPT0 hxP with hxT | hxEnd
    · exact Or.inr hxT
    · exact False.elim (hxt (Option.some.inj hxEnd).symm)
  · intro hsReal
    refine ⟨realEdges_subset_of_cut (t := t) hsReal (by
      rw [hUE]
      exact Set.subset_union_left), ?_, ?_⟩
    · intro x hx hxs
      apply isRealTerminal_of_finitePortEquations (liftFamily_isWarp hAdj hP)
        hKhead hKX (by rw [hUV]; exact Set.subset_union_left) ?_ hx hxs
      rw [hUE0]
      exact Set.union_subset_union_left _ Set.sdiff_subset
    · have hpsReal : ∀ edge ∈ ps.edgeSet, Gamma.graph.Adj edge.1 edge.2 := by
        intro edge he
        have heq : ps.edgeSet = p.edgeSet := path_edges_lift hAdj (.inl p : Gamma.DPath)
        exact p.edgeSet_subset_adj (heq ▸ he)
      exact hps ▸ not_isRealTerminal_of_nontrivial_path ps hpE0 hpsReal hpne

#print axioms endpoint_finite_exists_sourceCovered_roofCut_splice

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
