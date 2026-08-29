/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointSourceRootedRoofCut
import ErdosProblems.Erdos599.ColouredSafeEndpointPortSplices
import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability
import ErdosProblems.Erdos599.ColouredSafePortEquationsRealLedger

/-!
# Source-covered infinite endpoint replacement without uniform capture

Select an infinite occurrence after protecting the old carrier, take its
actual rooted roof cut, and insert every finite component. The exposed
source component reaches the displayed frontier. Full-reference source
coverage, exact edge and boundary identities, and marked rays are retained.
Only the source, not the whole occurrence, must be strictly roofed.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference ColouredSafeGraphLift
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma D : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_infinite_exists_sourceCovered_roofCut_splice
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {W : Set D.DPath} (hW : D.IsWarp W) (hWcard : #(D.vertexSet W) ≤ kappa)
    (hWRoof : D.vertexSet W ⊆ Gamma.roof (C.ladder.frontier a))
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp (D.vertexSet W)))
    {marked : V → V → Prop} (hmarked : D.InfinitelyManyMarkedEdges W marked)
    {s : V} (hsTerminal : s ∈ D.terminalFrontier W)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    {extra : Occurrence (reference C.ladder.limitWarp s none) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s none) s none extra (succ kappa)) :
    ∃ (P : Set Gamma.DPath) (p : FinitePath Gamma.graph) (U : Set D.DPath),
      Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      (Sum.inl p : Gamma.DPath) ∈ P ∧ p.start = s ∧
      p.finish ∈ C.ladder.frontier a ∧ p.start ≠ p.finish ∧ D.IsWarp U ∧
      familyEdges U = familyEdges W ∪ familyEdges P ∧
      D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet P ∧
      D.initialSet U = D.initialSet W ∪ (Gamma.initialSet P \ {s}) ∧
      D.terminalFrontier U = (D.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier P ∧
      p.edgeSet ⊆ familyEdges U ∧ p.finish ∈ D.terminalFrontier U ∧
      #(D.vertexSet U) ≤ kappa ∧ D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
      D.InfinitelyManyMarkedEdges U marked ∧
      D.terminalFrontier U ⊆ (D.terminalFrontier W \ {s}) ∪ C.ladder.frontier a ∧
      Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
        (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
          referencePathsMeeting C.ladder.limitWarp (D.vertexSet U)) ∧
      Gamma.initialSet P ⊆ Gamma.source ∪ {s} ∧
      RealEdges (Gamma := D) Gamma.graph.Adj W ⊆ RealEdges (Gamma := D) Gamma.graph.Adj U ∧
      (∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := D) Gamma.graph.Adj U x) ∧
      ¬IsRealTerminal (Gamma := D) Gamma.graph.Adj U s ∧
      ∃ A : Occurrence (reference C.ladder.limitWarp s none) s,
        A ∈ goodRoutes (reference C.ladder.limitWarp s none) s none extra ∧
        Gamma.vertexSet P ⊆ A.referenceClosure := by
  obtain ⟨A, hA, P, hP, hPfinite, hPI, hPT0, hPRoof, hPCarrier,
      hPClosure, hPX, hPcountable, _hPE, hProots⟩ :=
    C.endpoint_hasCard_exists_sourceRooted_roofCut ha h hWcard hsStrict (by simp)
  have hPT : Gamma.terminalFrontier P ⊆ C.ladder.frontier a := by
    intro x hx
    rcases hPT0 hx with hx | hx
    · exact hx
    · cases hx
  have hsource : s ∈ Gamma.initialSet P := hPI.symm ▸ Or.inr (Set.mem_singleton s)
  obtain ⟨p0, hp0, hp0s⟩ := hsource
  obtain ⟨p, rfl⟩ := hPfinite hp0
  have hps : p.start = s := hp0s
  have hpT : p.finish ∈ C.ladder.frontier a := hPT ⟨Sum.inl p, hp0, rfl⟩
  have hpne : p.start ≠ p.finish := by
    intro heq
    apply hsStrict.2
    rw [C.ladder.frontiersAreEssential_of_roofsSourceAtStages C.legal.roofsSourceAtStages a]
    exact hps ▸ heq ▸ hpT
  let K : Set D.DPath := liftFamily hAdj P
  let ps : FinitePath D.graph := p.lift hAdj
  have hpsK : (Sum.inl ps : D.DPath) ∈ K := ⟨.inl p, hp0, rfl⟩
  have hKX : D.vertexSet K ∩ D.vertexSet W ⊆ {s} := by
    simpa only [K, liftFamily_vertexSet, endpoints_none] using hPX
  obtain ⟨U, hU, hUE0, hUV0, hUI0, hUT0, hpE0, htrace⟩ :=
    ColouredSafeOnePortSplice.exists_onePortSplice_with_path_exact hW
      (liftFamily_isWarp hAdj hP) (liftFamily_finiteCharacter hAdj hPfinite)
      hsTerminal ps hpsK hps hKX
  have hUE : familyEdges U = familyEdges W ∪ familyEdges P := by
    simpa only [K, liftFamily_edges] using hUE0
  have hUV : D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet P := by
    simpa only [K, liftFamily_vertexSet] using hUV0
  have hUI : D.initialSet U = D.initialSet W ∪ (Gamma.initialSet P \ {s}) := by
    simpa only [K, liftFamily_initialSet] using hUI0
  have hUT : D.terminalFrontier U = (D.terminalFrontier W \ {s}) ∪
      Gamma.terminalFrontier P := by
    simpa only [K, liftFamily_terminalFrontier] using hUT0
  have hpE : p.edgeSet ⊆ familyEdges U := by
    have heq : ps.edgeSet = p.edgeSet := path_edges_lift hAdj (.inl p : Gamma.DPath)
    exact heq ▸ hpE0
  have hends : endpoints s none ⊆ D.vertexSet W := by
    rw [endpoints_none, Set.singleton_subset_iff]
    obtain ⟨q, hq, hqs⟩ := hsTerminal
    exact ⟨q, hq, D.terminal_mem_support hqs⟩
  have hsourceU := ColouredSafeEndpointRoofCut.sourceCondition_of_roofCut
    C.legal A hPRoof hPCarrier hends hcover (by rw [hUI]; exact Set.subset_union_left)
    (by
      intro x hx
      rw [hUI]
      refine Or.inr ⟨hPI.symm ▸ Or.inl hx, ?_⟩
      intro hxs
      obtain ⟨q, hq, hqx⟩ := hx
      exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
        ⟨q, hq.1, hqx ▸ q.initial_mem_support⟩ (Or.inl hxs))
    (le_of_eq hUV)
  have hUcard : #(D.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      hWcard (hPcountable.le_aleph0.trans C.capacity_infinite))
  refine ⟨P, p, U, hP, hPfinite, hp0, hps, hpT, hpne, hU, hUE, hUV, hUI, hUT,
    hpE, ?_, hUcard, ?_, DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace hmarked htrace,
    ?_, hsourceU, hProots, ?_, ?_, ?_, A, hA, hPClosure⟩
  · rw [hUT]
    exact Or.inr ⟨Sum.inl p, hp0, rfl⟩
  · rw [hUV]
    exact Set.union_subset hWRoof hPRoof
  · rw [hUT]
    exact Set.union_subset_union_right _ hPT
  · rintro edge ⟨he, hreal⟩
    exact ⟨hUE.symm ▸ Or.inl he, hreal⟩
  · intro x hx hxs
    exact isRealTerminal_of_onePortEquations hKX
      (by rw [hUV]; exact Set.subset_union_left) (le_of_eq hUE0) hx hxs
  · have hpsReal : ∀ edge ∈ ps.edgeSet, Gamma.graph.Adj edge.1 edge.2 := by
      intro edge he
      have heq : ps.edgeSet = p.edgeSet := path_edges_lift hAdj (.inl p : Gamma.DPath)
      exact p.edgeSet_subset_adj (heq ▸ he)
    exact hps ▸ not_isRealTerminal_of_nontrivial_path ps hpE0 hpsReal hpne

#print axioms endpoint_infinite_exists_sourceCovered_roofCut_splice

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
