/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRoofCutFrontierInsertion
import ErdosProblems.Erdos599.ColouredSafeRoofCutConnectorInsertion
import ErdosProblems.Erdos599.ColouredSafeSourceRootedRoofCut

/-!
# The complete finite native roof-cut transaction

An arbitrary successor-sized finite native hammock supplies an actual
pruned rooted stage-roof warp.  Its component at the exposed source is
finite.  The exact terminal bound says that this component either reaches
the stage frontier early or reaches the exposed finite end.  The first
case uses the frontier insertion; the second uses the connector insertion.

No nondegeneracy, uniform roof filter, or explicit source-strictness premise
is imposed.  The result records the alternative and, conditionally on the
connector case, retention of every old edge except the represented cut.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock
open ColouredSafeStageRoofCutRelation ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Resolve an arbitrary finite native hammock by its actual pruned
stage-roof source component. -/
theorem exists_finiteRoofCutBlueprintRealTransaction
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
    (h : HasCard C.ladder.limitWarp s (some t) extra (succ kappa))
    (hclosed : ∀ A, extra A → A.vertexSet ⊆ Z) :
    ∃ (p : FinitePath Gamma.graph)
      (U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath),
      p.start = s ∧
      (p.finish ∈ C.ladder.frontier a ∨ p.finish = t) ∧
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
        Gamma.graph.Adj U s ∧
      (p.finish = t → familyEdges W \ {(s, t)} ⊆ familyEdges U ∧
        (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ⊆
          (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U) ∧
      SourcePredecessorRefines W U ∧ FullAccount W U {p.finish} ∧
      (p.finish ∈ C.ladder.frontier a →
        p.finish ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U) := by
  let G := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(G.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  have hsCarrier : s ∈ G.vertexSet W :=
    (familyEdges_subset_vertexSet_prod W hedge).1
  have hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a) :=
    h.source_mem_strictRoof C.legal (hW.vertices_roofed hsCarrier)
  obtain ⟨A, hA, _hAX, _hAbad, P, hP, hPfinite, hPI, hPT,
      hProof, hPcarrier, _hPclosure, hPX, hPcountable, hPE, _hIrefSource, hPsource⟩ :=
    C.native_global_hasCard_exists_sourceRootedRoofCut ha h hWcard hsStrict (by
      intro x hx
      have hxt : t = x := Option.some.inj hx
      exact hxt ▸ hne)
  have hAclosed : A.vertexSet ⊆ Z := hclosed A hA.2.2.2.2
  have hPT' : Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {t} := by
    intro x hx
    rcases hPT hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Set.mem_singleton_iff.mpr (Option.some.inj hx).symm)
  have hsource : s ∈ Gamma.initialSet P :=
    hPI.symm ▸ Or.inr (Set.mem_singleton s)
  obtain ⟨p0, hpP, hpStart⟩ := hsource
  obtain ⟨p, rfl⟩ := hPfinite hpP
  have hps : p.start = s := hpStart
  have hpTerminal : p.finish ∈ Gamma.terminalFrontier P :=
    ⟨Sum.inl p, hpP, rfl⟩
  have hPavoid : Gamma.vertexSet P ∩ G.vertexSet W ⊆ {s, t} := by
    simpa only [endpoints_some] using hPX
  rcases hPT' hpTerminal with hpFrontier | hpEnd
  · obtain ⟨U, hpEdges, hpSupport, hBlueprint, hIold, hVold, hTerminals,
        hRealEdges, hRealTerminals, hsNotReal, hPred, hAccount, hfinishTerminal⟩ :=
      exists_roofCutFrontierInsertion C hZ hW hne hedge hsReal A hA.1 hA.2.1
        hA.2.2.1 (hA.2.2.2.1 t rfl) hAclosed hP hPfinite hPsource hPI hPT' hProof
        hPcarrier hPcountable hPE hPavoid p hpP hps hpFrontier
    refine ⟨p, U, hps, Or.inl hpFrontier, hpEdges, hpSupport, hBlueprint,
      hIold, hVold, hTerminals, hRealEdges, hRealTerminals, hsNotReal, ?_, hPred,
      hAccount, fun _ ↦ hfinishTerminal⟩
    intro hpt
    exact False.elim (hA.2.2.2.1 t rfl
      (DWeb.KappaLadder.Deferred.frontier_subset_vertexSet_limitWarp C.legal a
        (hpt ▸ hpFrontier)))
  · have hpt : p.finish = t := Set.mem_singleton_iff.mp hpEnd
    obtain ⟨U, hpEdges, hpSupport, hBlueprint, hIold, hVold, hTerminals,
        hRealEdges, hRealTerminals, hsNotReal, hOldEdges, hOldTerminals, hPred, hAccount⟩ :=
      exists_roofCutConnectorInsertion C hZ hW hne hedge hsReal A hA.2.2.1
        hAclosed hP hPfinite hPsource hPI hPT' hProof hPcarrier hPcountable hPavoid
        p hpP hps hpt
    refine ⟨p, U, hps, Or.inr hpt, hpEdges, hpSupport, hBlueprint,
      hIold, hVold, hTerminals, hRealEdges, hRealTerminals, hsNotReal,
      (fun _ ↦ ⟨hOldEdges, hOldTerminals⟩), hPred, hAccount, ?_⟩
    intro hpFrontier
    exact False.elim (hA.2.2.2.1 t rfl
      (DWeb.KappaLadder.Deferred.frontier_subset_vertexSet_limitWarp C.legal a
        (hpt ▸ hpFrontier)))

#print axioms exists_finiteRoofCutBlueprintRealTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
