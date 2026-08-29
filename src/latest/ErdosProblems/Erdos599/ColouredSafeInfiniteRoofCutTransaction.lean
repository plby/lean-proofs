/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutStrictSource
import ErdosProblems.Erdos599.ColouredSafeRoofCutPorts
import ErdosProblems.Erdos599.ColouredSafeRoofCutBlueprint
import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.ColouredSafeSourcePredecessorRefinement
import ErdosProblems.Erdos599.ColouredSafeFullAccounting

/-!
# The infinite native blueprint transaction without uniform roof capture

Choose a global infinite occurrence, cut its actual relation at the fixed
stage roof, and prune to the touched-reference roots plus the scheduled
source. Its finite source component reaches the stage frontier. Inserting
the entire rooted warp preserves all six blueprint conditions and the real
edge/pending-terminal ledger. Source strictness follows from the old
blueprint and the nonempty hammock; the global occurrence is not assumed
to stay in that roof.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock
open ColouredSafeStageRoofCutRelation ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- An actual infinite-hammock continuation, with all six native blueprint
conditions and the real-terminal ledger, without a uniform roof filter. -/
theorem exists_infiniteRoofCutBlueprintRealTransaction
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s : V}
    (hsTerminal : s ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s none extra (succ kappa))
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
        ((imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W \ {s}) ∪
          C.ladder.frontier a ∧
      RealEdges (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
        Gamma.graph.Adj W ⊆
        RealEdges (Gamma := imaginaryWeb C.ladder.limitWarp kappa) Gamma.graph.Adj U ∧
      (∀ x : V,
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj W x → x ≠ s →
          IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj U x) ∧
      ¬IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
        Gamma.graph.Adj U s ∧ SourcePredecessorRefines W U ∧
      FullAccount W U {p.finish} ∧
      p.finish ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(D.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  have hsCarrier : s ∈ D.vertexSet W := by
    obtain ⟨q, hq, hqs⟩ := hsTerminal
    exact ⟨q, hq, D.terminal_mem_support hqs⟩
  have hsStrict := h.source_mem_strictRoof C.legal (hW.vertices_roofed hsCarrier)
  obtain ⟨A, hA, _hAX, _hAbad, K, hK, hKfinite, hKI, hKT,
      hKroof, hKcarrier, _hKclosure, hKX, hKcountable, hKE⟩ :=
    C.native_global_hasCard_exists_prunedRoofCut ha h hWcard hsStrict
      (fun t ht ↦ by cases ht)
  have hKTfrontier : Gamma.terminalFrontier K ⊆ C.ladder.frontier a := by
    simpa using hKT
  have hsource : s ∈ Gamma.initialSet K := hKI.symm ▸ Or.inr (Set.mem_singleton s)
  obtain ⟨p, hpK, hps, hpt, hpne, _hpGlobal⟩ :=
    exists_source_frontierPath_of_nondegenerate C.legal A hA.2.2.1 hKfinite hsource
      (fun x hx ↦ Or.inl (hKTfrontier hx)) hKE
      (fun t ht ↦ by rw [hA.2.1] at ht; cases ht)
  let K' : Set D.DPath := liftRealFamily K
  let p' : FinitePath D.graph := p.lift (fun he ↦ Or.inl he)
  have hp'K : (Sum.inl p' : D.DPath) ∈ K' := ⟨Sum.inl p, hpK, rfl⟩
  have hp'E : p'.edgeSet = p.edgeSet := LinkageBlueprint.walk_edgeSet_lift _ p.walk
  have hp'Real : ∀ e ∈ p'.edgeSet, Gamma.graph.Adj e.1 e.2 := by
    intro e he
    exact p.edgeSet_subset_adj (hp'E ▸ he)
  have hinter : D.vertexSet K' ∩ D.vertexSet W ⊆ {s} := by
    change D.vertexSet (liftRealFamily K) ∩ D.vertexSet W ⊆ {s}
    rw [liftRealFamily_vertexSet]
    simpa only [endpoints_none] using hKX
  have hsReal : IsRealTerminal (Gamma := D) Gamma.graph.Adj W s := by
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq, hqs⟩ := hsTerminal
      exact ⟨q, hq, D.terminal_mem_support hqs⟩
    · rintro ⟨y, hy, _hyReal⟩
      exact (not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
        hW.isWarp hsTerminal) ⟨y, hy⟩
  obtain ⟨U, hU, hUE, hUV0, hUI0, hUT0, hp'UE,
      hRealEdges, hRealTerminals, hsNotReal, htrace⟩ :=
    ColouredSafeLocalTransactionRealLedger.OnePort.exists_realLedger
      hW.isWarp (liftRealFamily_isWarp hK) (liftRealFamily_finiteCharacter hKfinite)
      hsTerminal p' hp'K hps hinter hsReal hp'Real hpne
  have hUV : D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet K := by
    rw [hUV0]
    change D.vertexSet W ∪ D.vertexSet (liftRealFamily K) = _
    rw [liftRealFamily_vertexSet]
  have hUI : D.initialSet U = D.initialSet W ∪
      Gamma.initialSet (stageTouchedReference (a := a) A) := by
    rw [hUI0]
    change D.initialSet W ∪ (D.initialSet (liftRealFamily K) \ {s}) = _
    rw [liftRealFamily_initialSet, roofCut_initials_sdiff_source C.legal A hA.2.2.1 hKI]
  have hUT : D.terminalFrontier U ⊆
      (D.terminalFrontier W \ {s}) ∪ C.ladder.frontier a := by
    rw [hUT0]
    change (D.terminalFrontier W \ {s}) ∪
      D.terminalFrontier (liftRealFamily K) ⊆ _
    rw [liftRealFamily_terminalFrontier]
    exact Set.union_subset Set.subset_union_left
      (hKTfrontier.trans Set.subset_union_right)
  have hIold : D.initialSet W ⊆ D.initialSet U := by
    rw [hUI]
    exact Set.subset_union_left
  have hIreference : Gamma.initialSet (stageTouchedReference (a := a) A) ⊆
      D.initialSet U := by
    rw [hUI]
    exact Set.subset_union_right
  have hterminals : D.terminalFrontier U ⊆
      D.terminalFrontier W ∪ C.ladder.frontier a :=
    hUT.trans (Set.union_subset_union_left _ Set.sdiff_subset)
  have hBlueprint := isLinkageBlueprint_of_roofCutInsertion C hZ hW A
    (hclosed A hA.2.2.2.2) hKroof hKcarrier hKcountable hU hIold hIreference
    hterminals (le_of_eq hUV) htrace
  have hPred : SourcePredecessorRefines W U :=
    sourcePredecessorRefines_of_onePortInsertion hK hsource
      (by simpa only [endpoints_none] using hKX)
      (by simpa only [K', liftRealFamily_familyEdges] using le_of_eq hUE)
  have hAccount : FullAccount W U {p.finish} := by
    refine fullAccount_of_cut_and_path hW.isWarp (s := s) (t := s) ?_ ?_ p hps ?_ ?_
    · rw [hUE]
      exact Set.sdiff_subset.trans Set.subset_union_left
    · rw [hUT0]
      exact Set.subset_union_left
    · rw [hUV]
      exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpK, hx⟩
    · simpa only [hp'E] using hp'UE
  have hfinishTerminal : p.finish ∈ D.terminalFrontier U := by
    rw [hUT0]
    exact Or.inr ⟨Sum.inl p', hp'K, rfl⟩
  refine ⟨p, U, hps, hpt, ?_, ?_, hBlueprint, hIold, ?_, hUT,
    hRealEdges, hRealTerminals, hsNotReal, hPred, hAccount, hfinishTerminal⟩
  · simpa only [hp'E] using hp'UE
  · rw [hUV]
    exact fun x hx ↦ Or.inr ⟨Sum.inl p, hpK, hx⟩
  · rw [hUV]
    exact Set.subset_union_left

#print axioms exists_infiniteRoofCutBlueprintRealTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
