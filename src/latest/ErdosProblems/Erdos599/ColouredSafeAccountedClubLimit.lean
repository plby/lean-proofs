/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSourceRefinedClubLimit
import ErdosProblems.Erdos599.ColouredSafeAccountedLimit
import ErdosProblems.Erdos599.HalfwayIndexedLadderBoundary

/-!
# Stable native proper limits with genuine target accounting

All native blueprint fields are constructed from a bounded actual history.
The persistent set is the canonical limiting roof boundary, so its target
containment is derived from the ladder rather than added as a graph premise.
The history still has to be produced by the moving-successor construction;
local completion merely to a stage frontier does not satisfy this interface.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain

open Set Cardinal Order DirectedPath Alternating ColouredSafeLocalTransactionRealLedger
open LinkageBlueprint.IndexedTerminalResolutionState.ReachableResolutionRecursor.ResolutionChain

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type u} [LinearOrder I]

theorem target_inter_vertexUnion_subset_limitBoundary
    (G : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    (index : I → Ladder.Stage (succ kappa))
    (R : RealStageChain Gamma G.ladder.limitWarp kappa I
      (fun i ↦ G.ladder.frontier (index i)))
    (hroof : ∀ i, (imaginaryWeb G.ladder.limitWarp kappa).vertexSet (R.stage i) ⊆
      Gamma.roof (G.ladder.frontier (index i))) :
    Gamma.target ∩ R.vertexUnion ⊆ G.ladder.limitRoof \ G.ladder.limitStrictRoof := by
  rintro x ⟨hxB, hxV⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxV
  refine ⟨Set.mem_iUnion.mpr ⟨index i, hroof i hxi⟩, ?_⟩
  intro hxStrict
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxStrict
  exact target_not_mem_strictRoof hxB hxa

/-- The actual stable proper-limit compiler for the native graph. Every
result-producing premise is a verified property of the supplied history,
not a supplied limit blueprint. -/
theorem exists_stableAccountedLimit_at_clubSup
    [Nonempty I]
    (G : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    (hGamma : Gamma.IsNormalized)
    (index : I → Ladder.Stage (succ kappa)) (hmono : Monotone index)
    (hclub : ∀ i, index i ∈ G.club)
    (R : RealStageChain Gamma G.ladder.limitWarp kappa I
      (fun i ↦ G.ladder.frontier (index i)))
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (R.stage i) (R.stage j))
    (haccount : ∀ {i j}, i ≤ j → FullAccount (R.stage i) (R.stage j) Gamma.target)
    (hI : Monotone fun i ↦ (imaginaryWeb G.ladder.limitWarp kappa).initialSet (R.stage i))
    (hindex : #I ≤ kappa) (closed : I → Set V) (Z : Set V)
    (hstage : ∀ i, IsLinkageBlueprint (R.stage i)
      (G.ladder.frontier (index i)) (closed i)
      (G.ladder.limitRoof \ G.ladder.limitStrictRoof))
    (hstable : ∀ i,
      (imaginaryWeb G.ladder.limitWarp kappa).terminalFrontier (R.stage i) ∩
        G.ladder.frontier (index i) ⊆ G.ladder.limitRoof \ G.ladder.limitStrictRoof)
    (hclosed : ∀ i, closed i ⊆ Z) :
    ∃ a ∈ G.club, IsLUB (Set.range index) a ∧
      ∃ U : Set (imaginaryWeb G.ladder.limitWarp kappa).DPath,
        IsLinkageBlueprint U (G.ladder.frontier a) Z
          (G.ladder.limitRoof \ G.ladder.limitStrictRoof) ∧
        ((imaginaryWeb G.ladder.limitWarp kappa).terminalFrontier U ∩
          G.ladder.frontier a ⊆ G.ladder.limitRoof \ G.ladder.limitStrictRoof) ∧
        (imaginaryWeb G.ladder.limitWarp kappa).vertexSet U = R.vertexUnion ∧
        familyEdges U = R.eventualEdges ∧
        ∀ i, (imaginaryWeb G.ladder.limitWarp kappa).initialSet (R.stage i) ⊆
            (imaginaryWeb G.ladder.limitWarp kappa).initialSet U ∧
          SourcePredecessorRefines (R.stage i) U ∧
          FullAccount (R.stage i) U Gamma.target ∧
          RealEdges (Gamma := imaginaryWeb G.ladder.limitWarp kappa)
              Gamma.graph.Adj (R.stage i) ⊆
            RealEdges (Gamma := imaginaryWeb G.ladder.limitWarp kappa)
              Gamma.graph.Adj U := by
  let persistent := G.ladder.limitRoof \ G.ladder.limitStrictRoof
  have hY : Gamma.IsWarp G.ladder.limitWarp :=
    G.legal.warpStages (Ladder.finalStage (succ kappa))
  obtain ⟨a, ha, hLUB, U, hU, hUV, hUE, hcover, hroof, hZ, hcard, hinitials⟩ :=
    exists_structuralLimit_at_clubSup G index hmono hclub R hrefine hI hindex
      closed Z persistent hstage hclosed
  have hB : Gamma.target ∩ R.vertexUnion ⊆ persistent :=
    target_inter_vertexUnion_subset_limitBoundary G index R (fun i ↦ (hstage i).vertices_roofed)
  have hpop := R.eventualWarp_terminals_popular haccount closed persistent
    hstage hstable hB hU hUV hUE
  have hBlueprint : IsLinkageBlueprint U (G.ladder.frontier a) Z persistent := {
    isWarp := hU
    vertices_roofed := hroof
    covers_source := hcover
    vertices_closed := hZ
    card_paths := hcard
    infinitely_many_strong := R.eventualWarp_infinitelyManyStrong hGamma hY haccount
      (fun i ↦ (hstage i).infinitely_many_strong) hUE
    terminals_popular := fun _ hx ↦ Or.inl (hpop hx) }
  refine ⟨a, ha, hLUB, U, hBlueprint, ?_, hUV, hUE, ?_⟩
  · rintro x ⟨hxT, hxa⟩
    have hxV : x ∈ R.vertexUnion := hUV ▸ terminalFrontier_subset_vertexSet U hxT
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxV
    have hno := hxT
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU,
      hUE] at hno
    rcases R.eventual_sink_mem_target_or_stage_terminal haccount hno.2 i hxi with hxB | hxOld
    · exact hB ⟨hxB, hxV⟩
    · apply hstable i
      refine ⟨hxOld, ?_⟩
      exact oldRoof_inter_laterFrontier_subset G.legal (hLUB.1 ⟨i, rfl⟩)
        ⟨(hstage i).vertices_roofed hxi, hxa⟩
  · intro i
    refine ⟨hinitials i, R.sourcePredecessorRefines_eventualWarp hrefine hUV hUE i,
      R.fullAccount_eventualWarp haccount hU hUV hUE i, ?_⟩
    intro e he
    exact ⟨hUE.symm ▸ R.edgeUnion_subset_eventualEdges (R.stage_edges_subset i he), he.2⟩

#print axioms target_inter_vertexUnion_subset_limitBoundary
#print axioms exists_stableAccountedLimit_at_clubSup

end Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain
