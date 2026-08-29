/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintSplice
import ErdosProblems.Erdos599.Halfway930OldSliceCut
import ErdosProblems.Erdos599.HalfwayOldStageIntervalSplice

/-!
# The edge-retaining old-slice diamond advance

The canonical inside interval relation records the new ladder segment but
does not, by itself, contain the incoming blueprint edges.  At the scheduled
old-slice terminal there is a simpler source-faithful operation.  The exact
9.30 cut has made the scheduled vertex a terminal.  The selected old-to-new
front leaves the old ladder roof immediately after that vertex, whereas the
whole incoming blueprint is contained in the old roof.  It can therefore be
spliced onto the cut path by the literal `diamond` construction.

This file constructs that splice and retains the exact incoming edge
relation.  The ambient target suffix is still kept external; it is not put
inside the later-frontier roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace IsCutAt

variable {W cut : LinkageBlueprint Gamma Y kappa} {z : V}

/-- Cutting the unique possible outgoing imaginary edge at a real terminal
makes that vertex a terminal of the whole cut blueprint. -/
theorem mem_terminalSet (h : W.IsCutAt cut z)
    (hz : z ∈ cut.realPart.terminals) : z ∈ cut.terminalSet := by
  rcases h with ⟨hzterm, rfl⟩ | ⟨v, hv⟩
  · exact hzterm
  · rw [cut.terminalSet_eq_no_outgoing]
    refine ⟨hz.1, ?_⟩
    rintro ⟨y, hzy⟩
    rw [hv.edges_eq] at hzy
    have hsame : y = v := by
      exact (Alternating.IsWarp.familyEdges_rightUnique W.isWarp)
        hzy.1 hv.edge_mem
    subst y
    exact hzy.2 rfl

end IsCutAt

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

/-- The selected deletion-safe target path meets the complete old ladder
roof only at its initial vertex. -/
theorem oldRoof_inter_path_support_subset
    (T : OldStageIntervalTransaction C z) :
    Gamma.roof C.oldSlice ∩ T.path.support ⊆ {z} := by
  intro x hx
  have hpathLift := T.path_mem_safe
  rw [T.safe.ambient_eq_lift] at hpathLift
  obtain ⟨q, hq, hqeq⟩ := hpathLift
  have hxLift : x ∈
      (C.ladder.liftStagePath C.oldStage q).support := by
    rw [hqeq]
    exact hx.2
  have hxRawRoof : x ∈ Gamma.roof
      (Gamma.terminalFrontier (C.ladder.warpAt C.oldStage)) := by
    rw [← Gamma.roof_essential,
      ← C.ladder.frontier_eq_essential_terminalFrontier
        C.legal.roofsSourceAtStages C.oldStage]
    exact hx.1
  have hxeq : x = z := by
    by_contra hxz
    have hxne : x ≠ q.initial := by
      intro hxq
      apply hxz
      calc
        x = q.initial := hxq
        _ = (C.ladder.liftStagePath C.oldStage q).initial :=
          (C.ladder.initial_liftStagePath C.oldStage q).symm
        _ = T.path.start := congrArg Path.initial hqeq
        _ = z := T.path_start
    exact False.elim
      ((C.ladder.liftStagePath_not_mem_roof_of_ne_initial
        C.oldStage q hxLift hxne) hxRawRoof)
  exact Set.mem_singleton_iff.2 hxeq

/-- Except for its initial vertex, the scheduled front avoids the complete
old ladder roof. -/
theorem oldRoof_inter_front_support_subset
    (T : OldStageIntervalTransaction C z) :
    Gamma.roof C.oldSlice ∩ T.front.support ⊆ {z} := by
  intro x hx
  apply T.oldRoof_inter_path_support_subset
  exact ⟨hx.1, T.front_support_subset_path hx.2⟩

end OldStageIntervalTransaction

/-- The literal scheduled diamond splice. -/
structure OldSliceDiamondAdvance
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {W : LinkageBlueprint Gamma C.selectedReference kappa} {z : V}
    (P : OldSlice930IntervalTransaction C W z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) where
  selectedPrefix : FinitePath
    (imaginaryGraph Gamma C.selectedReference kappa)
  selectedPrefix_mem : (.inl selectedPrefix : Path _) ∈ P.cut.paths
  selectedPrefix_finish : selectedPrefix.finish = z
  fresh : P.cut.vertexSet ∩ P.interval.front.support ⊆ {z}

namespace OldSliceDiamondAdvance

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {z : V} {P : OldSlice930IntervalTransaction C W z}
variable {hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent}

/-- The actual edge-retaining diamond result. -/
def result (Q : OldSliceDiamondAdvance P hW) :
    LinkageBlueprint Gamma C.selectedReference kappa :=
  P.cut.diamond Q.selectedPrefix Q.selectedPrefix_mem P.interval.front
    (P.interval.front_start.trans Q.selectedPrefix_finish.symm) (by
      simpa only [Q.selectedPrefix_finish] using Q.fresh)

/-- The old-roof separation supplies the exact freshness premise of the
blueprint diamond splice. -/
theorem front_fresh :
    W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent →
    P.cut.vertexSet ∩ P.interval.front.support ⊆ {z} := by
  intro hW
  intro x hx
  apply P.interval.oldRoof_inter_front_support_subset
  refine ⟨?_, hx.2⟩
  apply hW.vertices_roofed
  rw [← P.continuation.conclusion.isCutAt.vertexSet_eq]
  exact hx.1

/-- Exact carrier accounting for the scheduled diamond. -/
theorem result_vertexSet_eq (Q : OldSliceDiamondAdvance P hW) :
    Q.result.vertexSet =
      P.cut.vertexSet ∪ P.interval.front.support := by
  exact diamond_vertexSet P.cut Q.selectedPrefix Q.selectedPrefix_mem
    P.interval.front
    (P.interval.front_start.trans Q.selectedPrefix_finish.symm) (by
      simpa only [Q.selectedPrefix_finish] using Q.fresh)

/-- Exact edge accounting for the scheduled diamond. -/
theorem result_edgeSet_eq (Q : OldSliceDiamondAdvance P hW) :
    Q.result.edgeSet =
      P.cut.edgeSet ∪ P.interval.front.edgeSet := by
  exact diamond_edgeSet P.cut Q.selectedPrefix Q.selectedPrefix_mem
    P.interval.front
    (P.interval.front_start.trans Q.selectedPrefix_finish.symm) (by
      simpa only [Q.selectedPrefix_finish] using Q.fresh)

theorem cut_vertexSet_subset_result (Q : OldSliceDiamondAdvance P hW) :
    P.cut.vertexSet ⊆ Q.result.vertexSet := by
  rw [Q.result_vertexSet_eq]
  exact Set.subset_union_left

theorem front_support_subset_result (Q : OldSliceDiamondAdvance P hW) :
    P.interval.front.support ⊆ Q.result.vertexSet := by
  rw [Q.result_vertexSet_eq]
  exact Set.subset_union_right

theorem cut_edgeSet_subset_result (Q : OldSliceDiamondAdvance P hW) :
    P.cut.edgeSet ⊆ Q.result.edgeSet := by
  rw [Q.result_edgeSet_eq]
  exact Set.subset_union_left

theorem front_edgeSet_subset_result (Q : OldSliceDiamondAdvance P hW) :
    P.interval.front.edgeSet ⊆ Q.result.edgeSet := by
  rw [Q.result_edgeSet_eq]
  exact Set.subset_union_right

/-- The scheduled diamond keeps every incoming blueprint vertex. -/
theorem old_vertexSet_subset_result (Q : OldSliceDiamondAdvance P hW) :
    W.vertexSet ⊆ Q.result.vertexSet :=
  P.continuation.real_extends_to_endpoint.vertices_mono.trans
    Q.cut_vertexSet_subset_result

/-- The scheduled diamond keeps every incoming real edge as a real edge. -/
theorem old_realEdges_subset_result_realEdges
    (Q : OldSliceDiamondAdvance P hW) :
    W.realPart.edges ⊆ Q.result.realPart.edges := by
  intro e he
  exact Q.result.mem_realPart_of_mem_edgeSet_of_original
    (Q.cut_edgeSet_subset_result
      (P.continuation.real_extends_to_endpoint.realEdges_mono he).1) he.2

/-- Every scheduled-front edge is a real edge of the result. -/
theorem front_edgeSet_subset_result_realEdges
    (Q : OldSliceDiamondAdvance P hW) :
    P.interval.front.edgeSet ⊆ Q.result.realPart.edges := by
  intro e he
  exact Q.result.mem_realPart_of_mem_edgeSet_of_original
    (Q.front_edgeSet_subset_result he)
    (P.interval.front.edgeSet_subset_adj he)

/-- The scheduled edge-retaining advance exists without any row-containment
assumption on the incoming real edges. -/
theorem exists_diamondAdvance (P : OldSlice930IntervalTransaction C W z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    Nonempty (OldSliceDiamondAdvance P hW) := by
  have hzterm : z ∈ P.cut.terminalSet :=
    P.continuation.conclusion.isCutAt.mem_terminalSet
      P.continuation.endpoint_terminal
  obtain ⟨p, hp, hpterm⟩ := hzterm
  rcases p with p | r
  · have hpfinish : p.finish = z := by
      exact Option.some.inj hpterm
    let hfresh := front_fresh (P := P) hW
    let hstart : P.interval.front.start = p.finish :=
      P.interval.front_start.trans hpfinish.symm
    exact ⟨{
      selectedPrefix := p
      selectedPrefix_mem := hp
      selectedPrefix_finish := hpfinish
      fresh := hfresh }⟩
  · simp at hpterm

end OldSliceDiamondAdvance

#print axioms IsCutAt.mem_terminalSet
#print axioms OldStageIntervalTransaction.oldRoof_inter_front_support_subset
#print axioms OldSliceDiamondAdvance.exists_diamondAdvance

end LinkageBlueprint
end Blueprint
end Erdos599
