/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointAttachmentBoundary
import ErdosProblems.Erdos599.ColouredSafeOnePortSplice

/-!
# The real target suffix of the endpoint-pruned ordinary extension

The stored suffix meets the actual rooted attachment only at its full terminal.
A literal one-port append retains source coverage and all old edges, and reaches
the ambient target. It is not yet the fair-history successor ledger.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint ColouredSafeMovingStages ColouredSafeGraphLift
open ColouredSafeActivatedPrefixes
open _root_.Erdos599.ColouredSafeAugmentedRealReach
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}
variable {T : NativePostClosureIntervalTransaction C seed z R}

theorem tail_support_subset_closed : T.interval.tail.support ⊆ R.closedSet := by
  intro x hx
  exact T.safe_vertices_closed ⟨.inl T.interval.path, EndpointReferenceAssignment.safe_path_mem,
    T.interval.tail_support_subset_path hx⟩

theorem tail_finish_mem_persistent : T.interval.tail.finish ∈ C.persistent := by
  have hx := tail_support_subset_closed (T := T) T.interval.tail.finish_mem_support
  have hf : T.interval.tail.finish ∈ C.ladder.frontier R.later.stage :=
    _root_.Erdos599.CardinalInduction.SliceSpliceConstructor.target_mem_of_mem_roof
      T.interval.tail_boundary.2 (R.later.subset_roof hx)
  exact (R.frontier_inter ▸ (show T.interval.tail.finish ∈
    R.closedSet ∩ C.ladder.frontier R.later.stage from ⟨hx, hf⟩)).2

theorem currentRoof_tail_inter_subset :
    Gamma.roof C.newSlice ∩ T.interval.tail.support ⊆ {T.interval.tail.start} := by
  rintro x ⟨hxRoof, hxTail⟩
  have hpathLift := EndpointReferenceAssignment.safe_path_mem (T := T)
  rw [T.safe.ambient_eq_lift] at hpathLift
  obtain ⟨q, _hq, hqeq⟩ := hpathLift
  have hxLift : x ∈ (C.ladder.liftStagePath C.newStage q).support := by
    rw [hqeq]
    exact T.interval.tail_support_subset_path hxTail
  have hxRawRoof : x ∈ Gamma.roof
      (Gamma.terminalFrontier (C.ladder.warpAt C.newStage)) := by
    rw [← Gamma.roof_essential, ← C.ladder.frontier_eq_essential_terminalFrontier
      C.legal.roofsSourceAtStages C.newStage]
    exact hxRoof
  have hxInitial : x = T.interval.path.start := by
    by_contra hxne
    have hxneQ : x ≠ q.initial := by
      intro hxeq
      apply hxne
      exact hxeq.trans ((C.ladder.initial_liftStagePath C.newStage q).symm.trans
        (congrArg Path.initial hqeq))
    exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
      C.newStage q hxLift hxneQ) hxRawRoof
  have hxFront : x ∈ T.interval.front.support := by
    have hxf : x = T.interval.front.start := hxInitial.trans
      (T.interval.path_start.trans T.interval.front_start.symm)
    exact hxf.symm ▸ T.interval.front.start_mem_support
  have hpair : x ∈ T.interval.front.support ∩ T.interval.tail.support := ⟨hxFront, hxTail⟩
  rw [T.interval.front_tail_inter] at hpair
  simpa only [← T.interval.tail_start] using hpair

namespace EndpointReferenceAssignment

variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}
variable (A : NativePostClosureIntervalTransaction.EndpointReferenceAssignment T F)

theorem rootedCarrier_tail_inter_subset {K : Set (web C).DPath}
    (hKR : (web C).vertexSet K ⊆ Gamma.roof C.newSlice) :
    RootReachableRelation.carrier (A.attachedEdges K) ((web C).initialSet K) ∩
      T.interval.tail.support ⊆ {T.interval.tail.start} := by
  rintro x ⟨hx, hxTail⟩
  rcases A.attachedCarrier_subset hx with hxK | hxRow
  · exact currentRoof_tail_inter_subset ⟨hKR hxK, hxTail⟩
  · have hxInter : x ∈ Gamma.vertexSet T.interval.ambientInterval ∩
        T.interval.tail.support := ⟨hxRow.1, hxTail⟩
    rw [T.interval.interval_tail_inter] at hxInter
    simpa only [← T.interval.tail_start] using hxInter

/-- Append the actual target suffix, preserving the exact relation data
needed for subsequent terminal accounting. -/
theorem exists_targetBlueprint {W : Set (web C).DPath}
    (hW : IsBlueprint C C.newStage W)
    (hWseed : (web C).vertexSet W ⊆ seed)
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet)
    (hz : z ∈ (web C).terminalFrontier W) :
    let K := seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet
    ∃ Q : Set (web C).DPath, IsBlueprint C R.later.stage Q ∧
      familyEdges Q =
        RootReachableRelation.edges (A.attachedEdges K) ((web C).initialSet K) ∪
          T.interval.tail.edgeSet ∧
      (web C).vertexSet Q =
        RootReachableRelation.carrier (A.attachedEdges K) ((web C).initialSet K) ∪
          T.interval.tail.support ∧
      (web C).initialSet Q = (web C).initialSet K ∧
      (web C).vertexSet W ⊆ (web C).vertexSet Q ∧
      familyEdges W ⊆ familyEdges Q ∧
      (web C).initialSet W ⊆ (web C).initialSet Q ∧
      (web C).vertexSet Q ⊆ R.closedSet ∧
      (web C).terminalFrontier Q ⊆ popular C ∧
      (web C).terminalFrontier Q ∩ C.ladder.frontier R.later.stage ⊆ C.persistent ∧
      RealReaches Gamma (web C) Q z Gamma.target ∧
      (∀ {x y}, y ∈ (web C).vertexSet W → (x, y) ∈ familyEdges Q →
        (x, y) ∈ familyEdges W) := by
  dsimp only
  let K := seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet
  have hKR : (web C).vertexSet K ⊆ Gamma.roof C.newSlice := by
    rw [seedFamily_vertices]
    exact Set.union_subset hW.vertices_roofed (vertices_roofed C.legal)
  obtain ⟨U, hU, hUE, hUV, hUI, hkeepV, hkeepE, hkeepI, hUX, hPop, _hStable,
      _hpV, _hpE, hpT, hpReach, hfresh⟩ := A.exists_sourceCoveredBlueprint hW hWseed hclosed hz
  let p : FinitePath (web C).graph := T.interval.tail.lift (real_adj (C := C))
  let S : Set (web C).DPath := {Sum.inl p}
  have hS : (web C).IsWarp S := by
    intro q hq r hr hne
    exact False.elim (hne ((Set.mem_singleton_iff.mp hq).trans
      (Set.mem_singleton_iff.mp hr).symm))
  have hSf : (web C).HasFiniteCharacter S := by
    rintro q hq
    exact ⟨p, Set.mem_singleton_iff.mp hq⟩
  have hSV : (web C).vertexSet S = T.interval.tail.support := by
    ext x
    simp only [S, DWeb.vertexSet, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      exists_eq_left]
    change x ∈ p.support ↔ x ∈ T.interval.tail.support
    simp only [p, FinitePath.support_lift]
  have hSI : (web C).initialSet S = {T.interval.tail.start} := by
    ext x
    simp only [S, DWeb.initialSet, Set.mem_image, Set.mem_singleton_iff, exists_eq_left]
    exact eq_comm
  have hST : (web C).terminalFrontier S = {T.interval.tail.finish} := by
    ext x
    simp only [S, DWeb.terminalFrontier, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      exists_eq_left, DWeb.terminal?, Path.terminal?_finite, Option.some.injEq]
    exact eq_comm
  have hSE : familyEdges S = T.interval.tail.edgeSet := by
    have hSp : familyEdges S = p.edgeSet := by simp [S, familyEdges]
    exact hSp.trans (path_edges_lift (real_adj (C := C)) (.inl T.interval.tail))
  have hinter : (web C).vertexSet S ∩ (web C).vertexSet U ⊆
      {T.interval.front.finish} := by
    rw [hSV, hUV, Set.inter_comm, ← T.interval.tail_start]
    exact A.rootedCarrier_tail_inter_subset hKR
  obtain ⟨Q, hQ, hQE0, hQV0, hQI0, hQT0, hpQE, htrace⟩ :=
    ColouredSafeOnePortSplice.exists_onePortSplice_with_path_exact hU.isWarp hS hSf hpT p
      (Set.mem_singleton _) T.interval.tail_start hinter
  have hQE : familyEdges Q = familyEdges U ∪ T.interval.tail.edgeSet := by
    simpa only [hSE] using hQE0
  have hQV : (web C).vertexSet Q = (web C).vertexSet U ∪ T.interval.tail.support := by
    simpa only [hSV] using hQV0
  have hQI : (web C).initialSet Q = (web C).initialSet U := by
    simpa only [hSI, T.interval.tail_start, Set.sdiff_self, Set.union_empty] using hQI0
  have hQT : (web C).terminalFrontier Q =
      ((web C).terminalFrontier U \ {T.interval.front.finish}) ∪ {T.interval.tail.finish} := by
    simpa only [hST] using hQT0
  have hUQ : (web C).vertexSet U ⊆ (web C).vertexSet Q := by
    rw [hQV]
    exact Set.subset_union_left
  have hUQE : familyEdges U ⊆ familyEdges Q := by
    rw [hQE]
    exact Set.subset_union_left
  have hQX : (web C).vertexSet Q ⊆ R.closedSet := by
    rw [hQV]
    exact Set.union_subset hUX tail_support_subset_closed
  have hPI : Gamma.initialSet
      (prefixes C.ladder C.newStage ((web C).vertexSet W) R.closedSet) ⊆
        (web C).initialSet Q := by
    rw [hQI, hUI, seedFamily_initials]
    exact Set.subset_union_right
  have hWI : (web C).initialSet W ⊆ (web C).initialSet Q := by
    rw [hQI]
    exact hkeepI
  have hlost : referencePathsMeeting C.ladder.limitWarp C.newSlice \
      referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier R.later.stage) ⊆
        referencePathsMeeting C.ladder.limitWarp R.closedSet := by
    intro q hq
    exact ⟨hq.1.1, q.initial, q.initial_mem_support,
      R.difference_subset ⟨q, Or.inl hq, q.initial_mem_support⟩⟩
  have hcover := source_coverage C.legal R.reference_closed hW.covers_source hWI hPI
    (hQX.trans Set.subset_union_right) hlost
  have hQPop : (web C).terminalFrontier Q ⊆ popular C := by
    rw [hQT]
    rintro x (hx | hx)
    · exact hPop hx.1
    · have hxp : x = T.interval.tail.finish := Set.mem_singleton_iff.mp hx
      exact hxp.symm ▸ Or.inl (tail_finish_mem_persistent (T := T))
  have hQBlue : IsBlueprint C R.later.stage Q :=
    of_roofed_fields hQ (hQX.trans R.later.subset_roof) hcover
      ((Cardinal.mk_subtype_mono hQX).trans R.card_le)
      (DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace hU.infinitely_many_marked htrace)
      (hQPop.trans Set.subset_union_left)
  have hpathV : T.interval.tail.support ⊆ (web C).vertexSet Q := by
    rw [hQV]
    exact Set.subset_union_right
  have hpathE : T.interval.tail.edgeSet ⊆ familyEdges Q := by
    rw [hQE]
    exact Set.subset_union_right
  have hreachFront : RealReach Gamma (web C) Q z T.interval.front.finish :=
    hpReach.mono hUQ (fun _ he ↦ ⟨hUQE he.1, he.2⟩)
  have hreachTail : RealReach Gamma (web C) Q T.interval.front.finish T.interval.tail.finish := by
    simpa only [T.interval.tail_start] using RealReach.of_path T.interval.tail hpathV hpathE
  refine ⟨Q, hQBlue, hQE.trans (congrArg (fun E ↦ E ∪ T.interval.tail.edgeSet) hUE),
    hQV.trans (congrArg (fun X ↦ X ∪ T.interval.tail.support) hUV), hQI.trans hUI,
    hkeepV.trans hUQ, hkeepE.trans hUQE, hWI, hQX, hQPop, ?_,
    ⟨T.interval.tail.finish, T.interval.tail_boundary.2, hreachFront.trans hreachTail⟩, ?_⟩
  · rintro x ⟨hx, hxF⟩
    have hxV : x ∈ (web C).vertexSet Q := by
      obtain ⟨q, hq, hqx⟩ := hx
      exact ⟨q, hq, (web C).terminal_mem_support hqx⟩
    exact (R.frontier_inter ▸ (show x ∈ R.closedSet ∩ C.ladder.frontier R.later.stage from
      ⟨hQX hxV, hxF⟩)).2
  · intro x y hy he
    rw [hQE] at he
    rcases he with he | he
    · exact hfresh hy he
    · have hyTail := (T.interval.tail.edgeSet_subset_support_prod he).2
      have hyStart : y = T.interval.tail.start := Set.mem_singleton_iff.mp
        (currentRoof_tail_inter_subset ⟨hW.vertices_roofed hy, hyTail⟩)
      exact False.elim (FinitePath.no_incoming_edge_at_start T.interval.tail x (hyStart ▸ he))

#print axioms rootedCarrier_tail_inter_subset
#print axioms exists_targetBlueprint

end EndpointReferenceAssignment
end Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction
