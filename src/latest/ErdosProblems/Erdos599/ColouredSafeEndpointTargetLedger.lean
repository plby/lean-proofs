/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointTargetTail
import ErdosProblems.Erdos599.ColouredSafeAugmentedFullAccounting

/-!
# The exact old-full-terminal ledger of the ordinary target extension

Old terminals off the current frontier or on the persistent frontier survive,
except for the selected source. This is the boundary required to promote a
preceding stable blueprint's singleton local account to the actual target.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction
namespace EndpointReferenceAssignment

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint ColouredSafeMovingStages ColouredSafeActivatedPrefixes
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}
variable {T : NativePostClosureIntervalTransaction C seed z R}
variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}
variable (A : NativePostClosureIntervalTransaction.EndpointReferenceAssignment T F)

theorem old_terminal_retained {W Q : Set (web C).DPath}
    (hW : IsBlueprint C C.newStage W) (hWX : (web C).vertexSet W ⊆ R.closedSet)
    (hQ : (web C).IsWarp Q) (hV : (web C).vertexSet W ⊆ (web C).vertexSet Q)
    (hE : familyEdges Q = RootReachableRelation.edges
      (A.attachedEdges (seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet))
      ((web C).initialSet (seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet)) ∪
      T.interval.tail.edgeSet)
    {x : V} (hx : x ∈ (web C).terminalFrontier W) (hxz : x ≠ z)
    (hboundary : x ∉ C.newSlice ∨ x ∈ C.persistent) :
    x ∈ (web C).terminalFrontier Q := by
  have hxW : x ∈ (web C).vertexSet W := by
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hp, (web C).terminal_mem_support hpx⟩
  have hnoW := isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier hW.isWarp hx
  have hnoK : ¬HasOutgoing (familyEdges
      (seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet)) x := by
    rw [seedFamily_edges]
    rintro ⟨y, he | he⟩
    · exact hnoW ⟨y, he⟩
    · exact Set.disjoint_left.mp vertices_disjoint
        (familyEdges_subset_vertexSet_prod _ he).1 hxW
  have hnoH : ¬HasOutgoing A.closedEdges x := by
    rintro ⟨y, he⟩
    have hxRow := (A.closedEdges_subset_insideCarrier he).1.1
    rcases hboundary with hxOff | hxPersistent
    · apply hxOff
      change x ∈ (nativeCapturedGeometry R).oldSlice
      rw [← T.interval.ambientInterval_vertexSet_inter_oldRoof]
      exact ⟨hxRow, hW.vertices_roofed hxW⟩
    · have hxLater : x ∈ C.ladder.frontier R.later.stage :=
        (R.frontier_inter.symm ▸ (show x ∈ R.closedSet ∩ C.persistent from
          ⟨hWX hxW, hxPersistent⟩)).2
      obtain ⟨p, hp, hxp⟩ := hxRow
      have hpx := T.interval.ambientInterval_meetsOnlyAtTerminal p hp x hxp hxLater
      exact A.noOutgoing_closedEdges_of_row_terminal ⟨p, hp, hpx⟩ ⟨y, he⟩
  have hxNotTail : x ∉ T.interval.tail.support := by
    intro hxTail
    have hxf : x = T.interval.front.finish :=
      (Set.mem_singleton_iff.mp
        (currentRoof_tail_inter_subset ⟨hW.vertices_roofed hxW, hxTail⟩)).trans
          T.interval.tail_start
    have hxFront : x ∈ T.interval.front.support := hxf.symm ▸
      T.interval.front.finish_mem_support
    have hxStart : x ≠ T.interval.front.start := by
      intro h
      exact hxz (h.trans T.interval.front_start)
    obtain ⟨v, hvx⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start T.interval.front hxFront hxStart
    have hrow : (v, x) ∈ familyEdges T.interval.ambientInterval :=
      Set.mem_iUnion.mpr ⟨.inl T.interval.front,
        Set.mem_iUnion.mpr ⟨T.interval.front_mem_interval, hvx⟩⟩
    exact intervalEdge_head_not_roof hrow (hW.vertices_roofed hxW)
  rw [isWarp_terminalFrontier_eq_noOutgoing hQ]
  refine ⟨hV hxW, ?_⟩
  rintro ⟨y, hxy⟩
  rw [hE] at hxy
  rcases hxy with hxy | hxy
  · rcases hxy.1 with hold | hfresh
    · exact hnoK ⟨y, hold⟩
    · exact hnoH ⟨y, hfresh.1⟩
  · exact hxNotTail (T.interval.tail.edgeSet_subset_support_prod hxy).1

/-- A stable earlier blueprint's local singleton account promotes through
the actual ordinary extension, using the exact retained-terminal boundary. -/
theorem promote_local_account {S W Q : Set (web C).DPath}
    (hstable : (web C).terminalFrontier S ∩ C.newSlice ⊆ C.persistent)
    (haccount : FullAccount Gamma (web C) S W {z})
    (hW : IsBlueprint C C.newStage W) (hWX : (web C).vertexSet W ⊆ R.closedSet)
    (hQ : (web C).IsWarp Q) (hV : (web C).vertexSet W ⊆ (web C).vertexSet Q)
    (hretain : familyEdges W ⊆ familyEdges Q)
    (hE : familyEdges Q = RootReachableRelation.edges
      (A.attachedEdges (seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet))
      ((web C).initialSet (seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet)) ∪
      T.interval.tail.edgeSet)
    (hz : RealReaches Gamma (web C) Q z Gamma.target) :
    FullAccount Gamma (web C) S Q Gamma.target := by
  apply haccount.promote_singleton hV hretain _ hz
  rintro x ⟨⟨hxS, hxW⟩, hxz⟩
  apply A.old_terminal_retained hW hWX hQ hV hE hxW hxz
  by_cases hxF : x ∈ C.newSlice
  · exact Or.inr (hstable ⟨hxS, hxF⟩)
  · exact Or.inl hxF

#print axioms old_terminal_retained
#print axioms promote_local_account

end EndpointReferenceAssignment
end Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction
