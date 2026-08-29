/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedActiveDeletedRootRecursion

/-!
# Root recursion at a blocking prefix

An arbitrary selected edge on a blocking prefix does not identify the edge
which actually prevents the blocking point from being rooted.  We therefore
return to the canonical prefix and take its downstream-most missing edge.
The head of that edge is unrooted.  Represented-cut and same-head conflict
cases feed back into the control/active-anchor recursion, while the two
genuine owner cases retain the exact selected request and link/forward edge.

The backward-link owner is also identified with the parent of the blocking
fragment.  This is a useful strengthening over the raw selected-edge
provenance: it records the component on which the subsequent owner/exchange
argument must operate.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode
  PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

private theorem altPath_link_support_subset_vertexSet
    {Q : AltPath Gamma.graph} {l : Link Gamma.graph}
    (hl : l ∈ Q.links) : l.path.support ⊆ Q.vertexSet := by
  cases Q with
  | trivial v => simp at hl
  | finite Q =>
      simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, hx⟩
  | infinite Q =>
      simp only [AltPath.links, InfiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, hx⟩

/-- Every edge of the canonical blocking prefix lies on the parent of the
fragment.  `GroundingBlockingPrefix.Data` only stores family-edge membership,
so the proof uses disjointness of the limiting-ladder warp to identify the
family-edge owner from either endpoint. -/
theorem blockingPrefix_edge_mem_parent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    {e : V × V}
    (he : e ∈ (GroundingBlockingPrefix.data
      (L.popularAuxiliaryInput hL.legal) S.cut P hP).path.edgeSet) :
    e ∈ P.parent.edgeSet := by
  let Q := GroundingBlockingPrefix.data
    (L.popularAuxiliaryInput hL.legal) S.cut P hP
  obtain ⟨Y, hY, heY⟩ := (Q.edgeSet_subset_residual he).1
  have heTailQ : e.1 ∈ Q.path.support :=
    (Q.path.edgeSet_subset_support_prod he).1
  have heTailP : e.1 ∈ P.parent.support :=
    P.support_subset (Q.support_subset heTailQ)
  have heTailY : e.1 ∈ Y.support :=
    (Y.edgeSet_subset_support_prod heY).1
  have hYP : Y = P.parent :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (L.popularAuxiliaryInput hL.legal).ladder.disjoint
      hY P.parent_mem heTailY heTailP
  simpa only [hYP] using heY

/-- A concrete selected backward link exposes its limiting-ladder owner to
the selected auxiliary path.  This is the data-free form of the analogous
lemma for a grounded backward-anchor prefix. -/
theorem selectedBackwardLink_parent_exposed
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (l : Link Gamma.graph) (parent : Gamma.DPath)
    (hl : l ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    parent ∈ exposedLadderPaths
      (L.popularAuxiliaryInput hL.legal)
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      l.path l.path.start_mem_support l.nontrivial
  have heDirection : (l.path.start, y) ∈
      (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.directionEdges .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hy⟩
  have hePath :=
    (selectedBackwardEdge_auxContact_offApex
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1) heDirection).1
  left
  refine ⟨?_, LambdaVertex.edge l.path.start y, hePath,
    Or.inr ⟨(l.path.start, y), hsub.2 hy, rfl⟩⟩
  simpa only [KappaLadder.popularAuxiliaryInput] using hparent

/-- A retained selected forward edge whose tail lies on a limiting-ladder
parent exposes that parent to its selected auxiliary path.  The proof uses
the actual loop-erased route vertex, not a raw decoded edge. -/
theorem retainedForwardTail_parent_exposed
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    {f : V × V}
    (hf : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path)
    (hftail : f.1 ∈ parent.support) :
    parent ∈ exposedLadderPaths
      (L.popularAuxiliaryInput hL.legal)
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
  let Q := selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (chosenRequest d.1)
  have hfDirection : f ∈ Q.path.directionEdges .forward := by
    simpa only [Q, retainedForwardEdgesAt_empty] using hf
  have hftailDirection : f.1 ∈ Q.path.directionVertices .forward :=
    (Q.path.directionEdge_endpoints hfDirection).1
  have hftailVertex : f.1 ∈ Q.path.vertexSet := by
    simp only [AltPath.directionVertices, Set.mem_iUnion] at hftailDirection
    obtain ⟨l, hl, _hdir, hfl⟩ := hftailDirection
    exact altPath_link_support_subset_vertexSet hl hfl
  have hftailCarrier : f.1 ∈
      (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier
        (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
    apply GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (chosenRequest d.1)
    simpa only [Q] using hftailVertex
  have hpStart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (chosenRequest d.1)).start ∈
      (L.popularAuxiliaryInput hL.legal).lambda.source :=
    (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)).starts_in_source
        ⟨chosenRequest d.1, rfl⟩
  apply (L.popularAuxiliaryInput hL.legal).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (L.popularAuxiliary_proxyPathsFaithful hL)
    (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (chosenRequest d.1))
    hpStart hparent hftailCarrier hftail

/-- Root-recursive normal form of a failed blocking point.  The selected
backward and same-tail forward constructors are the only owner cases left;
the other deletion classes are immediately turned into a control or active
anchor failure. -/
inductive ReservedBlockingDeletedRootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Prop
  | initialNotRooted
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.path.initial)
  | activeAnchor
      (failure : ReservedActiveAnchorFailure (R := R))
  | inactiveControl
      (q : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut)
      (data : InactivePreStoppedRootObstructionData S
        (L.reservedGroundedControls hL S R)
        (Gamma.source \ {R.record.initial}) q)
  | backwardOwner
      (D : LastDeletedHead
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hP).path
        (L.assertion822ReservedPreStoppedEdges hL S R))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a D.head)
      (u : V)
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (prefix_edge : (u, D.head) ∈
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hP).path.edgeSet)
      (selected_edge : (u, D.head) ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward)
      (link_mem : l ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.links)
      (direction : l.direction = .backward)
      (link_edge : (u, D.head) ∈ l.path.edgeSet)
      (parent_mem : parent ∈ L.limitWarp)
      (subpath : l.path.IsSubpathOf parent)
      (parent_ne_reserved : parent ≠ R.record)
      (parent_eq : parent = P.parent)
  | forwardTailOwner
      (D : LastDeletedHead
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hP).path
        (L.assertion822ReservedPreStoppedEdges hL S R))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a D.head)
      (u : V)
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (f : V × V)
      (prefix_edge : (u, D.head) ∈
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hP).path.edgeSet)
      (conflict : (u, D.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path)
      (same_tail : u = f.1)

/-- Classify a genuinely unrooted blocking point using the last missing edge
of its canonical prefix. -/
theorem blockingDeletedRootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hboundary : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary) :
    ReservedBlockingDeletedRootRecursionOutcome O P hP := by
  rcases O.blocking_lastDeletedHead_cases P hP hboundary with
      hinitial | ⟨D, hDnot, hclass⟩
  · exact .initialNotRooted hinitial
  rcases hclass with hcut | hbackward | hconflict
  · obtain ⟨u, huPrefix, huCut⟩ := hcut
    obtain ⟨q, hq⟩ := exists_controlRequest_head_of_mem_CE huCut
    have hqNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a q.1 := by
      simpa only [hq] using hDnot
    rcases controlAt_empty_unrooted_cases
        (L.reservedGroundedControls hL S R)
        (L.popularAuxiliary_proxyPathsFaithful hL)
        (Gamma.source \ {R.record.initial}) q hqNot with
        hactive | ⟨d, x, hx, hxNot⟩ | hdata
    · let d : ActiveControlRequestAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (∅ : Set V) :=
        ⟨q, hactive⟩
      have hexitNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
            a (requestExit (chosenRequest d.1)) := by
        simpa only [d, requestExit_chosenRequest] using hqNot
      exact .activeAnchor
        (ReservedActiveAnchorFailure.of_exit_not_rooted d hexitNot)
    · have hxDirection : x ∈ (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path.directionVertices .forward := by
        simpa only [retainedForwardVerticesAt_empty] using hx
      exact .activeAnchor
        (ReservedActiveAnchorFailure.of_forwardVertex_not_rooted
          d hxDirection hxNot)
    · exact .inactiveControl q hdata.some
  · obtain ⟨u, huPrefix, huBackward⟩ := hbackward
    obtain ⟨d, l, parent, hl, hldir, hul, hparent, hsub, hne⟩ :=
      R.exists_reservedSelectedBackwardEdge_ownerAt ∅ huBackward
    have huP : (u, D.head) ∈ P.parent.edgeSet :=
      blockingPrefix_edge_mem_parent hP huPrefix
    have huParent : (u, D.head) ∈ parent.edgeSet := hsub.2 hul
    have hparentEq : parent = P.parent :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (L.popularAuxiliaryInput hL.legal).ladder.disjoint
        hparent P.parent_mem
        (parent.edgeSet_subset_support_prod huParent).1
        (P.parent.edgeSet_subset_support_prod huP).1
    exact .backwardOwner D hDnot u d l parent huPrefix huBackward hl
      hldir hul hparent hsub hne hparentEq
  · obtain ⟨u, huPrefix, huConflict⟩ := hconflict
    rcases huConflict with ⟨huResidual, f, hf, htail | hhead⟩
    · simp only [erasedSelectedRetainedForwardEdgesAt,
        Set.mem_iUnion] at hf
      obtain ⟨d, hfd⟩ := hf
      exact .forwardTailOwner D hDnot u d f huPrefix
        ⟨huResidual, f, by
          simp only [erasedSelectedRetainedForwardEdgesAt,
            Set.mem_iUnion]
          exact ⟨d, hfd⟩,
          Or.inl htail⟩
        hfd htail
    · simp only [erasedSelectedRetainedForwardEdgesAt,
        Set.mem_iUnion] at hf
      obtain ⟨d, hfd⟩ := hf
      have hfDirectionEdge : f ∈ (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path.directionEdges .forward := by
        simpa only [retainedForwardEdgesAt_empty] using hfd
      have hfDirection : f.2 ∈ (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path.directionVertices .forward :=
        ((selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path.directionEdge_endpoints
            hfDirectionEdge).2
      have hfNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a f.2 := hhead ▸ hDnot
      exact .activeAnchor
        (ReservedActiveAnchorFailure.of_forwardVertex_not_rooted
          d hfDirection hfNot)

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.blockingPrefix_edge_mem_parent
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.blockingDeletedRootRecursionOutcome
