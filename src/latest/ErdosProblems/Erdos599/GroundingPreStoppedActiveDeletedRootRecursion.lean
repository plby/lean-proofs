/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedOwnerClassifiedRootOutcome

/-!
# Root recursion from an exposed deleted head

The root-assumption-free owner split still has two apparently unranked
constructors.  A represented cut edge has a control request at its head;
classifying that unrooted control gives either an active-anchor failure or
the finite inactive-control obstruction.  A same-head forward conflict
puts the unrooted deleted head on an actual retained active route, and hence
also gives an active-anchor failure.  Thus only the backward and same-tail
constructors remain as owner-rank alternatives.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Recursive normal form of one unrooted last deleted head on a component
exposed by the active request `c`. -/
inductive ReservedExposedDeletedRootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (c : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (Y : Gamma.DPath) {p : DirectedPath.FinitePath Gamma.graph}
    (D : LastDeletedHead p
      (L.assertion822ReservedPreStoppedEdges hL S R)) : Prop
  | activeAnchor
      (failure : ReservedActiveAnchorFailure (R := R))
  | inactiveControl
      (q : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut)
      (data : InactivePreStoppedRootObstructionData S
        (L.reservedGroundedControls hL S R)
        (Gamma.source \ {R.record.initial}) q)
  | backwardOwner
      (u : V)
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (selected_edge : (u, D.head) ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward)
      (link_mem : l ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.links)
      (direction : l.direction = .backward)
      (link_edge : (u, D.head) ∈ l.path.edgeSet)
      (parent_mem : parent ∈
        (L.popularAuxiliaryInput hL.legal).ladder.paths)
      (subpath : l.path.IsSubpathOf parent)
      (parent_eq : parent = Y)
      (owner_rank : d.1 = c.1 ∨
        controlRank (L.popularAuxiliaryIndexed hL) S d.1 <
          controlRank (L.popularAuxiliaryIndexed hL) S c.1)
  | forwardTailOwner
      (u : V)
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (f : V × V)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (conflict : (u, D.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path)
      (same_tail : u = f.1)
      (owner_rank : d.1 = c.1 ∨
        controlRank (L.popularAuxiliaryIndexed hL) S d.1 <
          controlRank (L.popularAuxiliaryIndexed hL) S c.1)

/-- Eliminate the represented-cut and same-head constructors of the exposed
owner split by feeding their genuinely unrooted points back into the
control/active-anchor recursion. -/
theorem ExposedDeletedOwnerRankOutcome.rootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {c : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    {Y : Gamma.DPath} {p : DirectedPath.FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (L.assertion822ReservedPreStoppedEdges hL S R)}
    (outcome : ExposedDeletedOwnerRankOutcome
      (L.reservedGroundedControls hL S R) c Y D)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a D.head) :
    ReservedExposedDeletedRootRecursionOutcome c Y D := by
  cases outcome with
  | cut u he hcut =>
      obtain ⟨q, hq⟩ := exists_controlRequest_head_of_mem_CE hcut
      have hqNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              L.assertion822ReservedPreStoppedEdges hL S R)
            a q.1 := by
        simpa only [hq] using hnot
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
              (fun x y ↦ (x, y) ∈
                L.assertion822ReservedPreStoppedEdges hL S R)
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
  | backward u d l parent he hselected hl hdir hlink hparent hsub
      hparentEq hrank =>
      exact .backwardOwner u d l parent he hselected hl hdir hlink
        hparent hsub hparentEq hrank
  | forwardTail u d f he hconflict hf htail hrank =>
      exact .forwardTailOwner u d f he hconflict hf htail hrank
  | retainedHead u d f he hconflict hf hhead =>
      have hfDirectionEdge : f ∈ (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path.directionEdges .forward := by
        simpa only [retainedForwardEdgesAt_empty] using hf
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
            (fun x y ↦ (x, y) ∈
              L.assertion822ReservedPreStoppedEdges hL S R)
            a f.2 := by
        simpa only [hhead] using hnot
      exact .activeAnchor
        (ReservedActiveAnchorFailure.of_forwardVertex_not_rooted
          d hfDirection hfNot)

/-- Recursive owner normal form for a selected-initial deleted-head
certificate. -/
theorem ReservedActiveInitialLastDeletedHeadData.rootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    (data : ReservedActiveInitialLastDeletedHeadData d) :
    ReservedExposedDeletedRootRecursionOutcome
      d data.parent data.deleted :=
  data.deletedOwnerRank_or_retainedHead.rootRecursionOutcome
    data.deleted_head_not_rooted

/-- Recursive owner normal form for the grounded-prefix branch of a
backward anchor. -/
theorem ReservedBackwardOwnerLastDeletedHeadData.rootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    {l : Link Gamma.graph} {parent : Gamma.DPath}
    (data : ReservedBackwardOwnerLastDeletedHeadData d l parent)
    (hl : l ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hsub : l.path.IsSubpathOf parent) :
    ReservedExposedDeletedRootRecursionOutcome
      d parent data.deleted :=
  (data.deletedOwnerRank_or_retainedHead hl hldir hsub).rootRecursionOutcome
    data.deleted_head_not_rooted

/-- The same recursive normal form for the deleted head produced by an
inactive control.  Its active absorber and exposed parent are already fields
of the obstruction data, so no rooting premise is required. -/
theorem inactiveControlRootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut}
    (data : InactivePreStoppedRootObstructionData S
      (L.reservedGroundedControls hL S R)
      (Gamma.source \ {R.record.initial}) c) :
    ReservedExposedDeletedRootRecursionOutcome
      data.absorber data.parent data.deleted := by
  have howner := exposedDeletedOwnerRankOutcome
    (L.reservedGroundedControls hL S R)
    (L.popularAuxiliary_proxyPathsFaithful hL)
    data.absorber data.parent data.parent_exposed data.segment_edges
    data.deleted data.deleted_class
  exact howner.rootRecursionOutcome data.deleted_head_not_rooted

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ExposedDeletedOwnerRankOutcome.rootRecursionOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedActiveInitialLastDeletedHeadData.rootRecursionOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedBackwardOwnerLastDeletedHeadData.rootRecursionOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.inactiveControlRootRecursionOutcome
