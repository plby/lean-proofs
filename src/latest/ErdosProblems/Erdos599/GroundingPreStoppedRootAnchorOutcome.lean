/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedActiveRootReduction
import ErdosProblems.Erdos599.GroundingPreStoppedFiniteRootBackwardSwitch

/-!
# Anchor-reduced pre-stopped root failures

The backward-normalized root classifier still has two syntactically
different active-route failures: the request exit of an active control, and
an internal retained forward vertex.  Both reduce to the same exact anchor
failure.  This file performs that reduction while retaining the inactive and
blocking constructors verbatim.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- The two possible unrooted anchors of one active reserved request. -/
inductive ReservedActiveAnchorFailure
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} : Prop
  | initial
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R)
            (chosenRequest d.1)).initial)
  | backwardOwner
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (link_mem : l ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.links)
      (backward : l.direction = .backward)
      (parent_mem : parent ∈ L.limitWarp)
      (subpath : l.path.IsSubpathOf parent)
      (parent_ne_reserved : parent ≠ R.record)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a l.path.start)

/-- Package the active-exit anchor reduction. -/
theorem ReservedActiveAnchorFailure.of_exit_not_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a (requestExit (chosenRequest d.1))) :
    ReservedActiveAnchorFailure (R := R) := by
  rcases R.reservedActiveRequest_exit_unrooted_cases d hnot with
      hinitial | ⟨l, parent, hl, hldir, hparent, hsub, hne, hstart⟩
  · exact .initial d hinitial
  · exact .backwardOwner d l parent hl hldir hparent hsub hne hstart

/-- Package the active-forward-vertex anchor reduction. -/
theorem ReservedActiveAnchorFailure.of_forwardVertex_not_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    {x : V}
    (hx : x ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.directionVertices .forward)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun u v ↦
          (u, v) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a x) :
    ReservedActiveAnchorFailure (R := R) := by
  rcases R.reservedActiveRequest_forwardVertex_unrooted_cases
      d hx hnot with
      hinitial | ⟨l, parent, hl, hldir, hparent, hsub, hne, hstart⟩
  · exact .initial d hinitial
  · exact .backwardOwner d l parent hl hldir hparent hsub hne hstart

/-- Root-failure classifier after both the finite-source normalization and
the active-route anchor reduction. -/
inductive ActiveAnchorReducedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | activeAnchor (failure : ReservedActiveAnchorFailure (R := R))
  | inactiveControl
      (c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : c.1 = O.boundary)
      (data : InactivePreStoppedRootObstructionData S
        (L.reservedGroundedControls hL S R)
        (Gamma.source \ {R.record.initial}) c)
  | blockingInitial
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (initial_not_rooted : ¬ ∃ a ∈
          Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.path.initial)
  | blockingBackward
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (e : V × V)
      (prefix_edge : e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P blockable).path.edgeSet)
      (selected_backward : e ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward)
  | blockingForwardConflict
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (e : V × V)
      (prefix_edge : e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P blockable).path.edgeSet)
      (forward_conflict : e ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)

/-- Every pre-stopped root obstruction has the anchor-reduced outcome. -/
theorem activeAnchorReducedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    ActiveAnchorReducedRootFailureOutcome O := by
  cases O.backwardNormalizedRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeControl c heq hactive =>
      let d : ActiveControlRequestAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (∅ : Set V) :=
        ⟨c, hactive⟩
      have hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
            a (requestExit (chosenRequest d.1)) := by
        rintro ⟨a, ha, hareach⟩
        apply O.not_rooted
        refine ⟨a, ha, ?_⟩
        simpa only [d, requestExit_chosenRequest, heq] using hareach
      exact .activeAnchor
        (ReservedActiveAnchorFailure.of_exit_not_rooted d hnot)
  | activeRetainedVertex c heq d x hx hnot =>
      have hx' : x ∈ (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path.directionVertices .forward := by
        simpa only [retainedForwardVerticesAt_empty] using hx
      exact .activeAnchor
        (ReservedActiveAnchorFailure.of_forwardVertex_not_rooted d hx' hnot)
  | inactiveControl c heq data => exact .inactiveControl c heq data
  | blockingInitial P hP heq hnot =>
      exact .blockingInitial P hP heq hnot
  | blockingBackward P hP heq e hePrefix heBackward =>
      exact .blockingBackward P hP heq e hePrefix heBackward
  | blockingForwardConflict P hP heq e hePrefix heConflict =>
      exact .blockingForwardConflict P hP heq e hePrefix heConflict

end Assertion822PreStoppedRootObstruction

/-- Public compiler whose root callback sees active requests only through
their exact initial/backward-anchor failure.  The finite root constructor is
already backward-normalized, while inactive and blocking failures remain
explicit. -/
theorem assertion822Output_or_hindrance_of_preStoppedActiveAnchorRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.ActiveAnchorReducedRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedFullyBackwardNormalizedRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.activeAnchorReducedRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedActiveAnchorFailure.of_exit_not_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedActiveAnchorFailure.of_forwardVertex_not_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.activeAnchorReducedRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedActiveAnchorRepairs
