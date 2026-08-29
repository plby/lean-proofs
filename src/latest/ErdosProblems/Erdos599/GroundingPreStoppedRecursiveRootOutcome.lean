/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedActiveDeletedRootRecursion

/-!
# Recursively owner-classified pre-stopped root failures

This file propagates the cut/head elimination for active deleted heads
through the total pre-stopped root classifier.  An active-anchor failure is
now either a genuine equal-stage hanging match or carries a recursive normal
form with only active/inactive recursion and same-or-strictly-earlier owners.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Active-anchor failure after the represented-cut and same-head branches
have been converted to actual recursive root failures. -/
inductive RecursivelyOwnerClassifiedReservedActiveAnchorFailure
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} : Prop
  | initialDeleted
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (data : ReservedActiveInitialLastDeletedHeadData d)
      (recursion : ReservedExposedDeletedRootRecursionOutcome
        d data.parent data.deleted)
  | backwardOwnerDeleted
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (link_mem : l ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.links)
      (backward : l.direction = .backward)
      (subpath : l.path.IsSubpathOf parent)
      (data : ReservedBackwardOwnerLastDeletedHeadData d l parent)
      (recursion : ReservedExposedDeletedRootRecursionOutcome
        d parent data.deleted)
  | hangingEqualMatch
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (certificate : OwnerClassifiedReservedActiveEqualMatch d)

/-- Eliminate cut and retained-head constructors from an already
owner-classified active anchor. -/
theorem OwnerClassifiedReservedActiveAnchorFailure.recursivelyClassified
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (failure : OwnerClassifiedReservedActiveAnchorFailure (R := R)) :
    RecursivelyOwnerClassifiedReservedActiveAnchorFailure (R := R) := by
  cases failure with
  | initialDeleted d data _ownerSplit =>
      exact .initialDeleted d data data.rootRecursionOutcome
  | backwardOwnerDeleted d l parent hl hldir hsub data _ownerSplit =>
      exact .backwardOwnerDeleted d l parent hl hldir hsub data
        (data.rootRecursionOutcome hl hldir hsub)
  | hangingEqualMatch d certificate =>
      exact .hangingEqualMatch d certificate

/-- Total root-failure outcome after recursive normalization of every
active deleted head. -/
inductive RecursivelyClassifiedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | activeAnchor
      (failure :
        RecursivelyOwnerClassifiedReservedActiveAnchorFailure (R := R))
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
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
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

/-- Every pre-stopped root obstruction has the recursively classified
outcome. -/
theorem recursivelyClassifiedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    RecursivelyClassifiedRootFailureOutcome O := by
  cases O.ownerClassifiedRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure =>
      exact .activeAnchor failure.recursivelyClassified
  | inactiveControl c heq data => exact .inactiveControl c heq data
  | blockingInitial P hP heq hnot =>
      exact .blockingInitial P hP heq hnot
  | blockingBackward P hP heq e hePrefix heBackward =>
      exact .blockingBackward P hP heq e hePrefix heBackward
  | blockingForwardConflict P hP heq e hePrefix heConflict =>
      exact .blockingForwardConflict P hP heq e hePrefix heConflict

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler exposing the recursively classified
root callback. -/
theorem assertion822Output_or_hindrance_of_preStoppedRecursiveRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.RecursivelyClassifiedRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedOwnerClassifiedRootRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.recursivelyClassifiedRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.OwnerClassifiedReservedActiveAnchorFailure.recursivelyClassified
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.recursivelyClassifiedRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedRecursiveRootRepairs
