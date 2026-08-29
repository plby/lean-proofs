/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBlockingRecursiveRootOutcome

/-!
# Fully recursive pre-stopped root-failure outcome

The blocking-prefix classifier can itself return an active-anchor or an
inactive-control failure.  Those are not new terminal cases: they have the
same deleted-owner recursion already used by the ordinary control branches.
This file performs that final uniform normalization.

The two genuine blocking-owner alternatives are stored in dependent data
structures.  In particular, the selected-backward alternative retains the
proof that its limiting-ladder owner is exactly the blocking fragment's
parent and is distinct from the reserved grounded record.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Exact data in the selected-backward owner branch of a blocking-prefix
root failure. -/
structure ReservedBlockingBackwardOwnerData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Type u where
  deleted : LastDeletedHead
    (GroundingBlockingPrefix.data
      (L.popularAuxiliaryInput hL.legal) S.cut P hP).path
    (L.assertion822ReservedPreStoppedEdges hL S R)
  head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a deleted.head
  u : V
  owner : ActiveControlRequestAt
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (∅ : Set V)
  link : Link Gamma.graph
  parent : Gamma.DPath
  prefix_edge : (u, deleted.head) ∈
    (GroundingBlockingPrefix.data
      (L.popularAuxiliaryInput hL.legal) S.cut P hP).path.edgeSet
  selected_edge : (u, deleted.head) ∈ erasedSelectedDirectionEdgesAt
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) ∅ .backward
  link_mem : link ∈ (selectedErasedCompression
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R)
    (chosenRequest owner.1)).path.links
  direction : link.direction = .backward
  link_edge : (u, deleted.head) ∈ link.path.edgeSet
  parent_mem : parent ∈ L.limitWarp
  subpath : link.path.IsSubpathOf parent
  parent_ne_reserved : parent ≠ R.record
  parent_eq : parent = P.parent

/-- Exact data in the same-tail retained-forward owner branch of a
blocking-prefix root failure. -/
structure ReservedBlockingForwardTailOwnerData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Type u where
  deleted : LastDeletedHead
    (GroundingBlockingPrefix.data
      (L.popularAuxiliaryInput hL.legal) S.cut P hP).path
    (L.assertion822ReservedPreStoppedEdges hL S R)
  head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a deleted.head
  u : V
  owner : ActiveControlRequestAt
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (∅ : Set V)
  forward_edge : V × V
  prefix_edge : (u, deleted.head) ∈
    (GroundingBlockingPrefix.data
      (L.popularAuxiliaryInput hL.legal) S.cut P hP).path.edgeSet
  conflict : (u, deleted.head) ∈ forwardConflictCutEdgesAt
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) ∅
  retained : forward_edge ∈ retainedForwardEdgesAt ∅
    (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest owner.1)).path
  same_tail : u = forward_edge.1

/-- Fully recursive normal form of a missing root on a blocking prefix. -/
inductive FullyRecursiveBlockingRootOutcome
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
      (failure :
        RecursivelyOwnerClassifiedReservedActiveAnchorFailure (R := R))
  | inactiveControl
      (q : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut)
      (data : InactivePreStoppedRootObstructionData S
        (L.reservedGroundedControls hL S R)
        (Gamma.source \ {R.record.initial}) q)
      (recursion : ReservedExposedDeletedRootRecursionOutcome
        data.absorber data.parent data.deleted)
  | backwardOwner (data : ReservedBlockingBackwardOwnerData O P hP)
  | forwardTailOwner
      (data : ReservedBlockingForwardTailOwnerData O P hP)

/-- Recursively normalize the active and inactive cases returned by the
blocking-prefix deleted-head classifier. -/
theorem ReservedBlockingDeletedRootRecursionOutcome.fullyRecursive
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : ReservedBlockingDeletedRootRecursionOutcome O P hP) :
    FullyRecursiveBlockingRootOutcome O P hP := by
  cases outcome with
  | initialNotRooted hnot => exact .initialNotRooted hnot
  | activeAnchor failure =>
      exact .activeAnchor failure.ownerClassified.recursivelyClassified
  | inactiveControl q data =>
      exact .inactiveControl q data
        (inactiveControlRootRecursionOutcome data)
  | backwardOwner D hnot u d l parent hePrefix heSelected hl hdir
      heLink hparent hsub hne heq =>
      exact .backwardOwner {
        deleted := D
        head_not_rooted := hnot
        u := u
        owner := d
        link := l
        parent := parent
        prefix_edge := hePrefix
        selected_edge := heSelected
        link_mem := hl
        direction := hdir
        link_edge := heLink
        parent_mem := hparent
        subpath := hsub
        parent_ne_reserved := hne
        parent_eq := heq }
  | forwardTailOwner D hnot u d f hePrefix heConflict hf htail =>
      exact .forwardTailOwner {
        deleted := D
        head_not_rooted := hnot
        u := u
        owner := d
        forward_edge := f
        prefix_edge := hePrefix
        conflict := heConflict
        retained := hf
        same_tail := htail }

/-- Total root-failure normal form with recursive classification in every
control branch, including those reached through a blocking prefix. -/
inductive FullyRecursiveRootFailureOutcome
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
      (recursion : ReservedExposedDeletedRootRecursionOutcome
        data.absorber data.parent data.deleted)
  | blocking
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (recursion : FullyRecursiveBlockingRootOutcome O P blockable)

/-- Every pre-stopped root obstruction has the fully recursive outcome. -/
theorem fullyRecursiveRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    FullyRecursiveRootFailureOutcome O := by
  cases O.blockingRecursiveRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.fullyRecursive

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler exposing the fully recursive root
normal form. -/
theorem assertion822Output_or_hindrance_of_preStoppedFullyRecursiveRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FullyRecursiveRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply
    L.assertion822Output_or_hindrance_of_preStoppedBlockingRecursiveRootRepairs
      hL S
  · intro R O _outcome
    exact repairRoot R O O.fullyRecursiveRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedBlockingDeletedRootRecursionOutcome.fullyRecursive
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.fullyRecursiveRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFullyRecursiveRootRepairs
