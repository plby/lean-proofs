/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedFullyRecursiveRootOutcome

/-!
# Uniform recursive normal form for pre-stopped root failures

The exact owner of a missing blocking-prefix edge exposes the blocking
fragment's parent.  Consequently the backward-owner and same-tail-forward
blocking cases are self-owner instances of the same exposed-component
recursion used for ordinary active and inactive controls.  This file makes
that identification literal and removes the two special selected-edge
constructors from the public root-repair callback.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- A blocking-prefix backward owner is a self-owner instance of exposed
deleted-head recursion on the blocking fragment's parent. -/
theorem ReservedBlockingBackwardOwnerData.rootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (data : ReservedBlockingBackwardOwnerData O P hP) :
    ReservedExposedDeletedRootRecursionOutcome
      data.owner P.parent data.deleted := by
  exact .backwardOwner data.u data.owner data.link data.parent
    data.prefix_edge data.selected_edge data.link_mem data.direction
    data.link_edge (by
      simpa only [KappaLadder.popularAuxiliaryInput] using data.parent_mem)
    data.subpath data.parent_eq (Or.inl rfl)

/-- A blocking-prefix same-tail conflict is the forward self-owner instance
of exposed deleted-head recursion on the blocking fragment's parent. -/
theorem ReservedBlockingForwardTailOwnerData.rootRecursionOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (data : ReservedBlockingForwardTailOwnerData O P hP) :
    ReservedExposedDeletedRootRecursionOutcome
      data.owner P.parent data.deleted := by
  exact .forwardTailOwner data.u data.owner data.forward_edge
    data.prefix_edge data.conflict data.retained data.same_tail
    (Or.inl rfl)

/-- Uniform recursive normal form for a blocking-prefix root failure. -/
inductive UniformRecursiveBlockingRootOutcome
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
  | ownerRecursion
      (owner : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (D : LastDeletedHead
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hP).path
        (L.assertion822ReservedPreStoppedEdges hL S R))
      (recursion : ReservedExposedDeletedRootRecursionOutcome
        owner P.parent D)

/-- Fold both exact blocking-owner constructors into uniform exposed-parent
recursion. -/
theorem FullyRecursiveBlockingRootOutcome.uniformRecursive
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : FullyRecursiveBlockingRootOutcome O P hP) :
    UniformRecursiveBlockingRootOutcome O P hP := by
  cases outcome with
  | initialNotRooted hnot => exact .initialNotRooted hnot
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl q data recursion =>
      exact .inactiveControl q data recursion
  | backwardOwner data =>
      exact .ownerRecursion data.owner data.deleted
        data.rootRecursionOutcome
  | forwardTailOwner data =>
      exact .ownerRecursion data.owner data.deleted
        data.rootRecursionOutcome

/-- Total root-failure normal form in which every selected-edge deletion is
represented by the same exposed-component owner recursion. -/
inductive UniformRecursiveRootFailureOutcome
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
      (recursion : UniformRecursiveBlockingRootOutcome O P blockable)

/-- Every pre-stopped root obstruction has the uniform recursive outcome. -/
theorem uniformRecursiveRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    UniformRecursiveRootFailureOutcome O := by
  cases O.fullyRecursiveRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.uniformRecursive

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler with a uniform exposed-component
recursion in every selected-edge root-failure branch. -/
theorem assertion822Output_or_hindrance_of_preStoppedUniformRecursiveRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.UniformRecursiveRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedFullyRecursiveRootRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.uniformRecursiveRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.FullyRecursiveBlockingRootOutcome.uniformRecursive
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.uniformRecursiveRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedUniformRecursiveRootRepairs
