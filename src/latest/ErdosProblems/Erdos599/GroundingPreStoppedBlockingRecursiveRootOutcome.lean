/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedDeepRecursiveRootOutcome
import ErdosProblems.Erdos599.GroundingPreStoppedBlockingDeletedRootRecursion

/-!
# Recursive classification of blocking root failures

The deep root classification already replaces represented-cut and same-head
failures in the active and inactive control branches by their exact owner
recursion.  This file performs the analogous normalization at a blocking
point.  In particular, the coarse witnesses that a selected backward edge
or a forward-conflict edge meets the blocking prefix are replaced by the
downstream-most missing edge and its exact owner data.

The blocking recursion is retained as a bundled value.  Consequently its
backward-owner branch keeps both the equality with the blocking fragment's
parent and the proof that this parent is not the reserved grounded record.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Root failures after recursive owner normalization in the active,
inactive, and blocking branches. -/
inductive BlockingRecursiveRootFailureOutcome
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
      (recursion : ReservedBlockingDeletedRootRecursionOutcome O P blockable)

/-- Every pre-stopped root obstruction has the recursively normalized
blocking outcome. -/
theorem blockingRecursiveRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    BlockingRecursiveRootFailureOutcome O := by
  cases O.deepRecursiveRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blockingInitial P hP heq _ =>
      exact .blocking P hP heq
        (O.blockingDeletedRootRecursionOutcome P hP heq)
  | blockingBackward P hP heq _ _ _ =>
      exact .blocking P hP heq
        (O.blockingDeletedRootRecursionOutcome P hP heq)
  | blockingForwardConflict P hP heq _ _ _ =>
      exact .blocking P hP heq
        (O.blockingDeletedRootRecursionOutcome P hP heq)

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler exposing recursive owner data in
all active, inactive, and blocking root-failure branches. -/
theorem assertion822Output_or_hindrance_of_preStoppedBlockingRecursiveRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.BlockingRecursiveRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedDeepRecursiveRootRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.blockingRecursiveRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.blockingRecursiveRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedBlockingRecursiveRootRepairs
