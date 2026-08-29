/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedUniformRecursiveRootOutcome
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Reducing a missing blocking-fragment initial

A maximal surviving fragment starts either at its limiting-ladder parent's
initial vertex or immediately after a represented cut edge.  In the second
case, failure to root the fragment initial is precisely failure to root the
control request represented by that cut edge, and hence feeds back into the
same recursively normalized active/inactive control classification.

Thus the only genuinely new initial case is an unrooted parent initial.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Uniform blocking recursion after resolving a missing fragment initial
through the fragment-predecessor dichotomy. -/
inductive ParentInitialRecursiveBlockingRootOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Prop
  | parentInitialNotRooted
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
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

/-- Resolve the unrooted-fragment-initial constructor.  A represented cut
predecessor is classified as an active anchor or an inactive-control owner
recursion; otherwise the fragment starts at its parent's initial vertex. -/
theorem UniformRecursiveBlockingRootOutcome.parentInitialRecursive
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : UniformRecursiveBlockingRootOutcome O P hP) :
    ParentInitialRecursiveBlockingRootOutcome O P hP := by
  cases outcome with
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl q data recursion =>
      exact .inactiveControl q data recursion
  | ownerRecursion owner D recursion =>
      exact .ownerRecursion owner D recursion
  | initialNotRooted hnot =>
      rcases
          GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
            (L.popularAuxiliaryInput hL.legal) S.cut P hP.1.1 with
        hfirst | ⟨e, heCut, _heParent, heHead⟩
      · exact .parentInitialNotRooted (by
          simpa only [hfirst] using hnot)
      · obtain ⟨q, hq⟩ := exists_controlRequest_head_of_mem_CE heCut
        have hqNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen
              (fun x y ↦
                (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
              a q.1 := by
          simpa only [hq, heHead] using hnot
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
                  (x, y) ∈
                    L.assertion822ReservedPreStoppedEdges hL S R)
                a (requestExit (chosenRequest d.1)) := by
            simpa only [d, requestExit_chosenRequest] using hqNot
          exact .activeAnchor
            ((ReservedActiveAnchorFailure.of_exit_not_rooted d hexitNot).ownerClassified.recursivelyClassified)
        · have hxDirection : x ∈ (selectedErasedCompression
              (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R)
              (chosenRequest d.1)).path.directionVertices .forward := by
            simpa only [retainedForwardVerticesAt_empty] using hx
          exact .activeAnchor
            ((ReservedActiveAnchorFailure.of_forwardVertex_not_rooted
              d hxDirection hxNot).ownerClassified.recursivelyClassified)
        · exact .inactiveControl q hdata.some
            (inactiveControlRootRecursionOutcome hdata.some)

/-- Total root-failure outcome whose only raw blocking-initial case is an
unrooted limiting-ladder parent initial. -/
inductive ParentInitialRecursiveRootFailureOutcome
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
      (recursion : ParentInitialRecursiveBlockingRootOutcome O P blockable)

/-- Every pre-stopped root obstruction has the parent-initial recursive
outcome. -/
theorem parentInitialRecursiveRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    ParentInitialRecursiveRootFailureOutcome O := by
  cases O.uniformRecursiveRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.parentInitialRecursive

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler after resolving every represented
cut predecessor of a missing blocking-fragment initial. -/
theorem assertion822Output_or_hindrance_of_preStoppedParentInitialRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.ParentInitialRecursiveRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedUniformRecursiveRootRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.parentInitialRecursiveRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.UniformRecursiveBlockingRootOutcome.parentInitialRecursive
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.parentInitialRecursiveRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedParentInitialRootRepairs
