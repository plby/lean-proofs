/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedParentInitialClassification
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# The first-fragment/cut-predecessor split for unrooted parents

The last two parent-initial cases in the pre-stopped grounding recursion are
not featureless.  A surviving fragment either begins at the initial vertex of
its limiting-ladder parent, or its incoming parent edge is one of the deleted
cut edges.  This module records that exact geometric split for both the
reserved record and a genuinely hanging parent.

The result is intentionally only a classification theorem.  It does not
claim that a cut predecessor is already rooted, nor that a hanging component
can be ignored.  Those are the two construction-specific exchanges which
remain after this reduction.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Refine the two parent-initial leaves by whether the displayed surviving
fragment is the first fragment of its parent or has a literal deleted cut
predecessor. -/
inductive FragmentSplitParentInitialBlockingRootOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Prop
  | reservedFirst
      (parent_eq : P.parent = R.record)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | reservedCutPredecessor
      (parent_eq : P.parent = R.record)
      (predecessor : GroundingConcreteControls.hasCutPredecessor
        (L.popularAuxiliaryInput hL.legal) S.cut P)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | hangingFirst
      (parent_hanging : PopularAuxiliary.IsHangingPath Gamma P.parent)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | hangingCutPredecessor
      (parent_hanging : PopularAuxiliary.IsHangingPath Gamma P.parent)
      (predecessor : GroundingConcreteControls.hasCutPredecessor
        (L.popularAuxiliaryInput hL.legal) S.cut P)
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

/-- The reserved/hanging classification always admits the literal
first-fragment/cut-predecessor refinement. -/
theorem ClassifiedParentInitialBlockingRootOutcome.fragmentSplit
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : ClassifiedParentInitialBlockingRootOutcome O P hP) :
    FragmentSplitParentInitialBlockingRootOutcome O P hP := by
  have hfragment : P ∈ GroundingCut.fragments
      (L.popularAuxiliaryInput hL.legal) S.cut := hP.1.1
  cases outcome with
  | reservedParent heq hnot =>
      rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
          (L.popularAuxiliaryInput hL.legal) S.cut P hfragment with
        hfirst | hcut
      · exact .reservedFirst heq hfirst hnot
      · exact .reservedCutPredecessor heq hcut hnot
  | hangingParent hhang hnot =>
      rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
          (L.popularAuxiliaryInput hL.legal) S.cut P hfragment with
        hfirst | hcut
      · exact .hangingFirst hhang hfirst hnot
      · exact .hangingCutPredecessor hhang hcut hnot
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl q data recursion =>
      exact .inactiveControl q data recursion
  | ownerRecursion owner D recursion =>
      exact .ownerRecursion owner D recursion

/-- Root-failure normal form with the final parent-initial leaves refined by
the actual position of the surviving fragment in its parent. -/
inductive FragmentSplitParentInitialRootFailureOutcome
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
      (recursion : FragmentSplitParentInitialBlockingRootOutcome
        O P blockable)

/-- Every root obstruction has the fragment-split normal form. -/
theorem fragmentSplitParentInitialRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    FragmentSplitParentInitialRootFailureOutcome O := by
  cases O.classifiedParentInitialRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.fragmentSplit

/-! ## Provenance-preserving first-fragment form

The preceding extensional refinement is useful for arbitrary values of the
older public outcome.  The actual recursive producer contains more
information: a cut predecessor is immediately fed back into the control
recursion.  The next form performs that reduction before forgetting the
proof that the surviving fragment is the first fragment of its parent. -/

/-- Exact producer-side form: the only remaining reserved/hanging leaves are
first fragments.  A cut-preceded fragment has already become an active or
inactive control recursion. -/
inductive FirstFragmentParentBlockingRootOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Prop
  | reservedFirst
      (parent_eq : P.parent = R.record)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | hangingFirst
      (parent_hanging : PopularAuxiliary.IsHangingPath Gamma P.parent)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
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

/-- Resolve cut-preceded initial failures before classifying the parent as
reserved or hanging.  This is the information-preserving version of the
older two-step classifiers. -/
theorem UniformRecursiveBlockingRootOutcome.firstFragmentParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : UniformRecursiveBlockingRootOutcome O P hP) :
    FirstFragmentParentBlockingRootOutcome O P hP := by
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
      · have hparentNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen
              (fun x y ↦
                (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
              a P.parent.initial := by
          simpa only [hfirst] using hnot
        rcases parent_eq_reserved_or_hanging_of_initial_not_rooted
            P hparentNot with heq | hhang
        · exact .reservedFirst heq hfirst hparentNot
        · exact .hangingFirst hhang hfirst hparentNot
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
            ((ReservedActiveAnchorFailure.of_exit_not_rooted d hexitNot)
              |>.ownerClassified.recursivelyClassified)
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

/-- Total root-failure outcome retaining the first-fragment fact on both
unrooted parent leaves. -/
inductive FirstFragmentParentRootFailureOutcome
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
      (recursion : FirstFragmentParentBlockingRootOutcome O P blockable)

/-- Every root obstruction has the provenance-preserving first-fragment
normal form. -/
theorem firstFragmentParentRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    FirstFragmentParentRootFailureOutcome O := by
  cases O.uniformRecursiveRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.firstFragmentParent

end Assertion822PreStoppedRootObstruction

/-- Public Assertion 8.22 compiler whose only raw parent leaves have already
been split into first-fragment and deleted-cut-predecessor cases. -/
theorem assertion822Output_or_hindrance_of_preStoppedFragmentSplitRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FragmentSplitParentInitialRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedClassifiedParentInitialRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.fragmentSplitParentInitialRootFailureOutcome
  · exact repairBoundary

/-- Source-faithful public compiler retaining the proof that every raw
reserved/hanging leaf is the first surviving fragment of its parent. -/
theorem assertion822Output_or_hindrance_of_preStoppedFirstFragmentParentRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FirstFragmentParentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedUniformRecursiveRootRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.firstFragmentParentRootFailureOutcome
  · intro R O _outcome
    exact repairBoundary R O O.finiteSinkReducedTerminalFailureOutcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ClassifiedParentInitialBlockingRootOutcome.fragmentSplit
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.fragmentSplitParentInitialRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFragmentSplitRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.UniformRecursiveBlockingRootOutcome.firstFragmentParent
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.firstFragmentParentRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFirstFragmentParentRepairs
