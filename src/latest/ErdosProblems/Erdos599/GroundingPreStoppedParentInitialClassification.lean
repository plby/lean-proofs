/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedFiniteBoundarySink

/-!
# Classifying an unrooted limiting-ladder parent initial

A limiting-ladder component whose initial vertex belongs to the original
source is already rooted by a reflexive path, unless it is the reserved
grounded record itself.  Indeed, two members of the limiting warp sharing
their initial vertex are equal.  Thus the last raw parent-initial case in the
pre-stopped root classifier is either the reserved record or a genuinely
hanging component.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- A limiting-ladder parent with an unrooted initial vertex is either the
reserved grounded record or is genuinely hanging. -/
theorem parent_eq_reserved_or_hanging_of_initial_not_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a P.parent.initial) :
    P.parent = R.record ∨
      PopularAuxiliary.IsHangingPath Gamma P.parent := by
  by_cases hground : PopularAuxiliary.IsGroundedPath Gamma P.parent
  · left
    by_contra hne
    have hinitial_ne : P.parent.initial ≠ R.record.initial := by
      intro heq
      apply hne
      have hlimitWarp : Gamma.IsWarp L.limitWarp := by
        simpa [KappaLadder.limitWarp] using
          hL.legal.warpStages (Ladder.finalStage kappa)
      have hparent := P.parent_mem
      change P.parent ∈ L.limitWarp at hparent
      apply Alternating.DWeb.IsWarp.eq_of_mem_support
        hlimitWarp
        hparent
        R.limit_inessential.1
      · exact P.parent.initial_mem_support
      · rw [heq]
        exact R.record.initial_mem_support
    apply hnot
    exact ⟨P.parent.initial,
      ⟨hground, by
        simpa only [Set.mem_singleton_iff] using hinitial_ne⟩,
      Relation.ReflTransGen.refl⟩
  · exact Or.inr hground

/-- Blocking recursion after replacing an arbitrary unrooted parent initial
by the exact reserved-or-hanging dichotomy. -/
inductive ClassifiedParentInitialBlockingRootOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Prop
  | reservedParent
      (parent_eq : P.parent = R.record)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | hangingParent
      (parent_hanging : PopularAuxiliary.IsHangingPath Gamma P.parent)
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

/-- Classify the last raw parent-initial constructor. -/
theorem ParentInitialRecursiveBlockingRootOutcome.classifyParentInitial
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : ParentInitialRecursiveBlockingRootOutcome O P hP) :
    ClassifiedParentInitialBlockingRootOutcome O P hP := by
  cases outcome with
  | parentInitialNotRooted hnot =>
      rcases parent_eq_reserved_or_hanging_of_initial_not_rooted P hnot with
        heq | hhang
      · exact .reservedParent heq hnot
      · exact .hangingParent hhang hnot
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl q data recursion =>
      exact .inactiveControl q data recursion
  | ownerRecursion owner D recursion =>
      exact .ownerRecursion owner D recursion

/-- Total root-failure outcome with the remaining parent initial classified
as reserved or hanging. -/
inductive ClassifiedParentInitialRootFailureOutcome
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
      (recursion : ClassifiedParentInitialBlockingRootOutcome O P blockable)

/-- Every pre-stopped root obstruction admits the classified parent-initial
normal form. -/
theorem classifiedParentInitialRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    ClassifiedParentInitialRootFailureOutcome O := by
  cases O.parentInitialRecursiveRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.classifyParentInitial

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler whose only parent-initial failures
are the reserved record and genuinely hanging limiting components, and whose
boundary outcome has already eliminated a finite cut source as the earlier
endpoint. -/
theorem assertion822Output_or_hindrance_of_preStoppedClassifiedParentInitialRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.ClassifiedParentInitialRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedFiniteSinkRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.classifiedParentInitialRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.parent_eq_reserved_or_hanging_of_initial_not_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.classifiedParentInitialRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedClassifiedParentInitialRepairs
