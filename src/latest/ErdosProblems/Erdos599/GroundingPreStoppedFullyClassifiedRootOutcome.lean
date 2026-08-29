/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBackwardAnchorClassification

/-!
# Fully classified active anchors in the pre-stopped root outcome

The two active-anchor alternatives are now construction-level positive
data.  A trace-initial failure has a grounded root prefix and a classified
last deleted head.  A backward-owner failure either has the same kind of
grounded prefix or is a genuine equal-stage hanging match from Assertion
8.19.  This file propagates that exact trichotomy through the total root and
Assertion 8.22 compilers without adding any rooting premise.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- The exact equal-stage certificate produced by a hanging backward owner
of the active request `d`. -/
def ReservedActiveEqualMatch
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)) : Prop :=
  let p := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (chosenRequest d.1)
  let hp : p.start ∈
      (L.popularAuxiliaryInput hL.legal).lambda.source :=
    (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)).starts_in_source
        ⟨chosenRequest d.1, rfl⟩
  Nonempty (L.Assertion819EqualMatch hL S (chosenRequest d.1)
    ((L.popularAuxiliaryIndexed hL).f ⟨p.start, hp⟩))

/-- The active-anchor failure after expanding both constructors into their
exact positive data. -/
inductive ClassifiedReservedActiveAnchorFailure
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} : Prop
  | initialDeleted
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (data : ReservedActiveInitialLastDeletedHeadData d)
  | backwardOwnerDeleted
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (data : ReservedBackwardOwnerLastDeletedHeadData d l parent)
  | hangingEqualMatch
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (certificate : ReservedActiveEqualMatch d)

/-- Expand an active anchor into a grounded deleted-head certificate or the
exact equal-stage match retained by Assertion 8.19. -/
theorem ReservedActiveAnchorFailure.classified
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (failure : ReservedActiveAnchorFailure (R := R)) :
    ClassifiedReservedActiveAnchorFailure (R := R) := by
  cases failure with
  | initial d hnot =>
      exact .initialDeleted d
        (exists_reservedActiveInitialLastDeletedHeadData d hnot).some
  | backwardOwner d l parent hl hldir hparent hsub hne hnot =>
      rcases exists_reservedBackwardOwnerLastDeletedHeadData_or_equalMatch
          d l parent hl hldir hparent hsub hne hnot with hdata | hmatch
      · exact .backwardOwnerDeleted d l parent hdata.some
      · exact .hangingEqualMatch d (by
          simpa only [ReservedActiveEqualMatch] using hmatch)

/-- Root-failure classifier after finite backward normalization and complete
active-anchor classification. -/
inductive FullyClassifiedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | activeAnchor
      (failure : ClassifiedReservedActiveAnchorFailure (R := R))
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

/-- Every pre-stopped root obstruction has the fully classified outcome. -/
theorem fullyClassifiedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    FullyClassifiedRootFailureOutcome O := by
  cases O.activeAnchorReducedRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure.classified
  | inactiveControl c heq data => exact .inactiveControl c heq data
  | blockingInitial P hP heq hnot =>
      exact .blockingInitial P hP heq hnot
  | blockingBackward P hP heq e hePrefix heBackward =>
      exact .blockingBackward P hP heq e hePrefix heBackward
  | blockingForwardConflict P hP heq e hePrefix heConflict =>
      exact .blockingForwardConflict P hP heq e hePrefix heConflict

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler whose active root callback has no
negative or abstract anchor constructor left. -/
theorem assertion822Output_or_hindrance_of_preStoppedFullyClassifiedRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FullyClassifiedRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedActiveAnchorRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.fullyClassifiedRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedActiveAnchorFailure.classified
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.fullyClassifiedRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFullyClassifiedRootRepairs
