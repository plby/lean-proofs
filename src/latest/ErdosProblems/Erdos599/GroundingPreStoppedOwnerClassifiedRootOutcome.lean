/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBackwardAnchorClassification

/-!
# Owner-classified active anchors in the pre-stopped root outcome

The grounded-prefix certificate for an unrooted active anchor has a last
deleted head.  Its parent is exposed by the same selected request.  Hence
the deleted edge has one of four exact causes: a represented cut edge, a
backward edge owned by the same or a strictly earlier active request, a
same-tail forward conflict owned by the same or a strictly earlier active
request, or a same-head retained vertex.  The last alternative is kept as
an actual retained vertex so that it can be fed back into the active-anchor
recursion without a rooting assumption.

It is important to perform this refinement directly on
`ReservedActiveAnchorFailure`: the older fully-classified wrapper quite
deliberately forgot the link-membership witnesses of a backward anchor.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- The equal-stage certificate retained in the hanging backward-owner
branch.  This local spelling keeps the owner-classified reduction
independent of the older wrapper which forgets backward-link provenance. -/
def OwnerClassifiedReservedActiveEqualMatch
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

/-- An active-anchor failure after retaining the exact exposed-parent
owner split of its last deleted head. -/
inductive OwnerClassifiedReservedActiveAnchorFailure
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} : Prop
  | initialDeleted
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (data : ReservedActiveInitialLastDeletedHeadData d)
      (ownerSplit : data.DeletedOwnerRankOrRetainedHead)
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
      (ownerSplit : data.DeletedOwnerRankOrRetainedHead)
  | hangingEqualMatch
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (certificate : OwnerClassifiedReservedActiveEqualMatch d)

/-- Expand an active anchor while its backward-link provenance is still
available, and immediately orient every owned deletion by control rank. -/
theorem ReservedActiveAnchorFailure.ownerClassified
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (failure : ReservedActiveAnchorFailure (R := R)) :
    OwnerClassifiedReservedActiveAnchorFailure (R := R) := by
  cases failure with
  | initial d hnot =>
      let data :=
        (exists_reservedActiveInitialLastDeletedHeadData d hnot).some
      exact .initialDeleted d data data.deletedOwnerRank_or_retainedHead
  | backwardOwner d l parent hl hldir hparent hsub hne hnot =>
      rcases exists_reservedBackwardOwnerLastDeletedHeadData_or_equalMatch
          d l parent hl hldir hparent hsub hne hnot with hdata | hmatch
      · let data := hdata.some
        exact .backwardOwnerDeleted d l parent hl hldir hsub data
          (data.deletedOwnerRank_or_retainedHead hl hldir hsub)
      · exact .hangingEqualMatch d (by
          simpa only [OwnerClassifiedReservedActiveEqualMatch] using hmatch)

/-- Root-failure classifier in which every active-anchor deletion has its
root-assumption-free owner split. -/
inductive OwnerClassifiedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | activeAnchor
      (failure : OwnerClassifiedReservedActiveAnchorFailure (R := R))
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

/-- Every pre-stopped root obstruction has the owner-classified outcome. -/
theorem ownerClassifiedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    OwnerClassifiedRootFailureOutcome O := by
  cases O.activeAnchorReducedRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure.ownerClassified
  | inactiveControl c heq data => exact .inactiveControl c heq data
  | blockingInitial P hP heq hnot =>
      exact .blockingInitial P hP heq hnot
  | blockingBackward P hP heq e hePrefix heBackward =>
      exact .blockingBackward P hP heq e hePrefix heBackward
  | blockingForwardConflict P hP heq e hePrefix heConflict =>
      exact .blockingForwardConflict P hP heq e hePrefix heConflict

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler whose active callback retains the
root-assumption-free deleted-owner split. -/
theorem assertion822Output_or_hindrance_of_preStoppedOwnerClassifiedRootRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.OwnerClassifiedRootFailureOutcome →
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
    exact repairRoot R O O.ownerClassifiedRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedActiveAnchorFailure.ownerClassified
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ownerClassifiedRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedOwnerClassifiedRootRepairs
