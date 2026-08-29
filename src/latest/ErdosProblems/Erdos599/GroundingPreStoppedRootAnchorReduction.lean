/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBlockingInitialReduction

/-!
# Root-anchor reduction for the pre-stopped Assertion 8.22 compiler

If every auxiliary control exit is source-rooted, none of the three
control-shaped constructors can witness an unrooted boundary.  If, in
addition, every blockable fragment parent's initial vertex is source-rooted,
the fragment-predecessor dichotomy eliminates the `blockingInitial` case.

Thus the normalized root failure has only three honest outcomes: the
canonical finite backward switch, a selected backward edge on a blocking
prefix, or a forward-conflict edge on such a prefix.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- The root classifier after request exits and fragment-parent initials
have been proved source-rooted. -/
inductive AnchorReducedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | blockingBackward
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (e : V × V)
      (prefix_edge : e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P blockable).path.edgeSet)
      (selected_backward : e ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
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
      (forward_conflict : e ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅)

/-- Rooted control exits and rooted fragment-parent initials reduce the
total normalized classifier to the three constructors above. -/
theorem anchorReducedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (hcontrol : ∀ c : GroundingErasedDecode.ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a c.1)
    (hparent : ∀
        (P : (L.popularAuxiliaryInput hL.legal).Fragment),
      P ∈ GroundingCut.blockableG0
          (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial) :
    AnchorReducedRootFailureOutcome O := by
  cases O.backwardNormalizedRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeControl c heq _hactive =>
      exfalso
      apply O.not_rooted
      obtain ⟨a, ha, hareach⟩ := hcontrol c
      exact ⟨a, ha, by simpa only [heq] using hareach⟩
  | activeRetainedVertex c heq _d _x _hx _hnot =>
      exfalso
      apply O.not_rooted
      obtain ⟨a, ha, hareach⟩ := hcontrol c
      exact ⟨a, ha, by simpa only [heq] using hareach⟩
  | inactiveControl c heq _data =>
      exfalso
      apply O.not_rooted
      obtain ⟨a, ha, hareach⟩ := hcontrol c
      exact ⟨a, ha, by simpa only [heq] using hareach⟩
  | blockingInitial P hP _heq hnot =>
      exact False.elim
        (O.not_blockingInitial_of_control_and_parent_rooted
          P hP hnot hcontrol (hparent P hP))
  | blockingBackward P hP heq e hePrefix heBackward =>
      exact .blockingBackward P hP heq e hePrefix heBackward
  | blockingForwardConflict P hP heq e hePrefix heConflict =>
      exact .blockingForwardConflict P hP heq e hePrefix heConflict

end Assertion822PreStoppedRootObstruction

/-- Public output-or-hindrance compiler after the root-anchor reduction.
The root repair callback sees only the canonical finite switch and the two
genuine selected-edge collisions on blocking prefixes. -/
theorem assertion822Output_or_hindrance_of_preStoppedRootAnchorRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hcontrol : ∀ (R : L.UnusedGroundedRecord hL S)
        (c : GroundingErasedDecode.ControlRequest
          (L.popularAuxiliaryInput hL.legal) S.cut),
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a c.1)
    (hparent : ∀ (R : L.UnusedGroundedRecord hL S)
        (P : (L.popularAuxiliaryInput hL.legal).Fragment),
      P ∈ GroundingCut.blockableG0
          (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.AnchorReducedRootFailureOutcome →
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
    exact repairRoot R O
      (O.anchorReducedRootFailureOutcome (hcontrol R) (hparent R))
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.anchorReducedRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedRootAnchorRepairs
