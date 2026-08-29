/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedParentInitialFragmentSplit

/-!
# The escape/finite split for the remaining first-fragment root leaves

After cut-preceded fragments have been returned to the control recursion,
the only unstructured parent leaves in the pre-stopped Assertion 8.22
compiler are actual first fragments of the reserved record or of a hanging
limiting-ladder component.  Such a fragment belongs to `blockableG0`, so its
blockability proof gives the source-faithful final local dichotomy: the
fragment meets the escape region, or it is finite.

This file records that dichotomy without discarding the parent provenance or
the literal first-fragment equality.  It deliberately makes no claim that
either leaf is already rooted; the subsequent exchange/descent must use the
displayed escape witness or terminal.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Producer-side root recursion with the two genuine first-fragment leaves
split according to the definition of `GroundingCut.IsBlockable`. -/
inductive FirstFragmentBlockabilityBlockingRootOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut) : Prop
  | reservedEscape
      (parent_eq : P.parent = R.record)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : PopularAuxiliary.Input.Fragment.MeetsEscape
        (L.popularAuxiliaryInput hL.legal) S.cut P)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | reservedTerminal
      (parent_eq : P.parent = R.record)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (terminal : V)
      (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ PopularAuxiliary.Input.Fragment.MeetsEscape
        (L.popularAuxiliaryInput hL.legal) S.cut P)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | hangingEscape
      (parent_hanging : PopularAuxiliary.IsHangingPath Gamma P.parent)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : PopularAuxiliary.Input.Fragment.MeetsEscape
        (L.popularAuxiliaryInput hL.legal) S.cut P)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial)
  | hangingTerminal
      (parent_hanging : PopularAuxiliary.IsHangingPath Gamma P.parent)
      (fragment_initial_eq : P.path.initial = P.parent.initial)
      (terminal : V)
      (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ PopularAuxiliary.Input.Fragment.MeetsEscape
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

/-- Split the last first-fragment leaves into escape and finite cases. -/
theorem FirstFragmentParentBlockingRootOutcome.blockabilitySplit
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (outcome : FirstFragmentParentBlockingRootOutcome O P hP) :
    FirstFragmentBlockabilityBlockingRootOutcome O P hP := by
  cases outcome with
  | reservedFirst heq hfirst hnot =>
      by_cases hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
          (L.popularAuxiliaryInput hL.legal) S.cut P
      · exact .reservedEscape heq hfirst hescape hnot
      · obtain ⟨t, ht⟩ := hP.2.resolve_left hescape
        exact .reservedTerminal heq hfirst t ht hescape hnot
  | hangingFirst hhang hfirst hnot =>
      by_cases hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
          (L.popularAuxiliaryInput hL.legal) S.cut P
      · exact .hangingEscape hhang hfirst hescape hnot
      · obtain ⟨t, ht⟩ := hP.2.resolve_left hescape
        exact .hangingTerminal hhang hfirst t ht hescape hnot
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl q data recursion =>
      exact .inactiveControl q data recursion
  | ownerRecursion owner D recursion =>
      exact .ownerRecursion owner D recursion

/-- Total root-failure outcome retaining the first-fragment fact and the
escape/finite witness on each genuine parent leaf. -/
inductive FirstFragmentBlockabilityRootFailureOutcome
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
      (recursion : FirstFragmentBlockabilityBlockingRootOutcome
        O P blockable)

/-- Every root obstruction has the escape/finite first-fragment normal
form. -/
theorem firstFragmentBlockabilityRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    FirstFragmentBlockabilityRootFailureOutcome O := by
  cases O.firstFragmentParentRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure => exact .activeAnchor failure
  | inactiveControl c heq data recursion =>
      exact .inactiveControl c heq data recursion
  | blocking P hP heq recursion =>
      exact .blocking P hP heq recursion.blockabilitySplit

end Assertion822PreStoppedRootObstruction

/-- Public Assertion 8.22 compiler exposing the escape/finite split on the
only remaining raw first-fragment leaves. -/
theorem assertion822Output_or_hindrance_of_preStoppedFirstFragmentBlockabilityRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FirstFragmentBlockabilityRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedFirstFragmentParentRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.firstFragmentBlockabilityRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.FirstFragmentParentBlockingRootOutcome.blockabilitySplit
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.firstFragmentBlockabilityRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFirstFragmentBlockabilityRepairs
