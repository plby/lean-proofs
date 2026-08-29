/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBackwardSelfNormalization
import ErdosProblems.Erdos599.GroundingPreStoppedFirstFragmentBlockabilitySplit

/-!
# Total root outcome after self-backward normalization

`GroundingPreStoppedBackwardSelfNormalization` performs the well-founded
normalization of one exposed deleted-head state.  This file threads that
normalizer through every producer of such a state in the current public root
outcome: active anchors, inactive-control segments, and blocking prefixes.

The resulting callback no longer sees a raw selected-edge recursion.  Its
only recursive terminal is `BackwardSelfNormalizedRootOutcome`, which has
already eliminated every unrooted grounded backward anchor, descending by
control rank and then by position.  Rooted backward anchors, hanging equal
matches, and same-tail forward exchanges remain explicit, as do the genuine
reserved/hanging first-fragment escape/terminal leaves.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- A last deleted head inherits non-rootedness from the endpoint of its
surviving suffix. -/
theorem lastDeletedHead_head_not_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (D : LastDeletedHead p
      (L.assertion822ReservedPreStoppedEdges hL S R))
    (hfinish : p.finish = O.boundary) :
    ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a D.head := by
  rintro ⟨a, ha, haHead⟩
  apply O.not_rooted
  refine ⟨a, ha, haHead.trans ?_⟩
  have hreach := finitePath_start_reaches_of_mem_support
    D.suffix D.suffix_edgeSet_subset D.suffix.finish_mem_support
  simpa only [D.suffix_start, D.suffix_finish, hfinish] using hreach

/-- Forget the provenance wrapper after an active-anchor normalization. -/
theorem BackwardSelfNormalizedReservedActiveAnchorFailure.outcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (failure : BackwardSelfNormalizedReservedActiveAnchorFailure (R := R)) :
    BackwardSelfNormalizedRootOutcome (R := R) := by
  cases failure with
  | initial _d _data normalized => exact normalized
  | backwardOwner _d _l _parent _hl _hdir _hsub _data normalized =>
      exact normalized
  | hangingEqualMatch d certificate =>
      exact .hangingEqualMatch d certificate

/-- First-fragment blocking outcome after normalizing every exposed
deleted-head recursion. -/
inductive BackwardSelfNormalizedFirstFragmentBlockingRootOutcome
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
  | normalized (outcome : BackwardSelfNormalizedRootOutcome (R := R))

/-- Normalize every recursive constructor in a first-fragment blocking
outcome.  In the blocking-prefix case the non-rootedness of the deleted head
is recovered from its surviving suffix to the displayed boundary point. -/
theorem FirstFragmentBlockabilityBlockingRootOutcome.backwardSelfNormalized
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    {hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut}
    (hboundary : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
    (outcome : FirstFragmentBlockabilityBlockingRootOutcome O P hP) :
    BackwardSelfNormalizedFirstFragmentBlockingRootOutcome O P hP := by
  cases outcome with
  | reservedEscape heq hfirst hescape hnot =>
      exact .reservedEscape heq hfirst hescape hnot
  | reservedTerminal heq hfirst t ht hnotEscape hnot =>
      exact .reservedTerminal heq hfirst t ht hnotEscape hnot
  | hangingEscape hhang hfirst hescape hnot =>
      exact .hangingEscape hhang hfirst hescape hnot
  | hangingTerminal hhang hfirst t ht hnotEscape hnot =>
      exact .hangingTerminal hhang hfirst t ht hnotEscape hnot
  | activeAnchor failure =>
      exact .normalized failure.backwardSelfNormalized.outcome
  | inactiveControl _q data _recursion =>
      exact .normalized
        (Assertion822PreStoppedRootObstruction.InactivePreStoppedRootObstructionData.toExposedRootState
          data).normalizeBackwardSelf
  | ownerRecursion owner D recursion =>
      let Q := GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P hP
      let state : ReservedExposedRootState (R := R) := {
        control := owner
        parent := P.parent
        rootPath := Q.path
        rootPath_support := fun _ hx ↦ P.support_subset (Q.support_subset hx)
        rootPath_edges := fun _ he ↦ blockingPrefix_edge_mem_parent hP he
        deleted := D
        deleted_head_not_rooted := O.lastDeletedHead_head_not_rooted D
          (Q.finish_eq.trans hboundary)
        recursion := recursion }
      exact .normalized state.normalizeBackwardSelf

/-- Total root-failure outcome after well-founded elimination of every
grounded self-owned backward recursion exposed by the current producer. -/
inductive BackwardSelfNormalizedFirstFragmentRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | normalized (outcome : BackwardSelfNormalizedRootOutcome (R := R))
  | blocking
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (outcome : BackwardSelfNormalizedFirstFragmentBlockingRootOutcome
        O P blockable)

/-- Every pre-stopped root obstruction admits the fully threaded
self-backward-normalized outcome. -/
theorem backwardSelfNormalizedFirstFragmentRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    BackwardSelfNormalizedFirstFragmentRootFailureOutcome O := by
  cases O.firstFragmentBlockabilityRootFailureOutcome with
  | normalizedFinite data => exact .normalizedFinite data
  | activeAnchor failure =>
      exact .normalized failure.backwardSelfNormalized.outcome
  | inactiveControl _c _heq data _recursion =>
      exact .normalized
        (Assertion822PreStoppedRootObstruction.InactivePreStoppedRootObstructionData.toExposedRootState
          data).normalizeBackwardSelf
  | blocking P hP heq recursion =>
      exact .blocking P hP heq (recursion.backwardSelfNormalized heq)

end Assertion822PreStoppedRootObstruction

/-- Public Assertion 8.22 compiler after globally threading the
self-backward normalizer through the root-failure producer. -/
theorem assertion822Output_or_hindrance_of_preStoppedBackwardSelfNormalizedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedFirstFragmentBlockabilityRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.backwardSelfNormalizedFirstFragmentRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.lastDeletedHead_head_not_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.FirstFragmentBlockabilityBlockingRootOutcome.backwardSelfNormalized
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.backwardSelfNormalizedFirstFragmentRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedBackwardSelfNormalizedRepairs
