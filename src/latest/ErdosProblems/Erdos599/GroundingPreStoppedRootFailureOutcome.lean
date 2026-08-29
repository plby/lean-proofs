/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRootCases
import ErdosProblems.Erdos599.GroundingPreStoppedRootClassification

/-!
# Exact finite outcomes of a pre-stopped root obstruction

This module composes the literal `BB` trichotomy with the deleted-head and
blocking-prefix classifiers.  The result is a single lossless certificate:
every root obstruction is localized to a finite parent deletion, an active
or inactive control route, or an explicit toggle collision on a blocking
prefix.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder
namespace Assertion822PreStoppedRootObstruction

open GroundingErasedDecode PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Lossless construction-level classification of an unrooted literal
boundary point in the reserved pre-stopped relation. -/
inductive FailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | finite
      (hfinite : O.boundary ∈
        (L.popularAuxiliaryInput hL.legal).finiteSource)
      (hcut : (PopularAuxiliary.Input.LambdaVertex.old O.boundary :
        (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut)
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
      (hchosen : L.chosen
        (L.finiteTerminalIndex ⟨O.boundary, hfinite⟩) =
          some (.inl p : Gamma.DPath))
      (D : LastDeletedHead p
        (L.assertion822ReservedPreStoppedEdges hL S R))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a D.head)
      (deleted_class :
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ GroundingCut.CE
            (L.popularAuxiliaryInput hL.legal) S.cut) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ erasedSelectedDirectionEdgesAt
            (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) ∅ .backward) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ forwardConflictCutEdgesAt
            (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) ∅))
  | activeControl
      (c : ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : c.1 = O.boundary)
      (active : IsActiveControlAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ c)
  | activeRetainedVertex
      (c : ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : c.1 = O.boundary)
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)
      (x : V)
      (retained : x ∈ retainedForwardVerticesAt ∅
        (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).path)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a x)
  | inactiveControl
      (c : ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut)
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

/-- Every pre-stopped root obstruction has one of the exact finite outcomes
above. -/
theorem failureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    FailureOutcome O := by
  rcases O.boundary_cases with
      hfinite | ⟨c, hc⟩ | ⟨P, hPG0, hblockable, hboundary⟩
  · obtain ⟨p, hchosen, D, hnot, hclass⟩ :=
      O.exists_unrootedClassifiedLastDeletedHead_of_finiteSource
        hfinite.1 hfinite.2
    exact .finite hfinite.1 hfinite.2 p hchosen D hnot hclass
  · rcases O.control_cases c hc with hactive | hrest
    · exact .activeControl c hc hactive
    · rcases hrest with ⟨d, x, hx, hnot⟩ | hinactive
      · exact .activeRetainedVertex c hc d x hx hnot
      · obtain ⟨data⟩ := hinactive
        exact .inactiveControl c hc data
  · let hPblockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut :=
      ⟨hPG0, hblockable⟩
    rcases O.blocking_cases P hPblockable hboundary with
      hinitial | ⟨e, hePrefix, heBackward⟩ |
        ⟨e, hePrefix, heConflict⟩
    · exact .blockingInitial P hPblockable hboundary hinitial
    · exact .blockingBackward P hPblockable hboundary e
        hePrefix heBackward
    · exact .blockingForwardConflict P hPblockable hboundary e
        hePrefix heConflict

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.failureOutcome
