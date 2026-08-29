/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingControlNormalization

/-!
# Elimination of a retained-forward-head root failure

A same-head forward conflict is not a terminal exchange.  Its deleted head
is itself a retained forward vertex of the selected owner.  The active
forward-vertex normalizer therefore either roots that head, contradicting
the root state's stored non-rootedness, or returns the earlier initial or
backward-anchor obstruction of the owner route.

The same-tail constructor is deliberately not treated here.  It really
diverts the switched component away from the old parent head and requires
the separate last-contact exchange.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open Alternating PopularGroundingBridge
open GroundingErasedDecode GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ForwardHeadIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ForwardHeadControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ForwardHeadRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev ForwardHeadEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

/-- A retained-forward-head constructor immediately restarts at the
selected owner's earlier source/backward anchor.  The apparent alternative
that the retained head is rooted contradicts the non-rootedness stored in
the original state. -/
theorem splitGroundedFreshAvoiding_retainedForwardHead_reduces_to_ownerAnchor
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (owner : ActiveControlRequestAt
      (ForwardHeadIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardHeadControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (f : V × V)
    (retained : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (ForwardHeadIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardHeadControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (head_eq : state.deleted.head = f.2) :
    L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) := by
  have hforward : f.2 ∈ (selectedErasedCompression
      (ForwardHeadIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardHeadControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.directionVertices .forward :=
    retainedForwardVerticesAt_subset_directionVertices ∅ _
      (retainedForwardEdgeAt_endpoints ∅ _ retained).2
  rcases L.splitGroundedFreshAvoiding_activeForwardVertex_rooted_or_normalized
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) owner hforward with hroot | hnormalized
  · exfalso
    apply state.deleted_head_not_rooted
    rw [head_eq]
    exact hroot
  · exact hnormalized

/-- Constructor-level form: every normalized retained-head leaf can be
replaced by the selected owner's source/backward-anchor normalization. -/
theorem SplitGroundedFreshAvoidingBackwardNormalizedOutcome.eliminateRetainedForwardHead
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (u : V)
    (owner : ActiveControlRequestAt
      (ForwardHeadIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardHeadControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (f : V × V)
    (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
    (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
      (ForwardHeadIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardHeadControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (retained : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (ForwardHeadIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardHeadControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (head_eq : state.deleted.head = f.2) :
    L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) := by
  exact L.splitGroundedFreshAvoiding_retainedForwardHead_reduces_to_ownerAnchor
    state owner f retained head_eq

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_retainedForwardHead_reduces_to_ownerAnchor
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingBackwardNormalizedOutcome.eliminateRetainedForwardHead
