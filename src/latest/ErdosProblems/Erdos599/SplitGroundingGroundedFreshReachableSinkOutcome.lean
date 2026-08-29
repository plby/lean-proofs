/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshReachableSinkSeparatorReduction

/-!
# Closing the source-reachable sink outcome

The global last-contact exchange has two truthful successful outcomes.  It
may already produce an ambient hindrance, or it may root every point of the
source-first stopping frontier from the allowed original sources.  The
second outcome makes the dynamic reachable-sink boundary separating and the
concrete source-reachable warp then gives the ambient hindrance.

This file is only the deterministic consumer of that disjunction.  It does
not package either branch as a new hypothesis of the public grounding
theorem.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev SinkOutcomeRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev SinkOutcomeFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

private abbrev SinkOutcomeEdges : Set (V × V) :=
  L.splitGroundedFreshRelevantSwitchedEdges
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

private abbrev SinkOutcomeSources : Set V :=
  Gamma.source \ {
    (SinkOutcomeRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- Consume the exact global exchange outcome once the positive branch is
already phrased as separation by the dynamic reachable-sink boundary. -/
theorem exists_hindrance_of_splitGroundedFreshReachableSinkOutcome
    (hout : (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      Popular.IsSeparator Gamma
        (L.splitGroundedFreshReachableSinkBoundary
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases hout with h | h
  · exact h
  · exact
      L.exists_hindrance_of_splitGroundedFreshReachableSinkSeparator
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) h

/-- Consume the source-faithful last-contact outcome in its more useful
rooted-frontier form.  The positive branch is converted to a separating
dynamic sink boundary by the source-first separator bridge. -/
theorem exists_hindrance_of_splitGroundedFreshFrontierRootedOutcome
    (hC : Popular.IsSeparator
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut)
    (hout : (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∀ t ∈ SinkOutcomeFrontier (L := L) (hL := hL) (S := S),
        ∃ a ∈ SinkOutcomeSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ SinkOutcomeEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.exists_hindrance_of_splitGroundedFreshReachableSinkOutcome
    (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  rcases hout with h | hroot
  · exact Or.inl h
  · exact Or.inr
      (L.splitGroundedFreshReachableSinkBoundary_isSeparator_of_frontier_rooted
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) hC hroot)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedFreshReachableSinkOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedFreshFrontierRootedOutcome
