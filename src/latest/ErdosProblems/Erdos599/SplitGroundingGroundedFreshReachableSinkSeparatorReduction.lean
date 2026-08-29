/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshReachableSinkWarp

/-!
# The rooted source-first frontier lies in the dynamic sink boundary

The canonical switched relation is stopped at the source-first relevant
frontier.  Consequently every point of that frontier is a literal sink.
If all of those points are also reachable from the allowed original
sources, the source-first frontier is contained in the dynamic reachable
sink boundary.  Since the former already separates the ambient source and
target, so does the latter.

This is the exact positive branch of the separator compiler.  No claim is
made that reachability from `source \ {reserved}` is automatic; the
remaining exchange argument must either establish it or directly produce
the ambient hindrance.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ReachableSeparatorIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ReachableSeparatorControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ReachableSeparatorRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev ReachableSeparatorFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

private abbrev ReachableSeparatorEdges : Set (V × V) :=
  L.splitGroundedFreshRelevantSwitchedEdges
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

private abbrev ReachableSeparatorSources : Set V :=
  Gamma.source \ {
    (ReachableSeparatorRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- Reachability of every stopped source-first point puts that entire
frontier inside the actual reachable-sink boundary. -/
theorem splitGroundedFreshRelevantStoppingFrontier_subset_reachableSinkBoundary
    (hroot : ∀ t ∈ ReachableSeparatorFrontier
        (L := L) (hL := hL) (S := S),
      ∃ a ∈ ReachableSeparatorSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReachableSeparatorEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t) :
    ReachableSeparatorFrontier (L := L) (hL := hL) (S := S) ⊆
      L.splitGroundedFreshReachableSinkBoundary
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
  intro t ht
  refine ⟨hroot t ht, ?_⟩
  exact boundary_noOutgoing_switchedAt
    (ReachableSeparatorIndexed (L := L) (hL := hL)
      (hground := hground)) S
    (ReachableSeparatorControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (ReachableSeparatorFrontier (L := L) (hL := hL) (S := S)) ht

/-- Positive separator branch: a rooted source-first stopping frontier is
already a separating subset of the dynamic sink boundary. -/
theorem splitGroundedFreshReachableSinkBoundary_isSeparator_of_frontier_rooted
    (hC : Popular.IsSeparator
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut)
    (hroot : ∀ t ∈ ReachableSeparatorFrontier
        (L := L) (hL := hL) (S := S),
      ∃ a ∈ ReachableSeparatorSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReachableSeparatorEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t) :
    Popular.IsSeparator Gamma
      (L.splitGroundedFreshReachableSinkBoundary
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) := by
  have hsubset :=
    L.splitGroundedFreshRelevantStoppingFrontier_subset_reachableSinkBoundary
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) hroot
  intro p hpSource hpTarget
  obtain ⟨t, htp, htT⟩ :=
    L.splitGroundedRelevantSourceFirstBB_isSeparator
      hL.legal S.cut hC p hpSource hpTarget
  exact ⟨t, htp, hsubset htT⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevantStoppingFrontier_subset_reachableSinkBoundary
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshReachableSinkBoundary_isSeparator_of_frontier_rooted
