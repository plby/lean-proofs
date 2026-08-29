/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableOutcome
import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryDeparture

/-!
# First-hit normalization of the source-reachable grounded split boundary

The public grounded dispatcher uses `splitGroundedReachableBB`, not the full
literal `BB`.  This module transports the earlier full-boundary first-hit
geometry to that sound restricted boundary and proves that the newly chosen
later endpoint remains both ambient-source-reachable and rooted from the
allowed source set.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge GroundingErasedDecode
  GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ReachableControls :=
  L.splitGroundedCanonicalControls hL hground S

private abbrev ReachableRecord :=
  L.splitGroundedCanonicalUnusedRecord hL hground S

private abbrev ReachableEdges :=
  L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅

/-- Forget only the ambient-prefix decoration of a source-reachable
boundary obstruction.  Its endpoints remain literal members of `BB`, and
the relation is definitionally the canonical pre-stopped relation. -/
def SplitGroundedReachableBoundaryObstruction.toPreStopped
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) :
    L.SplitGroundedPreStoppedBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S)) where
  earlier := O.earlier
  later := O.later
  earlier_mem := O.earlier_mem.1
  later_mem := O.later_mem.1
  distinct := O.distinct
  reaches := O.reaches

/-- First-hit reduction within the public source-reachable boundary.  The
core path is the literal pre-stopped first-hit path; both endpoints are
again members of the restricted boundary and retain allowed roots. -/
structure SplitGroundedReachableFirstBoundaryReduction
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) where
  core : L.SplitGroundedFirstBoundaryReduction
    (ReachableRecord (L := L) (hL := hL)
      (hground := hground) (S := S)) O.toPreStopped
  earlier_mem : core.reduced.earlier ∈
    L.splitGroundedReachableBB hL hground S
  later_mem : core.reduced.later ∈
    L.splitGroundedReachableBB hL hground S
  earlier_rooted : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S))
      a core.reduced.earlier
  later_rooted : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S))
      a core.reduced.later

/-- A first distinct literal boundary hit reached after a source-reachable
endpoint is itself source-reachable. -/
theorem SplitGroundedReachableBoundaryObstruction.exists_firstBoundaryReduction
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) :
    Nonempty (L.SplitGroundedReachableFirstBoundaryReduction O) := by
  obtain ⟨D⟩ := O.toPreStopped.exists_firstBoundaryReduction
    (ReachableRecord (L := L) (hL := hL)
      (hground := hground) (S := S))
  have hrootEarlier : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReachableEdges
          (L := L) (hL := hL) (hground := hground) (S := S))
        a D.reduced.earlier := by
    simpa only [D.earlier_eq,
      SplitGroundedReachableBoundaryObstruction.toPreStopped] using
        O.earlier_rooted
  have hrootLater : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReachableEdges
          (L := L) (hL := hL) (hground := hground) (S := S))
        a D.reduced.later := by
    obtain ⟨a, ha, hareach⟩ := hrootEarlier
    exact ⟨a, ha, hareach.trans D.reduced.reaches⟩
  have hambientLater : splitGroundedAmbientSourceReachable Gamma
      D.reduced.later := by
    obtain ⟨a, ha, hareach⟩ := hrootLater
    obtain ⟨P⟩ :=
      GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
        (Gamma := Gamma)
        (L.splitGroundedCanonicalSwitchedEdgesAt_subset_adj
          hL hground S ∅)
        ⟨a, ha, hareach⟩
    exact ⟨P.path, P.start_mem, P.finish_eq⟩
  refine ⟨{
    core := D
    earlier_mem := ?_
    later_mem := ⟨D.reduced.later_mem, hambientLater⟩
    earlier_rooted := hrootEarlier
    later_rooted := hrootLater }⟩
  simpa only [D.earlier_eq,
    SplitGroundedReachableBoundaryObstruction.toPreStopped] using
      O.earlier_mem

/-- Owner-classified first-hit data for the public reachable-boundary
branch. -/
structure SplitGroundedReachableFirstBoundaryOwnerPair
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) where
  reduction : L.SplitGroundedReachableFirstBoundaryReduction O
  earlier_owner : SplitGroundedBBPointOwner
    (L := L) (hL := hL) (hground := hground)
      (S := S) reduction.core.reduced.earlier
  later_owner : SplitGroundedBBPointOwner
    (L := L) (hL := hL) (hground := hground)
      (S := S) reduction.core.reduced.later

/-- Produce the source-reachable first-hit owner-pair normal form. -/
theorem SplitGroundedReachableBoundaryObstruction.exists_firstBoundaryOwnerPair
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) :
    Nonempty (L.SplitGroundedReachableFirstBoundaryOwnerPair O) := by
  obtain ⟨D⟩ := O.exists_firstBoundaryReduction
  exact ⟨{
    reduction := D
    earlier_owner :=
      L.splitGroundedBBPointOwner_of_mem D.core.reduced.earlier_mem
    later_owner :=
      L.splitGroundedBBPointOwner_of_mem D.core.reduced.later_mem }⟩

/-- Reachable first-hit normal form after eliminating the impossible finite
first endpoint.  Both constructors retain the ambient and switched source
roots stored by `reduction`; the later endpoint remains fully classified. -/
inductive SplitGroundedReachableFirstBoundarySinkOutcome
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) : Prop
  | earlierControl
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (old : oldRequests
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (value_eq : old.1 = D.core.reduced.earlier)
      (departure : SplitGroundedFirstBoundaryDepartureOutcome D.core)
      (later_owner : SplitGroundedBBPointOwner
        (L := L) (hL := hL) (hground := hground) (S := S)
          D.core.reduced.later)
  | earlierBlocking
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (blockable : GroundingCut.IsBlockable
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P)
      (point_eq : GroundingCut.blockingPoint
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P =
          D.core.reduced.earlier)
      (point_mem_support : D.core.reduced.earlier ∈ P.path.support)
      (departure : SplitGroundedFirstBoundaryDepartureOutcome D.core)
      (later_owner : SplitGroundedBBPointOwner
        (L := L) (hL := hL) (hground := hground) (S := S)
          D.core.reduced.later)

/-- The public source-reachable boundary branch has exactly the six
control/blocking to finite/control/blocking first-hit cases. -/
theorem SplitGroundedReachableBoundaryObstruction.firstBoundarySinkOutcome
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) :
    SplitGroundedReachableFirstBoundarySinkOutcome O := by
  obtain ⟨D⟩ := O.exists_firstBoundaryOwnerPair
  cases D.earlier_owner with
  | finiteSource hfinite hcut =>
      exact False.elim
        (D.reduction.core.reduced.earlier_not_finiteSource
          (ReachableRecord (L := L) (hL := hL)
            (hground := hground) (S := S)) hfinite hcut)
  | oldControl old hvalue =>
      exact .earlierControl D.reduction old hvalue
        D.reduction.core.residual_or_firstSelectedForward D.later_owner
  | blocking P hPG0 hblockable hpoint hsupport =>
      exact .earlierBlocking D.reduction P hPG0 hblockable hpoint hsupport
        D.reduction.core.residual_or_firstSelectedForward D.later_owner

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableBoundaryObstruction.exists_firstBoundaryOwnerPair
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableBoundaryObstruction.firstBoundarySinkOutcome
