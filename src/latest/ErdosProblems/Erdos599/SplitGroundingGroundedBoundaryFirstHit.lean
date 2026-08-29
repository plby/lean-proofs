/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryOwner
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# First-hit normalization of a grounded split boundary obstruction

An ordered obstruction may pass through other members of `BB` before its
displayed later endpoint.  We replace it by the first distinct boundary
point on a finite simple path in the actual pre-stopped relation.  The two
endpoints are then classified by their finite/control/blocking owners.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedFirstHitInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedFirstHitIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- A concrete first-distinct-boundary representative of an ordered raw
boundary obstruction. -/
structure SplitGroundedFirstBoundaryReduction
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) where
  reduced : L.SplitGroundedPreStoppedBoundaryObstruction R
  earlier_eq : reduced.earlier = O.earlier
  path : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  start_eq : path.start = reduced.earlier
  finish_eq : path.finish = reduced.later
  edgeSet_subset : path.edgeSet ⊆
    erasedSelectedSwitchedEdgesAt
      (GroundedFirstHitIndexed (L := L) (hL := hL)
        (hground := hground)) S K ∅
  no_boundary_before : ∀ {x : V},
    x ∈ path.walk.support.dropLast →
    x ∉ GroundingCut.BB
      (GroundedFirstHitInput (L := L) (hL := hL)) S.cut \
        {reduced.earlier}

/-- Every ordered obstruction admits a first-hit representative in the
same literal pre-stopped relation. -/
theorem SplitGroundedPreStoppedBoundaryObstruction.exists_firstBoundaryReduction
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) :
    Nonempty (L.SplitGroundedFirstBoundaryReduction R O) := by
  classical
  let E := erasedSelectedSwitchedEdgesAt
    (GroundedFirstHitIndexed (L := L) (hL := hL)
      (hground := hground)) S K ∅
  let B := GroundingCut.BB
    (GroundedFirstHitInput (L := L) (hL := hL)) S.cut \ {O.earlier}
  have hroot : ∃ a ∈ ({O.earlier} : Set V),
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a O.later :=
    ⟨O.earlier, Set.mem_singleton O.earlier, O.reaches⟩
  obtain ⟨P⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
      (Gamma := Gamma)
      (erasedSelectedSwitchedEdgesAt_subset_adj
        (GroundedFirstHitIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅)
      hroot
  have hstart : P.path.start = O.earlier :=
    Set.mem_singleton_iff.mp P.start_mem
  have hfinishB : P.path.finish ∈ B := by
    rw [P.finish_eq]
    exact ⟨O.later_mem, fun h ↦ O.distinct h.symm⟩
  have hmeet : P.path.walk.Meets B :=
    ⟨P.path.finish, P.path.finish_mem_support, hfinishB⟩
  let q := P.path.firstHit B hmeet
  have hqStart : q.start = O.earlier := by
    change P.path.start = O.earlier
    exact hstart
  have hqFinishB : q.finish ∈ B :=
    P.path.firstHit_finish_mem B hmeet
  have hqEdges : q.edgeSet ⊆ E :=
    (P.path.firstHit_edgeSet_subset B hmeet).trans P.edgeSet_subset
  have hqReach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) q.start q.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ q.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact hqEdges hxy
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet q.walk
  let reduced : L.SplitGroundedPreStoppedBoundaryObstruction R :=
    { earlier := O.earlier
      later := q.finish
      earlier_mem := O.earlier_mem
      later_mem := hqFinishB.1
      distinct := fun h ↦ hqFinishB.2 h.symm
      reaches := by simpa only [hqStart] using hqReach }
  refine ⟨{
    reduced := reduced
    earlier_eq := rfl
    path := q
    start_eq := hqStart
    finish_eq := rfl
    edgeSet_subset := hqEdges
    no_boundary_before := ?_ }⟩
  intro x hx
  change x ∉ B
  exact P.path.firstHit_no_mem_before B hmeet hx

/-- First-hit data together with the exact owner of both endpoint boundary
vertices.  Pattern matching the two owner fields gives all nine ordered
finite/control/blocking cases. -/
structure SplitGroundedFirstBoundaryOwnerPair
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) where
  reduction : L.SplitGroundedFirstBoundaryReduction R O
  earlier_owner : SplitGroundedBBPointOwner
    (L := L) (hL := hL) (hground := hground) (S := S)
      reduction.reduced.earlier
  later_owner : SplitGroundedBBPointOwner
    (L := L) (hL := hL) (hground := hground) (S := S)
      reduction.reduced.later

/-- Produce the first-hit ordered owner-pair normal form. -/
theorem SplitGroundedPreStoppedBoundaryObstruction.exists_firstBoundaryOwnerPair
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) :
    Nonempty (L.SplitGroundedFirstBoundaryOwnerPair R O) := by
  obtain ⟨D⟩ := O.exists_firstBoundaryReduction R
  exact ⟨{
    reduction := D
    earlier_owner :=
      L.splitGroundedBBPointOwner_of_mem D.reduced.earlier_mem
    later_owner :=
      L.splitGroundedBBPointOwner_of_mem D.reduced.later_mem }⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedPreStoppedBoundaryObstruction.exists_firstBoundaryOwnerPair
