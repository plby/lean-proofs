/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBoundaryCollisionCases
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# First-boundary normalization of a pre-stopped collision

An arbitrary ordered boundary obstruction may pass through further boundary
vertices before its displayed endpoint.  This file replaces it by the first
distinct `BB` point on a concrete simple relation path.  The resulting path
contains no member of `BB \ {earlier}` before its endpoint.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- A first-hit representative of an ordered pre-stopped boundary
collision. -/
structure FirstBoundaryReduction
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) where
  reduced : L.Assertion822PreStoppedBoundaryObstruction hL S R
  earlier_eq : reduced.earlier = o.earlier
  path : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  start_eq : path.start = reduced.earlier
  finish_eq : path.finish = reduced.later
  edgeSet_subset : path.edgeSet ⊆
    L.assertion822ReservedPreStoppedEdges hL S R
  no_boundary_before : ∀ {x : V},
    x ∈ path.walk.support.dropLast →
    x ∉ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut \ {reduced.earlier}

/-- Every ordered collision has a first-distinct-boundary representative. -/
theorem exists_firstBoundaryReduction
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    Nonempty (FirstBoundaryReduction o) := by
  classical
  let E := L.assertion822ReservedPreStoppedEdges hL S R
  let B := GroundingCut.BB
    (L.popularAuxiliaryInput hL.legal) S.cut \ {o.earlier}
  have hroot : ∃ a ∈ ({o.earlier} : Set V),
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a o.later :=
    ⟨o.earlier, Set.mem_singleton o.earlier, o.reaches⟩
  obtain ⟨P⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
      (Gamma := Gamma)
      (L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅)
      hroot
  have hstart : P.path.start = o.earlier := by
    exact Set.mem_singleton_iff.mp P.start_mem
  have hfinishB : P.path.finish ∈ B := by
    rw [P.finish_eq]
    exact ⟨o.later_mem, fun h ↦ o.distinct h.symm⟩
  have hmeet : P.path.walk.Meets B :=
    ⟨P.path.finish, P.path.finish_mem_support, hfinishB⟩
  let q := P.path.firstHit B hmeet
  have hqStart : q.start = o.earlier := by
    change P.path.start = o.earlier
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
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet
        q.walk
  let reduced : L.Assertion822PreStoppedBoundaryObstruction hL S R :=
    { earlier := o.earlier
      later := q.finish
      earlier_mem := o.earlier_mem
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

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.exists_firstBoundaryReduction
