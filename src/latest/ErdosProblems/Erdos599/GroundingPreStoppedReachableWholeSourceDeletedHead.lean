/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedReachableBoundaryReduction
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt

/-!
# The first exact defect on an ambient source prefix

The source-reachable boundary reduction retains a finite ambient path from an
original source to every whole-source root obstruction.  Since the endpoint
is not reachable in the pre-stopped switched relation, that path has a last
deleted head.  Its incoming edge is either outside the limiting-ladder family,
or it belongs to one of the three genuine pre-stopped deletion classes:
represented cut, selected backward, or forward conflict.

This is deliberately an ambient certificate.  The outside-family alternative
is retained rather than incorrectly applying the ladder-edge classifier to an
arbitrary graph path.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822ReachableWholeSourceRootObstruction

/-- A concrete ambient source prefix together with its last missing switched
edge and the exact strongest classification available for that edge. -/
structure AmbientLastDeletedHeadData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R) where
  path : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  path_start_source : path.start ∈ Gamma.source
  path_finish_boundary : path.finish = O.obstruction.boundary
  deleted : LastDeletedHead path
    (L.assertion822ReservedPreStoppedEdges hL S R)
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a deleted.head
  tail : V
  incoming_mem : (tail, deleted.head) ∈ path.edgeSet
  incoming_not_relation : (tail, deleted.head) ∉
    L.assertion822ReservedPreStoppedEdges hL S R
  incoming_class :
    (tail, deleted.head) ∉
        (L.popularAuxiliaryInput hL.legal).familyEdges ∨
      (tail, deleted.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut ∨
      (tail, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward ∨
      (tail, deleted.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅

/-- Extract the last switched-relation defect of the concrete ambient source
prefix carried by a reachable whole-source obstruction. -/
theorem exists_ambientLastDeletedHeadData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R) :
    Nonempty O.AmbientLastDeletedHeadData := by
  obtain ⟨p, hpStart, hpFinish⟩ := O.ambient
  have hstart : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a p.start :=
    ⟨p.start, hpStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a p.finish := by
    simpa only [hpFinish] using O.not_rooted
  obtain ⟨D, hDnot⟩ := exists_unrootedLastDeletedHead p hstart hfinish
  obtain ⟨u, huPath, huNot⟩ := D.deleted_incoming
  have hclass :
      (u, D.head) ∉
          (L.popularAuxiliaryInput hL.legal).familyEdges ∨
        (u, D.head) ∈ GroundingCut.CE
          (L.popularAuxiliaryInput hL.legal) S.cut ∨
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅ .backward ∨
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅ := by
    by_cases huFamily : (u, D.head) ∈
        (L.popularAuxiliaryInput hL.legal).familyEdges
    · have hdeleted := familyEdge_deleted_classificationAt
        (L.reservedGroundedControls hL S R) (∅ : Set V)
        huFamily huNot
      rcases hdeleted with hcut | hback | hconflict | hboundary
      · exact Or.inr (Or.inl hcut)
      · exact Or.inr (Or.inr (Or.inl hback))
      · exact Or.inr (Or.inr (Or.inr hconflict))
      · rw [boundaryOutgoingCutEdgesAt_empty] at hboundary
        exact False.elim hboundary
    · exact Or.inl huFamily
  exact ⟨{
    path := p
    path_start_source := hpStart
    path_finish_boundary := hpFinish
    deleted := D
    deleted_head_not_rooted := hDnot
    tail := u
    incoming_mem := huPath
    incoming_not_relation := huNot
    incoming_class := hclass }⟩

end Assertion822ReachableWholeSourceRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822ReachableWholeSourceRootObstruction.exists_ambientLastDeletedHeadData
