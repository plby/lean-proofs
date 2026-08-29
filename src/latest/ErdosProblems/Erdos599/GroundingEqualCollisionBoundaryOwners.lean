/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualCollisionOwners

/-!
# Owners of the target-plus-maximal-collision boundary

The reserved route is deliberately absent from this cut.  Its sole role is
to identify an unused grounded source and constrain the maximal family.  The
auxiliary target separates source from target, while the selected collision
hull records every route/component touched by the maximal active family.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection GroundingSimultaneousDecode
open PopularAuxiliary.Input

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The corrected maximal equal-stage cut. -/
def reservedMaximalTargetCollisionCut
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) : Set J.LV :=
  J.lambda.target ∪ collisionHull J P

/-- The corrected cut is unconditionally an auxiliary separator because it
contains the complete auxiliary target. -/
theorem reservedMaximalTargetCollisionCut_isSeparator
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) :
    Popular.IsSeparator J.lambda (reservedMaximalTargetCollisionCut J P) := by
  intro p _hpSource hpTarget
  exact ⟨p.finish, p.finish_mem_support, Or.inl hpTarget⟩

theorem old_mem_collisionHull_iff
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) (b : V) :
    (LambdaVertex.old b : J.LV) ∈ collisionHull J P ↔
      ∃ r ∈ P, OldCollisionProvenance J r b := by
  rw [mem_collisionHull]
  constructor
  · rintro ⟨r, hrP, hbr⟩
    exact ⟨r, hrP, (old_mem_collisionCarrier_iff J r b).1 hbr⟩
  · rintro ⟨r, hrP, hbr⟩
    exact ⟨r, hrP, (old_mem_collisionCarrier_iff J r b).2 hbr⟩

theorem edge_mem_collisionHull_iff
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) (u v : V) :
    (LambdaVertex.edge u v : J.LV) ∈ collisionHull J P ↔
      ∃ r ∈ P, EdgeCollisionProvenance J r u v := by
  rw [mem_collisionHull]
  constructor
  · rintro ⟨r, hrP, her⟩
    exact ⟨r, hrP, (edge_mem_collisionCarrier_iff J r u v).1 her⟩
  · rintro ⟨r, hrP, her⟩
    exact ⟨r, hrP, (edge_mem_collisionCarrier_iff J r u v).2 her⟩

/-- Old points of the corrected cut are either target markers or are owned
by one selected maximal route/component. -/
theorem old_mem_reservedMaximalTargetCollisionCut_iff
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) (b : V) :
    (LambdaVertex.old b : J.LV) ∈ reservedMaximalTargetCollisionCut J P ↔
      b ∈ J.targetMarkers ∨
        ∃ r ∈ P, OldCollisionProvenance J r b := by
  rw [reservedMaximalTargetCollisionCut, Set.mem_union,
    J.mem_lambda_target_old, old_mem_collisionHull_iff]

/-- Auxiliary targets contain only old gadgets, so every edge gadget in the
corrected cut is owned by a selected maximal route/component. -/
theorem edge_mem_reservedMaximalTargetCollisionCut_iff
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) (u v : V) :
    (LambdaVertex.edge u v : J.LV) ∈ reservedMaximalTargetCollisionCut J P ↔
      ∃ r ∈ P, EdgeCollisionProvenance J r u v := by
  rw [reservedMaximalTargetCollisionCut, Set.mem_union,
    edge_mem_collisionHull_iff]
  simp only [J.not_mem_lambda_target_edge, false_or]

/-- `CV` has the same target-marker/selected-owner dichotomy. -/
theorem mem_CV_reservedMaximalTargetCollisionCut_iff
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) (b : V) :
    b ∈ GroundingCut.CV J (reservedMaximalTargetCollisionCut J P) ↔
      b ∈ J.targetMarkers ∨
        ∃ r ∈ P, OldCollisionProvenance J r b := by
  exact old_mem_reservedMaximalTargetCollisionCut_iff J P b

/-- Complete classification for the corrected original-web boundary. -/
theorem mem_BB_target_or_selected_or_blockingPoint
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) {b : V}
    (hb : b ∈ GroundingCut.BB J (reservedMaximalTargetCollisionCut J P)) :
    (b ∈ J.targetMarkers ∨
      ∃ r ∈ P, OldCollisionProvenance J r b) ∨
      ∃ F : J.Fragment,
        F ∈ GroundingCut.G0 J (reservedMaximalTargetCollisionCut J P) ∧
        GroundingCut.IsBlockable J (reservedMaximalTargetCollisionCut J P) F ∧
        GroundingCut.blockingPoint J
          (reservedMaximalTargetCollisionCut J P) F = b ∧
        b ∈ F.path.support := by
  rcases hb with hbCV | hbBlocking
  · exact Or.inl
      ((mem_CV_reservedMaximalTargetCollisionCut_iff J P b).1 hbCV)
  · obtain ⟨F, hFG0, hFblock, hbEq, hbF⟩ :=
      GroundingCut.BL_covered_by_G0 hbBlocking
    exact Or.inr ⟨F, hFG0, hFblock, hbEq.symm, hbF⟩

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.old_mem_reservedMaximalTargetCollisionCut_iff
#print axioms Erdos599.DWeb.KappaLadder.edge_mem_reservedMaximalTargetCollisionCut_iff
#print axioms Erdos599.DWeb.KappaLadder.mem_BB_target_or_selected_or_blockingPoint
