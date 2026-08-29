/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualCollisionBoundaryOwners

/-!
# Audit of the maximal collision-hull cut

The collision hull is useful as a forbidden carrier in the maximal-family
selection, but it cannot also serve as the final component-transversal cut.
Every selected path which starts at an old source contributes that source to
the hull, while its old target endpoint belongs to the literal target.  Thus
both endpoints already lie in `CV`, and hence in `BB`, for the hull-enlarged
cut.  Any component construction joining the decoded route from source to
target must therefore meet this `BB` more than once unless the endpoints
coincide.

The theorem below records the set-theoretic part of that obstruction without
assuming any particular repaired relation.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- An old-start selected route contributes both its original start and its
old target endpoint to `BB` for the target-plus-collision-hull cut. -/
theorem selected_oldStart_and_targetFinish_mem_BB_targetCollisionCut
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph))
    (q : FinitePath J.lambda.graph) (hqP : q ∈ P)
    (hfinish : q.finish ∈ J.lambda.target)
    {b : V} (hstart : q.start = .old b) :
    b ∈ GroundingCut.BB J (reservedMaximalTargetCollisionCut J P) ∧
      ∃ y : V,
        q.finish = .old y ∧
        y ∈ GroundingCut.BB J (reservedMaximalTargetCollisionCut J P) := by
  have hbCut : (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ∈
      reservedMaximalTargetCollisionCut J P := by
    right
    rw [mem_collisionHull]
    refine ⟨q, hqP, ?_⟩
    exact Or.inl (Or.inl (hstart ▸ q.start_mem_support))
  have hbBB : b ∈
      GroundingCut.BB J (reservedMaximalTargetCollisionCut J P) :=
    GroundingCut.CV_subset_BB J _ hbCut
  obtain ⟨y, _hyMarker, hqy⟩ := J.finish_of_mem_lambda_target q hfinish
  refine ⟨hbBB, y, hqy, ?_⟩
  apply GroundingCut.CV_subset_BB J _
  exact Or.inl (hqy ▸ hfinish)

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.selected_oldStart_and_targetFinish_mem_BB_targetCollisionCut
