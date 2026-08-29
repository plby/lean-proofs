/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutEndpointOrder
import ErdosProblems.Erdos599.GroundingTargetPureChronology

/-!
# Contact order for target-pure equal-stage routes

The collision hull used to choose a maximal disjoint auxiliary family is an
absorption device, not a suitable stopping boundary: a selected route may
contribute several hull vertices to one decoded component.  For the actual
order argument we therefore use the literal auxiliary target as the cut.

A target-pure route has no target vertex before its endpoint.  Consequently,
the first prefix ending at any non-target gadget avoids the literal target,
and Assertion 8.21 applies to that prefix.  The results below are independent
of a popular separator and apply to every route in the maximal equal-stage
family.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingEqualTargetContactOrder

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev LV (J : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The literal auxiliary target is a finite-path separator. -/
theorem target_isSeparator (J : PopularAuxiliary.Input Gamma I) :
    Popular.IsSeparator J.lambda J.lambda.target := by
  intro p _ hpTarget
  exact ⟨p.finish, p.finish_mem_support, hpTarget⟩

/-- The first prefix ending at a non-target vertex of a target-pure route
avoids the complete auxiliary target. -/
theorem firstHit_nonTarget_avoids_target
    (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hpure : J.IsTargetPure p)
    (hfinishTarget : p.finish ∈ J.lambda.target)
    {z : J.LV} (hz : z ∈ p.support) (hznotTarget : z ∉ J.lambda.target) :
    let hmeet : p.walk.Meets ({z} : Set J.LV) :=
      ⟨z, hz, Set.mem_singleton z⟩
    J.lambda.Avoids (p.firstHit ({z} : Set J.LV) hmeet)
      J.lambda.target := by
  let hmeet : p.walk.Meets ({z} : Set J.LV) :=
    ⟨z, hz, Set.mem_singleton z⟩
  let q := p.firstHit ({z} : Set J.LV) hmeet
  have hfinishNot : p.finish ∉ ({z} : Set J.LV) := by
    intro h
    have heq : p.finish = z := Set.mem_singleton_iff.1 h
    exact hznotTarget (heq ▸ hfinishTarget)
  have hfinishNotQ : p.finish ∉ q.support :=
    Popular.firstHit_not_mem_of_finish_not_mem p ({z} : Set J.LV)
      hmeet hfinishNot
  change Disjoint q.support J.lambda.target
  rw [Set.disjoint_left]
  intro y hyq hyTarget
  have hyp : y ∈ p.support := p.firstHit_support_subset _ hmeet hyq
  have hyFinish : y = p.finish :=
    Set.mem_singleton_iff.1 (hpure ⟨hyp, hyTarget⟩)
  exact hfinishNotQ (hyFinish ▸ hyq)

/-- Assertion 8.21 at an old-vertex contact of an arbitrary target-pure
source--target auxiliary route, using the literal target as cut. -/
theorem oldContact_beforeEq_blockingPoint
    (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hstart : p.start ∈ J.lambda.source)
    (hfinish : p.finish ∈ J.lambda.target)
    (hpure : J.IsTargetPure p)
    (P : J.Fragment) (hP : P ∈ GroundingCut.G0 J J.lambda.target)
    (hblockable : GroundingCut.IsBlockable J J.lambda.target P)
    {x : V}
    (hx : (PopularAuxiliary.Input.LambdaVertex.old x : J.LV) ∈ p.support)
    (hxnotTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : J.LV) ∉ J.lambda.target)
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint J J.lambda.target P) := by
  let z : J.LV := .old x
  let hmeet : p.walk.Meets ({z} : Set J.LV) :=
    ⟨z, hx, Set.mem_singleton z⟩
  let q := p.firstHit ({z} : Set J.LV) hmeet
  apply GroundingCutDecoder.assertion8_21 J J.lambda.target
    (target_isSeparator J) P hP hblockable q
  · exact hstart
  · exact firstHit_nonTarget_avoids_target J p hpure hfinish hx hxnotTarget
  · exact Set.mem_singleton_iff.1 (p.firstHit_finish_mem _ hmeet)
  · exact hxP

/-- Assertion 8.21 at an edge-gadget contact of an arbitrary target-pure
source--target auxiliary route.  Since the literal target contains no edge
gadgets, the represented edge is automatically outside `CE`.  Its original
tail may nevertheless already be a target marker; that is the exact boundary
alternative in the conclusion. -/
theorem edgeContact_tail_beforeEq_or_oldTarget
    (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hstart : p.start ∈ J.lambda.source)
    (hfinish : p.finish ∈ J.lambda.target)
    (hpure : J.IsTargetPure p)
    (P : J.Fragment) (hP : P ∈ GroundingCut.G0 J J.lambda.target)
    (hblockable : GroundingCut.IsBlockable J J.lambda.target P)
    {x y : V}
    (hxyFamily : (x, y) ∈ J.familyEdges)
    (hedge : (PopularAuxiliary.Input.LambdaVertex.edge x y : J.LV) ∈
      p.support)
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x
        (GroundingCut.blockingPoint J J.lambda.target P) ∨
      (PopularAuxiliary.Input.LambdaVertex.old x : J.LV) ∈
        J.lambda.target := by
  let z : J.LV := .edge x y
  have hznotTarget : z ∉ J.lambda.target := J.not_mem_lambda_target_edge x y
  have hxyNotCE : (x, y) ∉ GroundingCut.CE J J.lambda.target := by
    intro h
    exact J.not_mem_lambda_target_edge x y (GroundingCut.mem_CE.1 h).1
  let hmeet : p.walk.Meets ({z} : Set J.LV) :=
    ⟨z, hedge, Set.mem_singleton z⟩
  let q := p.firstHit ({z} : Set J.LV) hmeet
  apply GroundingCutEndpointOrder.assertion8_21_edgeTail_or_old_mem_cut
    J J.lambda.target
    (target_isSeparator J) P hP hblockable q
  · exact hstart
  · exact firstHit_nonTarget_avoids_target J p hpure hfinish hedge hznotTarget
  · exact Set.mem_singleton_iff.1 (p.firstHit_finish_mem _ hmeet)
  · exact hxP
  · exact hxyFamily
  · exact hxyNotCE

end GroundingEqualTargetContactOrder
end Erdos599

#print axioms Erdos599.GroundingEqualTargetContactOrder.firstHit_nonTarget_avoids_target
#print axioms Erdos599.GroundingEqualTargetContactOrder.oldContact_beforeEq_blockingPoint
#print axioms Erdos599.GroundingEqualTargetContactOrder.edgeContact_tail_beforeEq_or_oldTarget
