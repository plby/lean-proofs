/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawStoppedRequestRoot

/-!
# Local routes to relevant blockers survive stopping

After a blocker all local edges advance on the same reference fragment,
so no departing route can return. A route from another blocker identifies
their maximal fragments and hence their blocking points. This excludes
every boundary departure on a route to a relevant blocker.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (S : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))

local notation "Lc" => canonicalDeferredLadder Gamma kappa preferred
local notation "J" => popularAuxiliaryInput Lc hL.legal
local notation "D" => reservedStrongSelectedPruningData (L := Lc) (hL := hL) (S := S)
local notation "BB" => reservedStrongSelectedRelevantBB (L := Lc) (hL := hL) (S := S)

include hkappa huncountable hNoEnter in
/-- A local route after a blocker preserves the order from its actual start. -/
theorem canonicalDeferredLadder_rawLocalSource_monotone_after_blocker
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {x y : V} (hx : x ∈ P.path.support)
    (hbx : GroundingCut.BeforeEq P.path (GroundingCut.blockingPoint J S.cut P) x)
    (hreach : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ reservedRawLocalSourceEdges r) x y) :
    GroundingCut.BeforeEq P.path x y := by
  induction hreach with
  | refl => exact GroundingCut.beforeEq_refl hx
  | @tail y z hxy he ih =>
      have hy := (canonicalDeferredLadder_rawLocalSource_reach_after_blocker
        preferred hkappa huncountable hNoEnter hL S r P hP hx hbx hxy).1
      have hby := GroundingFragmentResidualOrder.beforeEq_trans hbx ih
      have hret := (canonicalDeferredLadder_rawLocalSource_step_after_blocker
        preferred hkappa huncountable hNoEnter hL S r P hP hy hby he).1
      have href := reservedRawActiveReference_subset_reference r hret.1
      have hnotCut : (y, z) ∉ GroundingCut.CE J S.cut := by
        obtain ⟨R, heR⟩ := hret.1
        exact fun hc ↦ Set.disjoint_left.1 R.cut_free heR hc
      exact GroundingFragmentResidualOrder.beforeEq_trans ih
        (GroundingFragmentResidualOrder.beforeEq_of_mem_surviving_edge
          hP.1.1.1 hy href hnotCut)

include hkappa huncountable hNoEnter in
/-- No local route which leaves a relevant blocker can return to it. -/
theorem canonicalDeferredLadder_rawLocalSource_blocker_no_return
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {y : V} (he : (GroundingCut.blockingPoint J S.cut P, y) ∈ reservedRawLocalSourceEdges r)
    (hrest : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ reservedRawLocalSourceEdges r) y
      (GroundingCut.blockingPoint J S.cut P)) : False := by
  have hb := GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
  obtain ⟨hret, hy, hby⟩ := canonicalDeferredLadder_rawLocalSource_step_after_blocker
    preferred hkappa huncountable hNoEnter hL S r P hP hb
    (GroundingCut.beforeEq_refl hb) he
  have hyb := canonicalDeferredLadder_rawLocalSource_monotone_after_blocker
    preferred hkappa huncountable hNoEnter hL S r P hP hy hby hrest
  obtain ⟨R, heR⟩ := hret.1
  exact GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet (R.edges heR)
    (GroundingCutDecoder.beforeEq_antisymm hby hyb)

include hkappa huncountable hNoEnter in
/-- A local route to any relevant blocker cannot depart from the boundary. -/
theorem canonicalDeferredLadder_rawLocalSource_no_boundary_departure_to_blocker
    (r : Request J S.cut) (Q : (J).Fragment) (hQ : Q ∈ (D).relevantG0)
    {x y : V} (hxBB : x ∈ BB) (he : (x, y) ∈ reservedRawLocalSourceEdges r)
    (hrest : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ reservedRawLocalSourceEdges r) y
      (GroundingCut.blockingPoint J S.cut Q)) : False := by
  rcases hxBB with hxCV | ⟨P, hP, rfl⟩
  · exact canonicalDeferredLadder_rawLocalSourceTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S r he hxCV
  · have hb := GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
    obtain ⟨_hret, hy, hby⟩ := canonicalDeferredLadder_rawLocalSource_step_after_blocker
      preferred hkappa huncountable hNoEnter hL S r P hP hb
      (GroundingCut.beforeEq_refl hb) he
    have hbQP := (canonicalDeferredLadder_rawLocalSource_reach_after_blocker
      preferred hkappa huncountable hNoEnter hL S r P hP hy hby hrest).1
    have heq := GroundingFragmentUniqueness.blockingPoint_eq_of_common
      hP.1.1.1 hQ.1.1.1 hbQP (GroundingCut.blockingPoint_mem_support J S.cut Q hQ.1.2)
    apply canonicalDeferredLadder_rawLocalSource_blocker_no_return
      preferred hkappa huncountable hNoEnter hL S r P hP he
    simpa only [heq] using hrest

include hkappa huncountable hNoEnter in
/-- Every local route to a relevant blocker survives actual separator stopping. -/
theorem canonicalDeferredLadder_rawLocalBlockerRoute_survives_stopping
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {T : Set V} (hT : T ⊆ BB) {a : V}
    (hreach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ reservedRawLocalSourceEdges r) a
      (GroundingCut.blockingPoint J S.cut P)) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ reservedRawStoppedEdges (L := Lc) (hL := hL) (S := S) T)
      a (GroundingCut.blockingPoint J S.cut P) := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b he hrest ih =>
      exact ih.head ⟨reservedRawLocalSource_subset_simultaneous r he,
        fun haT ↦ canonicalDeferredLadder_rawLocalSource_no_boundary_departure_to_blocker
          preferred hkappa huncountable hNoEnter hL S r P hP (hT haT) he hrest⟩

#print axioms canonicalDeferredLadder_rawLocalSource_blocker_no_return
#print axioms canonicalDeferredLadder_rawLocalSource_no_boundary_departure_to_blocker
#print axioms canonicalDeferredLadder_rawLocalBlockerRoute_survives_stopping

end Erdos599.DWeb.KappaLadder.Deferred
