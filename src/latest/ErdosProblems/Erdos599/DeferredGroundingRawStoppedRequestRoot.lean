/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawTerminalContactOrder

/-!
# Actual request routes survive separator stopping

After any relevant blocker, the local request relation stays on that
fragment and advances in its order. Its first edge there has a changed
owner, whereas the request endpoint is outside every such owner. Hence
a route to the request cannot leave the relevant boundary. This converts
the actual unstopped local roots into roots in the stopped global relation.
Coverage of other separator vertices is not asserted here.
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
/-- The active source-prefix reference has no departure from the old cut. -/
theorem canonicalDeferredLadder_rawActiveTail_not_mem_CV
    (r : Request J S.cut) {x y : V}
    (he : (x, y) ∈ reservedRawActiveReferenceEdges r) :
    x ∉ GroundingCut.CV J S.cut := by
  obtain ⟨R, heR⟩ := he
  have hground := canonicalDeferredLadder_rawBackwardOwner_grounded
    preferred hkappa huncountable hNoEnter hL S r R.owner_mem R.changed_mem R.changed_owner
  have hnotFinite : x ∉ (J).finiteSource := by
    intro hx
    exact (popularAuxiliary_hasBoundaryIncidence Lc hL.legal).finite_source_sink hx
      ⟨y, R.owner, R.owner_mem, R.edges heR⟩
  intro hxC
  exact canonicalDeferredLadder_oldRequest_not_mem_grounded_owner
    preferred hkappa huncountable hNoEnter hL S ⟨x, hxC, hnotFinite⟩ R.owner_mem hground
    (R.owner.edgeSet_subset_support_prod (R.edges heR)).1

include hkappa huncountable hNoEnter in
/-- No edge of the actual local request relation leaves CV. -/
theorem canonicalDeferredLadder_rawLocalSourceTail_not_mem_CV
    (r : Request J S.cut) {x y : V}
    (he : (x, y) ∈ reservedRawLocalSourceEdges r) :
    x ∉ GroundingCut.CV J S.cut := by
  rcases he with (hret | hforward) | hprefix
  · exact canonicalDeferredLadder_rawActiveTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S r hret.1
  · exact canonicalDeferredLadder_rawInsertedTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S (Or.inl (Set.mem_iUnion.mpr ⟨r, hforward⟩))
  · exact canonicalDeferredLadder_rawInsertedTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S (Or.inr (Set.mem_iUnion.mpr ⟨r, hprefix⟩))

include hkappa huncountable hNoEnter in
/-- At or after a relevant blocker, a local edge is retained reference
and stays in the same fragment, advancing its intrinsic order. -/
theorem canonicalDeferredLadder_rawLocalSource_step_after_blocker
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {x y : V} (hx : x ∈ P.path.support)
    (horder : GroundingCut.BeforeEq P.path (GroundingCut.blockingPoint J S.cut P) x)
    (he : (x, y) ∈ reservedRawLocalSourceEdges r) :
    (x, y) ∈ reservedRawActiveReferenceEdges r \ reservedRawRequestBackwardEdges r ∧
      y ∈ P.path.support ∧
      GroundingCut.BeforeEq P.path (GroundingCut.blockingPoint J S.cut P) y := by
  have hret : (x, y) ∈
      reservedRawActiveReferenceEdges r \ reservedRawRequestBackwardEdges r := by
    rcases he with (hret | hforward) | hprefix
    · exact hret
    · have hstrict := canonicalDeferredLadder_rawGlobalForwardTail_before_blocker
        preferred hkappa huncountable hNoEnter hL S P hP
        (Set.mem_iUnion.mpr ⟨r, hforward⟩) hx
      exact (hstrict.2 (GroundingCutDecoder.beforeEq_antisymm hstrict.1 horder)).elim
    · exact (Set.disjoint_left.1 (reservedRawRelevantFragment_disjoint_startingRecord r P hP)
        hx ((reservedRawOwnerAttachment r).sourcePrefix_support
          ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hprefix).1)).elim
  have href := reservedRawActiveReference_subset_reference r hret.1
  have hnotCut : (x, y) ∉ GroundingCut.CE J S.cut := by
    obtain ⟨R, heR⟩ := hret.1
    exact fun hc ↦ Set.disjoint_left.1 R.cut_free heR hc
  exact ⟨hret,
    GroundingFragmentResidualOrder.head_mem_fragment_of_mem_surviving_edge
      hP.1.1.1 hx href hnotCut,
    GroundingFragmentResidualOrder.beforeEq_trans horder
      (GroundingFragmentResidualOrder.beforeEq_of_mem_surviving_edge
        hP.1.1.1 hx href hnotCut)⟩

include hkappa huncountable hNoEnter in
/-- A finite local route starting after a blocker cannot leave its fragment. -/
theorem canonicalDeferredLadder_rawLocalSource_reach_after_blocker
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {x y : V} (hx : x ∈ P.path.support)
    (horder : GroundingCut.BeforeEq P.path (GroundingCut.blockingPoint J S.cut P) x)
    (hreach : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ reservedRawLocalSourceEdges r) x y) :
    y ∈ P.path.support ∧
      GroundingCut.BeforeEq P.path (GroundingCut.blockingPoint J S.cut P) y := by
  induction hreach with
  | refl => exact ⟨hx, horder⟩
  | @tail y z _hreach he ih =>
      exact (canonicalDeferredLadder_rawLocalSource_step_after_blocker
        preferred hkappa huncountable hNoEnter hL S r P hP ih.1 ih.2 he).2

include hkappa huncountable hNoEnter in
/-- A local route to the request endpoint cannot first depart from BB. -/
theorem canonicalDeferredLadder_rawLocalSource_no_boundary_departure_to_request
    (r : Request J S.cut) {x y : V} (hxBB : x ∈ BB)
    (he : (x, y) ∈ reservedRawLocalSourceEdges r)
    (hrest : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ reservedRawLocalSourceEdges r) y (requestVertex r)) : False := by
  rcases hxBB with hxCV | ⟨P, hP, rfl⟩
  · exact canonicalDeferredLadder_rawLocalSourceTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S r he hxCV
  · have hb := GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
    obtain ⟨hret, hy, hby⟩ := canonicalDeferredLadder_rawLocalSource_step_after_blocker
      preferred hkappa huncountable hNoEnter hL S r P hP hb
      (GroundingCut.beforeEq_refl hb) he
    have hrequestP := (canonicalDeferredLadder_rawLocalSource_reach_after_blocker
      preferred hkappa huncountable hNoEnter hL S r P hP hy hby hrest).1
    obtain ⟨R, heR⟩ := hret.1
    have hsame : P.parent = R.owner := DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint
      P.parent_mem R.owner_mem (P.support_subset hb)
      (R.owner.edgeSet_subset_support_prod (R.edges heR)).1
    exact reservedRawBackwardOwner_requestVertex_not_mem r R.owner_mem
      R.changed_mem R.changed_owner (hsame ▸ P.support_subset hrequestP)

include hkappa huncountable hNoEnter in
/-- Every actual local route to its request survives stopping at any
subset of the actual relevant boundary. -/
theorem canonicalDeferredLadder_rawLocalRequestRoute_survives_stopping
    (r : Request J S.cut) {T : Set V} (hT : T ⊆ BB) {a : V}
    (hreach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ reservedRawLocalSourceEdges r) a (requestVertex r)) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ reservedRawStoppedEdges (L := Lc) (hL := hL) (S := S) T)
      a (requestVertex r) := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b he hrest ih =>
      exact ih.head ⟨reservedRawLocalSource_subset_simultaneous r he,
        fun haT ↦ canonicalDeferredLadder_rawLocalSource_no_boundary_departure_to_request
          preferred hkappa huncountable hNoEnter hL S r (hT haT) he hrest⟩

include hkappa huncountable hNoEnter in
/-- The actual canonical requests are rooted in the source-first stopped
simultaneous relation, with all local coverage premises discharged. -/
theorem canonicalDeferredLadder_rawRequest_sourceRooted
    (r : Request J S.cut) :
    reservedRawSourceRooted (L := Lc) (hL := hL) (S := S) (requestVertex r) := by
  obtain ⟨a, ha, hreach⟩ := reservedRawLocalSource_request_rooted r
    (canonicalDeferredLadder_rawBackward_subset_activeReference
      preferred hkappa huncountable hNoEnter hL S r)
  exact ⟨a, ha, canonicalDeferredLadder_rawLocalRequestRoute_survives_stopping
    preferred hkappa huncountable hNoEnter hL S r
    reservedStrongSelectedSourceFirstBB_subset_relevantBB hreach⟩

#print axioms canonicalDeferredLadder_rawLocalSource_step_after_blocker
#print axioms canonicalDeferredLadder_rawLocalSource_no_boundary_departure_to_request
#print axioms canonicalDeferredLadder_rawLocalRequestRoute_survives_stopping
#print axioms canonicalDeferredLadder_rawRequest_sourceRooted

end Erdos599.DWeb.KappaLadder.Deferred
