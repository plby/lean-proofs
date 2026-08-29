/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingAnchorOwners
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# Well-founded order for fresh-avoiding backward anchors

Repeated deleted heads owned by selected backward links move either to a
strictly earlier request or strictly left on the same limiting-ladder path.
This file packages that lexicographic descent without importing the legacy
reserved-record recursion cone.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshDescentIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshDescentControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshDescentRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshDescentEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

/-- Canonical natural-number position of a supported vertex on a directed
finite path or ray. -/
noncomputable def splitGroundedFreshAvoidingPathPosition
    (P : Gamma.DPath) (x : V) : ℕ :=
  by
    classical
    exact if hx : x ∈ P.support then
      Nat.find ((GroundingCut.mem_support_iff_exists_occursAt P x).1 hx)
    else 0

theorem occursAt_splitGroundedFreshAvoidingPathPosition
    (P : Gamma.DPath) {x : V} (hx : x ∈ P.support) :
    GroundingCut.OccursAt P
      (splitGroundedFreshAvoidingPathPosition P x) x := by
  classical
  rw [splitGroundedFreshAvoidingPathPosition, dif_pos hx]
  exact Nat.find_spec
    ((GroundingCut.mem_support_iff_exists_occursAt P x).1 hx)

theorem splitGroundedFreshAvoidingPathPosition_lt_of_before
    (P : Gamma.DPath) {x y : V} (hxy : GroundingCut.Before P x y) :
    splitGroundedFreshAvoidingPathPosition P x <
      splitGroundedFreshAvoidingPathPosition P y := by
  rcases hxy.1 with ⟨m, n, hmx, hny, hmn⟩
  have hx : x ∈ P.support := GroundingCut.occursAt_mem_support hmx
  have hy : y ∈ P.support := GroundingCut.occursAt_mem_support hny
  have hxm : splitGroundedFreshAvoidingPathPosition P x = m :=
    GroundingCutDecoder.occursAt_index_injective
      (occursAt_splitGroundedFreshAvoidingPathPosition P hx) hmx
  have hyn : splitGroundedFreshAvoidingPathPosition P y = n :=
    GroundingCutDecoder.occursAt_index_injective
      (occursAt_splitGroundedFreshAvoidingPathPosition P hy) hny
  rw [hxm, hyn]
  apply lt_of_le_of_ne hmn
  intro hnm
  apply hxy.2
  have hsame : GroundingCut.OccursAt P m y := by
    simpa only [hnm] using hny
  cases P with
  | inl p => exact hmx.2.symm.trans hsame.2
  | inr r => exact hmx.symm.trans hsame

theorem splitGroundedFreshAvoiding_walk_beforeEq_of_edgeSet_subset
    (P : Gamma.DPath) {a b : V} (q : Walk Gamma.graph a b)
    (ha : a ∈ P.support) (hq : q.edgeSet ⊆ P.edgeSet) :
    GroundingCut.BeforeEq P a b := by
  induction q with
  | nil => exact GroundingCut.beforeEq_refl ha
  | @cons a c b hac q ih =>
      have hacP : (a, c) ∈ P.edgeSet := by
        apply hq
        simp
      have hcP : c ∈ P.support :=
        (P.edgeSet_subset_support_prod hacP).2
      have hqP : q.edgeSet ⊆ P.edgeSet := by
        intro e he
        apply hq
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff]
        exact Or.inr he
      exact GroundingFragmentResidualOrder.beforeEq_trans
        (GroundingCut.beforeEq_of_mem_edgeSet hacP) (ih hcP hqP)

theorem splitGroundedFreshAvoiding_finiteSubpath_mem_beforeEq_finish
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf P) {x : V} (hx : x ∈ q.support) :
    GroundingCut.BeforeEq P x q.finish := by
  let m : q.walk.Meets ({x} : Set V) :=
    ⟨x, hx, Set.mem_singleton x⟩
  let r := q.lastHit ({x} : Set V) m
  have hrStart : r.start = x := by
    exact Set.mem_singleton_iff.mp
      (q.lastHit_start_mem ({x} : Set V) m)
  have hrFinish : r.finish = q.finish := rfl
  have hrEdges : r.edgeSet ⊆ P.edgeSet :=
    (q.lastHit_edgeSet_subset ({x} : Set V) m).trans hsub.2
  have hrStartP : r.start ∈ P.support := by
    simpa only [hrStart] using hsub.1 hx
  simpa only [hrStart, hrFinish] using
    splitGroundedFreshAvoiding_walk_beforeEq_of_edgeSet_subset
      P r.walk hrStartP hrEdges

theorem splitGroundedFreshAvoiding_finiteSubpath_start_beforeEq_of_mem
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf P) {x : V} (hx : x ∈ q.support) :
    GroundingCut.BeforeEq P q.start x := by
  let m : q.walk.Meets ({x} : Set V) :=
    ⟨x, hx, Set.mem_singleton x⟩
  let r := q.firstHit ({x} : Set V) m
  have hrStart : r.start = q.start := rfl
  have hrFinish : r.finish = x := by
    exact Set.mem_singleton_iff.mp
      (q.firstHit_finish_mem ({x} : Set V) m)
  have hrEdges : r.edgeSet ⊆ P.edgeSet :=
    (q.firstHit_edgeSet_subset ({x} : Set V) m).trans hsub.2
  have hstart : q.start ∈ P.support := hsub.1 q.start_mem_support
  simpa only [hrStart, hrFinish] using
    splitGroundedFreshAvoiding_walk_beforeEq_of_edgeSet_subset
      P r.walk hstart hrEdges

theorem splitGroundedFreshAvoiding_before_of_beforeEq_before
    (P : Gamma.DPath) {x y z : V}
    (hxy : GroundingCut.BeforeEq P x y)
    (hyz : GroundingCut.Before P y z) :
    GroundingCut.Before P x z := by
  refine ⟨GroundingFragmentResidualOrder.beforeEq_trans hxy hyz.1, ?_⟩
  intro hxz
  apply hyz.2
  apply GroundingCutDecoder.beforeEq_antisymm hyz.1
  simpa only [hxz] using hxy

theorem splitGroundedFreshAvoiding_backwardLink_start_before_head
    (Y : Gamma.DPath) (l : Link Gamma.graph)
    (hsub : l.path.IsSubpathOf Y) {u z : V}
    (huz : (u, z) ∈ l.path.edgeSet) :
    GroundingCut.Before Y l.path.start z := by
  refine ⟨splitGroundedFreshAvoiding_finiteSubpath_start_beforeEq_of_mem
    Y l.path hsub ((l.path.edgeSet_subset_support_prod huz).2), ?_⟩
  exact Ne.symm (FinitePath.target_ne_start_of_mem_edgeSet l.path huz)

/-- A concrete deleted-head problem on a parent exposed by one active
fresh-avoiding request. -/
structure SplitGroundedFreshAvoidingRootState where
  control : ActiveControlRequestAt
    (FreshDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (FreshDescentControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) ∅
  parent : Gamma.DPath
  parent_exposed : parent ∈ exposedLadderPaths
    (L.splitGroundedPopularAuxiliaryInput hL.legal)
    (strongSelectedPath
      (FreshDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshDescentControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) (chosenRequest control.1))
  rootPath : FinitePath Gamma.graph
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (FreshDescentEdges (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {
      (FreshDescentRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a deleted.head
  owner : L.SplitGroundedFreshAvoidingDeletedOwnerOutcome
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
    control parent deleted

theorem SplitGroundedFreshAvoidingRootState.deleted_head_mem
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    state.deleted.head ∈ state.parent.support := by
  obtain ⟨u, hu, _⟩ := state.deleted.deleted_incoming
  exact state.rootPath_support
    (state.rootPath.edgeSet_subset_support_prod hu).2

def SplitGroundedFreshAvoidingRootState.recursionKey
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    Stationary.Below kappa × ℕ :=
  (controlRank
      (FreshDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      state.control.1,
    splitGroundedFreshAvoidingPathPosition state.parent state.deleted.head)

def SplitGroundedFreshAvoidingRootState.Precedes :
    L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S) →
      L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S) →
      Prop :=
  (Prod.Lex (fun a b : Stationary.Below kappa ↦ a < b)
    (fun m n : ℕ ↦ m < n)).onFun
      SplitGroundedFreshAvoidingRootState.recursionKey

theorem SplitGroundedFreshAvoidingRootState.precedes_wellFounded :
    WellFounded (@SplitGroundedFreshAvoidingRootState.Precedes
      V Gamma kappa L hL hground hnotFresh S) := by
  exact InvImage.wf SplitGroundedFreshAvoidingRootState.recursionKey
    (wellFounded_lt.prod_lex wellFounded_lt)

/-- The last deleted head on the canonical source prefix to a backward-link
start is strictly before every head on that backward link. -/
theorem SplitGroundedFreshAvoidingBackwardDeletedData.deletedHead_before_oldHead
    {c : ActiveControlRequestAt
      (FreshDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshDescentControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅}
    {l : Link Gamma.graph} {parent : Gamma.DPath}
    (data : L.SplitGroundedFreshAvoidingBackwardDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (chosenRequest c.1) l parent)
    {u z : V} (hsub : l.path.IsSubpathOf parent)
    (huz : (u, z) ∈ l.path.edgeSet) :
    GroundingCut.Before parent data.deleted.head z := by
  obtain ⟨v, hv, _⟩ := data.deleted.deleted_incoming
  have hheadPrefix : data.deleted.head ∈ data.rootPath.support :=
    (data.rootPath.edgeSet_subset_support_prod hv).2
  have hheadStart : GroundingCut.BeforeEq parent
      data.deleted.head l.path.start := by
    simpa only [data.rootPath_finish] using
      splitGroundedFreshAvoiding_finiteSubpath_mem_beforeEq_finish
        parent data.rootPath
        ⟨data.rootPath_support, data.rootPath_edges⟩ hheadPrefix
  exact splitGroundedFreshAvoiding_before_of_beforeEq_before
    parent hheadStart
      (splitGroundedFreshAvoiding_backwardLink_start_before_head
        parent l hsub huz)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingRootState.precedes_wellFounded
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingBackwardDeletedData.deletedHead_before_oldHead
