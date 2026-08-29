/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingStoppedActiveForwardRootClassification
import ErdosProblems.Erdos599.SplitGroundingGroundedReducedDeletedOutcome
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# Native-frontier reduction of a selected forward conflict

The exact conflict certificate distinguishes a common tail from a common
head.  In the common-head case the unrooted deleted head is itself a retained
forward vertex of the selected owner.  Boundary-parametric root transfer then
reduces it to an unrooted selected initial or backward-link entry.  Thus only
the genuine common-tail exchange reaches the last-contact splice.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ForwardConflictIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- A finite walk whose edges lie on a directed path advances monotonically
in the intrinsic order of that path. -/
private theorem walk_beforeEq_of_edgeSet_subset
    (P : Gamma.DPath) {a b : V}
    (q : Walk Gamma.graph a b)
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

/-- A finite directed subpath advances monotonically on its ambient directed
path.  This local form is used to compare the two canonical suffixes of a
last-deleted finite segment. -/
private theorem finiteSubpath_start_beforeEq_of_mem
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
    walk_beforeEq_of_edgeSet_subset P r.walk hstart hrEdges

/-- Every vertex occurring after the last deleted head belongs to the
surviving suffix stored in `LastDeletedHead`. -/
theorem LastDeletedHead.mem_suffix_of_beforeEq
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (D : LastDeletedHead p E) {w : V}
    (hw : w ∈ p.support)
    (horder : GroundingCut.BeforeEq (.inl p : Gamma.DPath) D.head w) :
    w ∈ D.suffix.support := by
  let qw := p.suffixFrom w hw
  have hqw : qw.walk.support <:+ p.walk.support :=
    (p.walk.lastHit ({w} : Set V)
      ⟨w, hw, Set.mem_singleton w⟩).support_suffix
  let qh := p.suffixFrom D.head D.head_mem_parent
  have hqh : qh.walk.support <:+ p.walk.support :=
    (p.walk.lastHit ({D.head} : Set V)
      ⟨D.head, D.head_mem_parent, Set.mem_singleton D.head⟩).support_suffix
  rcases List.suffix_total hqw hqh with hqwqh | hqhqw
  · change w ∈ D.suffix.walk.support
    rw [D.suffix_support_eq_suffixFrom]
    apply hqwqh.subset
    have hwHead := List.head_mem qw.walk.support_ne_nil
    have hwStart : qw.start ∈ qw.walk.support := by
      simpa only [qw.walk.head_support] using hwHead
    simpa only [qw, FinitePath.suffixFrom_start] using hwStart
  · have hheadQw : D.head ∈ qw.support := by
      change D.head ∈ qw.walk.support
      apply hqhqw.subset
      have hheadHead := List.head_mem qh.walk.support_ne_nil
      have hheadStart : qh.start ∈ qh.walk.support := by
        simpa only [qh.walk.head_support] using hheadHead
      simpa only [qh, FinitePath.suffixFrom_start] using hheadStart
    have hreverse : GroundingCut.BeforeEq (.inl p : Gamma.DPath) w D.head := by
      have := finiteSubpath_start_beforeEq_of_mem
        (.inl p : Gamma.DPath) qw
        (p.suffixFrom_isSubpathOf w hw) hheadQw
      simpa only [qw, FinitePath.suffixFrom_start] using this
    have heq : D.head = w :=
      GroundingCutDecoder.beforeEq_antisymm horder hreverse
    subst w
    rw [← D.suffix_start]
    exact D.suffix.start_mem_support

/-- Once a vertex at or after the last deleted head has a source root, the
surviving parent suffix carries that root all the way to the segment finish.
This is the positive half of the last-contact splice: only contacts strictly
before the deleted head require an exchange. -/
theorem LastDeletedHead.finish_rooted_of_beforeEq_rooted
    {E : Set (V × V)} {A : Set V} {p : FinitePath Gamma.graph}
    (D : LastDeletedHead p E) {w : V}
    (hw : w ∈ p.support)
    (horder : GroundingCut.BeforeEq (.inl p : Gamma.DPath) D.head w)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a w) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
  have hwSuffix := D.mem_suffix_of_beforeEq hw horder
  let q := D.suffix.suffixFrom w hwSuffix
  have hqEdges : q.edgeSet ⊆ E :=
    (D.suffix.suffixFrom_edgeSet_subset w hwSuffix).trans
      D.suffix_edgeSet_subset
  have hqReach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) q.start q.finish := by
    exact Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ q.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
      (by
        intro x y hxy
        exact hqEdges hxy)
      q.start q.finish
      (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet q.walk)
  obtain ⟨a, ha, haw⟩ := hroot
  refine ⟨a, ha, haw.trans ?_⟩
  simpa only [q, FinitePath.suffixFrom_start,
    FinitePath.suffixFrom_finish, D.suffix_finish] using hqReach

/-- If the segment-local final contact lies at or after the last deleted
head, a root of that contact reaches the finite segment's terminal through
the surviving suffix. -/
theorem SplitGroundedReducedForwardConflictSpliceData.finish_rooted_of_head_beforeEq
    {T A : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D)
    (horder : GroundingCut.BeforeEq (.inl p : Gamma.DPath)
      D.head data.segmentLastContact.vertex)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T)
        a data.segmentLastContact.vertex) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T)
        a p.finish := by
  exact D.finish_rooted_of_beforeEq_rooted
    data.segmentLastContact.vertex_mem horder hroot

/-- Honest resolution of the rooted final-contact case.  Either the contact
is strictly before the last deleted head, which is precisely the old-tail
exchange still requiring normalization, or the surviving parent suffix
already roots the segment terminal.  No unchanged-`T` root is asserted for
the discarded tail. -/
theorem SplitGroundedReducedForwardConflictSpliceData.before_head_or_finish_rooted
    {T A : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D)
    (hnotHead : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T) a D.head)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T)
        a data.segmentLastContact.vertex) :
    GroundingCut.Before (.inl p : Gamma.DPath)
        data.segmentLastContact.vertex D.head ∨
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (ForwardConflictIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a p.finish := by
  rcases data.segmentLastContact_beforeEq_head_or_head_beforeEq with hbefore | hafter
  · left
    refine ⟨hbefore, ?_⟩
    intro heq
    apply hnotHead
    simpa only [heq] using hroot
  · exact Or.inr (data.finish_rooted_of_head_beforeEq hafter hroot)

/-- Constructor-ready form for an actual unrooted boundary segment.  Once
both the deleted head and the segment terminal are known to be unrooted, a
rooted final contact cannot lie at or after the head.  Hence it is a genuine
strict discarded-tail exchange, with no remaining positive subcase. -/
theorem SplitGroundedReducedForwardConflictSpliceData.before_head_of_unrooted_finish
    {T A : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D)
    (hnotHead : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T) a D.head)
    (hnotFinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T) a p.finish)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T)
        a data.segmentLastContact.vertex) :
    GroundingCut.Before (.inl p : Gamma.DPath)
      data.segmentLastContact.vertex D.head := by
  rcases data.before_head_or_finish_rooted hnotHead hroot with
    hbefore | hfinish
  · exact hbefore
  · exact False.elim (hnotFinish hfinish)

/-- Endpoint-rewritten form matching the source-first dispatcher, whose
unrooted certificate is stated at the named boundary point `t`. -/
theorem SplitGroundedReducedForwardConflictSpliceData.before_head_of_unrooted_endpoint
    {T A : Set V} {t : V} {parent : Gamma.DPath}
    {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D)
    (hfinish : p.finish = t)
    (hnotHead : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T) a D.head)
    (hnotEndpoint : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T) a t)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T)
        a data.segmentLastContact.vertex) :
    GroundingCut.Before (.inl p : Gamma.DPath)
      data.segmentLastContact.vertex D.head := by
  apply data.before_head_of_unrooted_finish hnotHead
  · simpa only [hfinish] using hnotEndpoint
  · exact hroot

/-- The edge entering the deleted head is adjacent on the finite segment.
Consequently, a segment-local last contact strictly before the head already
lies at or before that edge's tail.  This is the concrete splice position:
the selected suffix can leave the old segment no later than the divergent
incoming edge, without asserting that any discarded old tail survives. -/
theorem SplitGroundedReducedForwardConflictSpliceData.segmentLastContact_beforeEq_incomingTail
    {T : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D)
    (hbefore : GroundingCut.Before (.inl p : Gamma.DPath)
      data.segmentLastContact.vertex D.head) :
    GroundingCut.BeforeEq (.inl p : Gamma.DPath)
      data.segmentLastContact.vertex data.incomingTail := by
  rcases hbefore.1 with ⟨m, k, hm, hk, hmk⟩
  obtain ⟨n, hn, hntail, hnhead⟩ :=
    _root_.Erdos599.DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet
      p.walk data.incoming_mem
  have htailOccurs : GroundingCut.OccursAt
      (.inl p : Gamma.DPath) n data.incomingTail := by
    exact ⟨Nat.lt_of_succ_lt hn, hntail⟩
  have hheadOccurs : GroundingCut.OccursAt
      (.inl p : Gamma.DPath) (n + 1) D.head := by
    exact ⟨hn, hnhead⟩
  have hkEq : k = n + 1 :=
    GroundingCutDecoder.occursAt_index_injective hk hheadOccurs
  have hmNe : m ≠ n + 1 := by
    intro hmEq
    apply hbefore.2
    rcases hm with ⟨hmLen, hmVertex⟩
    rcases hheadOccurs with ⟨hheadLen, hheadVertex⟩
    subst m
    exact hmVertex.symm.trans hheadVertex
  refine ⟨m, n, hm, htailOccurs, ?_⟩
  omega

/-- Exact same-head elimination at the actual stopping frontier.  The left
alternative is precisely the remaining same-tail last-contact exchange; the
right alternative is already an earlier source/backward anchor of its active
selected owner. -/
theorem SplitGroundedReducedForwardConflictSpliceData.sameTail_or_unrootedAnchor
    {T A : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D)
    (hnot : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K T) a D.head) :
    data.incomingTail = data.contact.forwardEdge.1 ∨
      ActiveRetainedForwardVertexUnrootedOutcome
        (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T A data.contact.owner := by
  rcases data.endpointConflict with htail | hhead
  · exact Or.inl htail
  · right
    have hx : data.contact.forwardEdge.2 ∈ retainedForwardVerticesAt T
        (selectedErasedCompression
          (ForwardConflictIndexed (L := L) (hL := hL)
            (hground := hground)) S K
          (chosenRequest data.contact.owner.1)).path :=
      (retainedForwardEdgeAt_endpoints T _ data.contact.retained).2
    apply activeRequestAt_retainedForwardVertex_unrooted_outcome
      (ForwardConflictIndexed (L := L) (hL := hL) (hground := hground))
        S K T A data.contact.owner hx
    simpa only [← hhead] using hnot

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.sameTail_or_unrootedAnchor
#print axioms
  Erdos599.DWeb.KappaLadder.LastDeletedHead.finish_rooted_of_beforeEq_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.before_head_or_finish_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.before_head_of_unrooted_finish
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.before_head_of_unrooted_endpoint
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.segmentLastContact_beforeEq_incomingTail
