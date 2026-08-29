/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedSimultaneous

/-!
# Reserved-record refinement of the grounded split controls

The record omitted by stationary subtraction must be fixed before the final
request paths are selected.  Otherwise a selected route may use that record
as a backward-link owner even though it does not use the record's auxiliary
source.  We therefore refine the grounded strict/fragment controls by the
countable off-apex carrier of an initially omitted record, and then transport
the unused-stage certificate to the refined selection.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open Alternating PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K0 : GroundingSelection.Controls S}

private noncomputable local instance signedEdgeBEq :
    BEq (SignedEdge V) :=
  ⟨fun s t => @decide (s = t) (Classical.propDecidable _)⟩

private local instance signedEdgeLawfulBEq : LawfulBEq (SignedEdge V) :=
  ⟨by intro s t; simp⟩

private noncomputable local instance lambdaVertexBEq {I : Type u} :
    BEq (LambdaVertex V I) :=
  ⟨fun x y => @decide (x = y) (Classical.propDecidable _)⟩

private local instance lambdaVertexLawfulBEq {I : Type u} :
    LawfulBEq (LambdaVertex V I) :=
  ⟨by intro x y; simp⟩

private theorem count_backward_gadgetSteps_reserved {I : Type u}
    (J : PopularAuxiliary.Input Gamma I) (a : J.LV) (e : V × V) :
    List.count (SignedEdge.backward e) (J.gadgetSteps a) =
      List.count (.edge e.1 e.2) [a] := by
  rcases e with ⟨u, v⟩
  cases a with
  | old x =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]
  | edge x y =>
      by_cases hxy : (x, y) = (u, v)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
        exact (List.count_eq_one_of_mem (List.nodup_singleton _)
          (List.mem_singleton_self _)).trans
            (List.count_eq_one_of_mem (List.nodup_singleton _)
              (List.mem_singleton_self _)).symm
      · have hleft : List.count (SignedEdge.backward (u, v))
            (J.gadgetSteps (.edge x y)) = 0 :=
          List.count_eq_zero.mpr (by
            simp only [PopularAuxiliary.Input.gadgetSteps,
              List.mem_singleton]
            intro hs
            exact hxy (congrArg SignedEdge.edge hs).symm)
        have hright : List.count (.edge u v : J.LV) [.edge x y] = 0 :=
          List.count_eq_zero.mpr (by
            simp only [List.mem_singleton]
            intro hv
            have huv : u = x ∧ v = y := by simpa using hv
            exact hxy (Prod.ext huv.1.symm huv.2.symm))
        exact hleft.trans hright.symm
  | proxy i =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]

private theorem count_backward_connectorSteps_reserved {I : Type u}
    (J : PopularAuxiliary.Input Gamma I) (a b : J.LV) (e : V × V) :
    List.count (SignedEdge.backward e) (J.connectorSteps a b) = 0 := by
  unfold PopularAuxiliary.Input.connectorSteps
  split <;> simp [SignedEdge.forward, SignedEdge.backward]

private theorem count_backward_decodeWalkSteps_reserved {I : Type u}
    (J : PopularAuxiliary.Input Gamma I) {a b : J.LV}
    (q : Walk J.lambda.graph a b) (e : V × V) :
    List.count (SignedEdge.backward e) (J.decodeWalkSteps q) =
      List.count (.edge e.1 e.2) q.support := by
  classical
  induction q with
  | @nil a =>
      rw [J.decodeWalkSteps_nil, count_backward_gadgetSteps_reserved,
        Walk.support_nil]
  | @cons a b c hab q ih =>
      rw [J.decodeWalkSteps_cons, List.count_append, List.count_append,
        count_backward_gadgetSteps_reserved,
        count_backward_connectorSteps_reserved, Walk.support_cons, ih]
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.add_zero]
      omega

private theorem selectedRequestTrace_edge_backward_not_mem_reservedSplit
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (e : edgeRequests J S.cut) :
    SignedEdge.backward e.1 ∉ (selectedRequestTrace U S K (.inr e)).steps := by
  classical
  let p := strongSelectedPath U S K (.inr e)
  have hstart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  have hfinish : p.finish = .edge e.1.1 e.1.2 :=
    strongSelectedPath_finish U S K (.inr e)
  intro hmem
  have hpositive : 0 < List.count (SignedEdge.backward e.1)
      (selectedRequestTrace U S K (.inr e)).steps :=
    List.count_pos_iff.mpr hmem
  have hgadgetMem : (.edge e.1.1 e.1.2 : J.LV) ∈ p.walk.support := by
    rw [← hfinish]
    exact p.walk.end_mem_support
  have hgadgetCount :
      List.count (.edge e.1.1 e.1.2 : J.LV) p.walk.support = 1 :=
    List.count_eq_one_of_mem p.isPath hgadgetMem
  have htotal := count_backward_decodeWalkSteps_reserved J p.walk e.1
  have happ := congrArg (List.count (SignedEdge.backward e.1))
    (J.decodeFinitePathToEdgeEntry_steps_append p hstart
      e.1.1 e.1.2 hfinish)
  have hlast : List.count (SignedEdge.backward e.1)
      [SignedEdge.backward e.1] = 1 :=
    List.count_eq_one_of_mem (List.nodup_singleton _)
      (List.mem_singleton_self _)
  change List.count (SignedEdge.backward e.1)
      ((selectedRequestTrace U S K (.inr e)).steps ++
        [SignedEdge.backward e.1]) =
    List.count (SignedEdge.backward e.1) (J.decodeWalkSteps p.walk) at happ
  rw [List.count_append, hlast, htotal, hgadgetCount] at happ
  omega

private theorem selectedBackwardEdge_auxContact_offApex_reservedSplit
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request J S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges
      .backward) :
    (LambdaVertex.edge e.1 e.2 : J.LV) ∈
        (strongSelectedPath U S K r).support ∧
      (LambdaVertex.edge e.1 e.2 : J.LV) ≠ requestAuxVertex r := by
  let T := selectedRequestTrace U S K r
  obtain ⟨s, hs, hsd, hse⟩ :=
    EndpointTrace.erasedCompression_directionEdges_subset_steps
      J T .backward he
  have hsRaw : s ∈ J.decodeWalkSteps (strongSelectedPath U S K r).walk :=
    (selectedRequestTrace_steps_sublist U S K r).subset hs
  have heGadget : (LambdaVertex.edge e.1 e.2 : J.LV) ∈
      (strongSelectedPath U S K r).support := by
    have heSigned : e ∈ directedSignedEdgeSet .backward
        (J.decodeWalkSteps (strongSelectedPath U S K r).walk) :=
      ⟨s, hsRaw, hsd, hse⟩
    rw [J.backwardEdges_decodeWalkSteps
      (strongSelectedPath U S K r).walk] at heSigned
    exact heSigned
  refine ⟨heGadget, ?_⟩
  cases r with
  | inl x =>
      intro heApex
      cases heApex
  | inr f =>
      intro heApex
      have hef : e = f.1 := by
        exact Prod.ext (LambdaVertex.edge.inj heApex).1
          (LambdaVertex.edge.inj heApex).2
      have hsEq : s = SignedEdge.backward e := by
        rcases s with ⟨se, sd⟩
        simp only at hsd hse
        subst sd
        subst se
        rfl
      have hnot := selectedRequestTrace_edge_backward_not_mem_reservedSplit
        U S K f
      apply hnot
      rw [← hef]
      exact hsEq ▸ (by simpa only [T] using hs)

/-- Public split-input form of the edge-gadget contact carried by every
selected compressed backward edge.  This is independent of the particular
grounded control refinement and is used by later reserved selectors. -/
theorem selectedBackwardEdge_auxContact_offApex_split
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request J S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges
      .backward) :
    (LambdaVertex.edge e.1 e.2 : J.LV) ∈
        (strongSelectedPath U S K r).support ∧
      (LambdaVertex.edge e.1 e.2 : J.LV) ≠ requestAuxVertex r :=
  selectedBackwardEdge_auxContact_offApex_reservedSplit U S K r he

/-- Complete auxiliary carrier of an initially omitted grounded record. -/
def splitGroundedReservedRecordCarrier
    (R : L.SplitGroundedUnusedRecord hL hground S K0) :
    Set (PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords) :=
  PopularSwitching.ladderTrace
      (L.splitGroundedPopularAuxiliaryInput hL.legal) R.record ∪
    {R.auxiliarySource.1}

theorem splitGroundedReservedRecordCarrier_countable
    (R : L.SplitGroundedUnusedRecord hL hground S K0) :
    (splitGroundedReservedRecordCarrier R).Countable := by
  exact (PopularSwitching.ladderTrace_countable
    (L.splitGroundedPopularAuxiliaryInput hL.legal) R.record).union
      (Set.countable_singleton R.auxiliarySource.1)

/-- Local request paths meeting the reserved carrier away from their own
request apex. -/
def splitGroundedReservedRecordCollidingPaths
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    Set (FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph) :=
  {p | ∃ x ∈ splitGroundedReservedRecordCarrier R \ {requestAuxVertex r},
    x ∈ p.support}

theorem splitGroundedReservedRecordCollidingIndices_nonstationary
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (requestFan S r) (splitGroundedReservedRecordCollidingPaths R r)) := by
  apply
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (PopularSwitching.restrictPaths (requestFan S r)
        (splitGroundedReservedRecordCollidingPaths R r))
      ((splitGroundedReservedRecordCarrier_countable R).mono Set.sdiff_subset)
      Set.disjoint_sdiff_left
  intro p hp
  obtain ⟨x, hxCarrier, hxp⟩ := hp.2
  exact ⟨x, hxCarrier, hxp⟩

/-- Final grounded controls after reserving one omitted record. -/
noncomputable def splitGroundedReservedControls
    (R : L.SplitGroundedUnusedRecord hL hground S K0) :
    GroundingSelection.Controls S :=
  let K := L.splitGroundedControls hL hground S
  {
    hangingLadder := K.hangingLadder
    hangingFragment := fun r ↦
      K.hangingFragment r ∪ splitGroundedReservedRecordCollidingPaths R r
    ladderRank := K.ladderRank
    ladderTrace := K.ladderTrace
    ladderRank_regressive := K.ladderRank_regressive
    ladderTrace_countable := K.ladderTrace_countable
    ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
    hangingLadder_meets := K.hangingLadder_meets
    fragmentIndices_nonstationary := by
      intro r
      have hbase := K.fragmentIndices_nonstationary r
      have hreserved :=
        splitGroundedReservedRecordCollidingIndices_nonstationary R r
      intro hstationary
      apply GroundingSelection.not_isStationaryBelow_union
        hL.legal.regular hL.legal.uncountable hbase hreserved
      exact hstationary.mono
        (GroundingControlledAssembly.restrictedIndices_union_subset
          (L.splitGroundedPopularAuxiliaryIndexed hL hground)
          (requestFan S r) (K.hangingFragment r)
          (splitGroundedReservedRecordCollidingPaths R r))
  }

/-- A path selected after reservation meets the reserved carrier only at its
own request apex. -/
theorem splitGroundedStrongSelectedPath_no_offApex_reservedRecord_contact
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {x : PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords}
    (hxCarrier : x ∈ splitGroundedReservedRecordCarrier R)
    (hxApex : x ≠ requestAuxVertex r) :
    x ∉ (strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r).support := by
  intro hxPath
  apply strongSelectedPath_not_mem_hangingFragment
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (splitGroundedReservedControls R) r
  right
  exact ⟨x, ⟨hxCarrier, by simpa only [Set.mem_singleton_iff]⟩, hxPath⟩

/-- In particular, the final selected path cannot start at the reserved
auxiliary source. -/
theorem splitGroundedStrongSelectedPath_start_ne_reservedAuxiliarySource
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    (strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r).start ≠
      R.auxiliarySource.1 := by
  intro hstart
  have hsourceCarrier : R.auxiliarySource.1 ∈
      splitGroundedReservedRecordCarrier R :=
    Or.inr (Set.mem_singleton _)
  have hsourceNeApex : R.auxiliarySource.1 ≠ requestAuxVertex r := by
    intro heq
    apply R.auxiliarySource_not_mem_cut
    rw [heq]
    exact requestAuxVertex_mem_cut r
  apply splitGroundedStrongSelectedPath_no_offApex_reservedRecord_contact
    R r hsourceCarrier hsourceNeApex
  rw [← hstart]
  exact (strongSelectedPath
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (splitGroundedReservedControls R) r).start_mem_support

/-- The reserved refinement retains both original grounded control
conditions. -/
theorem splitGroundedReservedStrongSelectedPath_avoids_strict_and_fragment
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    let p := strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r
    ¬ L.splitGroundedAssertion819StrictCollisionPath hL hground S r p ∧
      ¬ GroundingConcreteControls.hangingFragmentCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p := by
  dsimp only
  have hp := strongSelectedPath_mem_controlledRequestFan
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (splitGroundedReservedControls R) r
  refine ⟨?_, ?_⟩
  · intro hstrict
    exact hp.2 (Or.inl hstrict)
  · intro hfragment
    exact hp.2 (Or.inr (Or.inl hfragment))

/-- Every literal hanging contact left after the reserved refinement is
still the genuine equal-stage case. -/
theorem splitGroundedReservedStrongSelectedPath_hangingCollision_equalMatch
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hcollision : GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r
        (strongSelectedPath
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
            (splitGroundedReservedControls R) r)) :
    let p := strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r
    let hp : p.start ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source :=
      (strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (splitGroundedReservedControls R)).starts_in_source ⟨r, rfl⟩
    Nonempty (L.SplitGroundedAssertion819EqualMatch hL hground S r
      ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, hp⟩)) := by
  dsimp only
  let p := strongSelectedPath
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (splitGroundedReservedControls R) r
  have hpControlled := strongSelectedPath_mem_controlledRequestFan
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (splitGroundedReservedControls R) r
  let hpCollision : p ∈ (PopularSwitching.restrictPaths
      (requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths :=
    ⟨hpControlled.1.1.1, hcollision⟩
  have hnot :=
    (splitGroundedReservedStrongSelectedPath_avoids_strict_and_fragment
      R r).1
  have hmatch :=
    L.splitGroundedAssertion819EqualMatch_of_collision_of_not_strict
      hL hground S r p hpCollision hnot
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source hpCollision⟩ :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start,
        (strongSelectedWarp
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
            (splitGroundedReservedControls R)).starts_in_source
              ⟨r, rfl⟩⟩ := Subtype.ext rfl
  simpa only [congrArg
    (L.splitGroundedPopularAuxiliaryIndexed hL hground).f hs] using hmatch

/-- The reserved record cannot own a backward link of a finally selected
request route. -/
theorem splitGroundedSelectedBackwardLink_parent_ne_record
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (_hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    parent ≠ R.record := by
  intro hparentRecord
  subst parent
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      l.path l.path.start_mem_support l.nontrivial
  have heDirection : (l.path.start, y) ∈
      (selectedErasedCompression
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (splitGroundedReservedControls R) r).path.directionEdges
            .backward := by
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hy⟩
  obtain ⟨hePath, heOffApex⟩ :=
    selectedBackwardEdge_auxContact_offApex_reservedSplit
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (splitGroundedReservedControls R) r heDirection
  have heCarrier :
      (PopularAuxiliary.Input.LambdaVertex.edge l.path.start y :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).LV) ∈
        splitGroundedReservedRecordCarrier R := by
    left
    right
    exact ⟨(l.path.start, y), hsub.2 hy, rfl⟩
  exact splitGroundedStrongSelectedPath_no_offApex_reservedRecord_contact
    R r heCarrier heOffApex hePath

/-- A backward-link owner under the reserved controls either has a finite
allowed-source prefix to the link exit, or is precisely the genuine
equal-stage hanging case retained by successor-correct 8.19. -/
theorem splitGroundedReservedBackwardOwner_rootPrefix_or_equalMatch
    (R : L.SplitGroundedUnusedRecord hL hground S K0)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    (∃ q : FinitePath Gamma.graph,
      q.start ∈ Gamma.source \ {R.record.initial} ∧
      q.finish = l.path.start ∧ q.support ⊆ parent.support ∧
      q.edgeSet ⊆ parent.edgeSet) ∨
    let p := strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r
    let hp : p.start ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source :=
      (strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (splitGroundedReservedControls R)).starts_in_source ⟨r, rfl⟩
    Nonempty (L.SplitGroundedAssertion819EqualMatch hL hground S r
      ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, hp⟩)) := by
  have hne : parent ≠ R.record :=
    splitGroundedSelectedBackwardLink_parent_ne_record
      R r l hl hldir parent hparent hsub
  by_cases hgrounded : PopularAuxiliary.IsGroundedPath Gamma parent
  · left
    have hrootNe : parent.initial ≠ R.record.initial := by
      intro heq
      apply hne
      apply Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa)) hparent
        R.limit_inessential.1
      · exact parent.initial_mem_support
      · rw [heq]
        exact R.record.initial_mem_support
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix parent
        (hsub.1 l.path.start_mem_support)
    refine ⟨q, ?_, hqFinish, hqSupport, hqEdges⟩
    rw [hqStart]
    exact ⟨hgrounded, fun heq ↦
      hrootNe (Set.mem_singleton_iff.mp heq)⟩
  · right
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    have heDirection : (l.path.start, y) ∈
        (selectedErasedCompression
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
            (splitGroundedReservedControls R) r).path.directionEdges
              .backward := by
      simp only [AltPath.directionEdges, Set.mem_iUnion]
      exact ⟨l, hl, hldir, hy⟩
    obtain ⟨hePath, heOffApex⟩ :=
      selectedBackwardEdge_auxContact_offApex_reservedSplit
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (splitGroundedReservedControls R) r heDirection
    have hcollision : GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r
        (strongSelectedPath
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
            (splitGroundedReservedControls R) r) := by
      refine ⟨parent, ⟨?_, hgrounded⟩,
        LambdaVertex.edge l.path.start y, ?_, hePath⟩
      · simpa only [splitGroundedPopularAuxiliaryInput] using hparent
      · exact ⟨Or.inr ⟨(l.path.start, y), hsub.2 hy, rfl⟩, by
          simpa only [Set.mem_singleton_iff] using heOffApex⟩
    exact splitGroundedReservedStrongSelectedPath_hangingCollision_equalMatch
      R r hcollision

/-- The initially omitted stage remains absent from the final refined
selected source family. -/
theorem SplitGroundedUnusedRecord.stage_unused_reservedControls
    (R : L.SplitGroundedUnusedRecord hL hground S K0) :
    R.stage ∉ Popular.initialIndicesOf
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (splitGroundedReservedControls R)).paths
      (strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (splitGroundedReservedControls R)).starts_in_source := by
  rintro ⟨p, hp, hpindex⟩
  obtain ⟨r, rfl⟩ := hp
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let W := strongSelectedWarp U S (splitGroundedReservedControls R)
  let q := strongSelectedPath U S (splitGroundedReservedControls R) r
  have hqW : q ∈ W.paths := ⟨r, rfl⟩
  have hsourceEq :
      (⟨q.start, W.starts_in_source hqW⟩ :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) =
      R.auxiliarySource := by
    apply L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground
    exact hpindex.trans R.source_index.symm
  exact splitGroundedStrongSelectedPath_start_ne_reservedAuxiliarySource R r
    (congrArg Subtype.val hsourceEq)

/-- Repackage the same grounded record as the unused record for the final
reserved controls. -/
noncomputable def SplitGroundedUnusedRecord.forReservedControls
    (R : L.SplitGroundedUnusedRecord hL hground S K0) :
    L.SplitGroundedUnusedRecord hL hground S
      (splitGroundedReservedControls R) where
  stage := R.stage
  stage_ground := R.stage_ground
  stage_unused := R.stage_unused_reservedControls
  record := R.record
  chosen := R.chosen
  grounded := R.grounded
  limit_inessential := R.limit_inessential
  auxiliarySource := R.auxiliarySource
  source_index := R.source_index
  auxiliarySource_not_mem_cut := R.auxiliarySource_not_mem_cut
  source_represents := R.source_represents

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.stage_unused_reservedControls
