/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingReservedRecordControls
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Backward-owner exclusion for reserved grounding controls

The reserved controls remove every selected auxiliary route which meets the
reserved grounded record away from its own apex.  A genuine compressed
backward link on that record necessarily visits one of its edge gadgets.  If
that gadget were the apex, the head-stopping decoder would have removed the
corresponding backward step.  Hence the reserved record cannot own any
backward link of a selected erased route.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DWeb.DirectedPath Alternating PopularGroundingBridge
open PopularAuxiliary.Input GroundingSimultaneousDecode
open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}

private noncomputable local instance signedEdgeBEq :
    BEq (PopularAuxiliary.Input.SignedEdge V) :=
  ⟨fun s t => @decide (s = t) (Classical.propDecidable _)⟩

private local instance signedEdgeLawfulBEq :
    LawfulBEq (PopularAuxiliary.Input.SignedEdge V) :=
  ⟨by intro s t; simp⟩

private noncomputable local instance lambdaVertexBEq {I : Type u} :
    BEq (PopularAuxiliary.Input.LambdaVertex V I) :=
  ⟨fun x y => @decide (x = y) (Classical.propDecidable _)⟩

private local instance lambdaVertexLawfulBEq {I : Type u} :
    LawfulBEq (PopularAuxiliary.Input.LambdaVertex V I) :=
  ⟨by intro x y; simp⟩

private theorem count_backward_gadgetSteps {I : Type u}
    (J : PopularAuxiliary.Input Gamma I) (a : J.LV) (e : V × V) :
    List.count (PopularAuxiliary.Input.SignedEdge.backward e)
        (J.gadgetSteps a) =
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
      · have hleft :
            List.count (PopularAuxiliary.Input.SignedEdge.backward (u, v))
                (J.gadgetSteps (.edge x y)) = 0 :=
          List.count_eq_zero.mpr (by
            simp only [PopularAuxiliary.Input.gadgetSteps,
              List.mem_singleton]
            intro hs
            exact hxy (congrArg PopularAuxiliary.Input.SignedEdge.edge hs).symm)
        have hright :
            List.count (.edge u v : J.LV) [.edge x y] = 0 :=
          List.count_eq_zero.mpr (by
            simp only [List.mem_singleton]
            intro hv
            have huv : u = x ∧ v = y := by simpa using hv
            exact hxy (Prod.ext huv.1.symm huv.2.symm))
        exact hleft.trans hright.symm
  | proxy i =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]

private theorem count_backward_connectorSteps {I : Type u}
    (J : PopularAuxiliary.Input Gamma I) (a b : J.LV) (e : V × V) :
    List.count (PopularAuxiliary.Input.SignedEdge.backward e)
        (J.connectorSteps a b) = 0 := by
  unfold PopularAuxiliary.Input.connectorSteps
  split <;> simp [PopularAuxiliary.Input.SignedEdge.forward,
    PopularAuxiliary.Input.SignedEdge.backward]

private theorem count_backward_decodeWalkSteps {I : Type u}
    (J : PopularAuxiliary.Input Gamma I) {a b : J.LV}
    (q : _root_.Erdos599.DirectedPath.Walk J.lambda.graph a b) (e : V × V) :
    List.count (PopularAuxiliary.Input.SignedEdge.backward e)
        (J.decodeWalkSteps q) =
      List.count (PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2)
        q.support := by
  classical
  induction q with
  | @nil a =>
      rw [J.decodeWalkSteps_nil, count_backward_gadgetSteps,
        _root_.Erdos599.DirectedPath.Walk.support_nil]
  | @cons a b c hab q ih =>
      rw [J.decodeWalkSteps_cons, List.count_append, List.count_append,
        count_backward_gadgetSteps, count_backward_connectorSteps,
        _root_.Erdos599.DirectedPath.Walk.support_cons, ih]
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.add_zero]
      omega

private theorem selectedRequestTrace_edge_backward_not_mem_reserved
    (R : L.UnusedGroundedRecord hL S)
    (e : edgeRequests (L.popularAuxiliaryInput hL.legal) S.cut) :
    PopularAuxiliary.Input.SignedEdge.backward e.1 ∉
      (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (.inr e)).steps := by
  classical
  let J := L.popularAuxiliaryInput hL.legal
  let p := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (.inr e)
  have hstart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)).starts_in_source ⟨.inr e, rfl⟩
  have hfinish : p.finish = .edge e.1.1 e.1.2 :=
    strongSelectedPath_finish (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (.inr e)
  intro hmem
  have hpositive :
      0 < List.count (PopularAuxiliary.Input.SignedEdge.backward e.1)
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (.inr e)).steps :=
    List.count_pos_iff.mpr hmem
  have hgadgetMem : (.edge e.1.1 e.1.2 : J.LV) ∈ p.walk.support := by
    rw [← hfinish]
    exact p.walk.end_mem_support
  have hgadgetCount :
      List.count (.edge e.1.1 e.1.2 : J.LV) p.walk.support = 1 :=
    List.count_eq_one_of_mem p.isPath hgadgetMem
  have htotal := count_backward_decodeWalkSteps J p.walk e.1
  have happ := congrArg
    (List.count (PopularAuxiliary.Input.SignedEdge.backward e.1))
    (J.decodeFinitePathToEdgeEntry_steps_append p hstart
      e.1.1 e.1.2 hfinish)
  have hlast :
      List.count (PopularAuxiliary.Input.SignedEdge.backward e.1)
        [PopularAuxiliary.Input.SignedEdge.backward e.1] = 1 :=
    List.count_eq_one_of_mem (List.nodup_singleton _)
      (List.mem_singleton_self _)
  change List.count (PopularAuxiliary.Input.SignedEdge.backward e.1)
      ((selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (.inr e)).steps ++
          [PopularAuxiliary.Input.SignedEdge.backward e.1]) =
    List.count (PopularAuxiliary.Input.SignedEdge.backward e.1)
      (J.decodeWalkSteps p.walk) at happ
  rw [List.count_append, hlast, htotal, hgadgetCount] at happ
  omega

private theorem walk_edgeSet_nonempty_of_ne {a b : V}
    (w : _root_.Erdos599.DirectedPath.Walk Gamma.graph a b)
    (hab : a ≠ b) : w.edgeSet.Nonempty := by
  induction w with
  | nil => exact False.elim (hab rfl)
  | @cons a c b hac w ih =>
      rw [_root_.Erdos599.DirectedPath.Walk.edgeSet_cons]
      exact Set.Nonempty.mono Set.subset_union_left
        (Set.singleton_nonempty (a, c))

private theorem link_edgeSet_nonempty (l : Link Gamma.graph) :
    l.path.edgeSet.Nonempty :=
  walk_edgeSet_nonempty_of_ne l.path.walk l.nontrivial

/-- No compressed backward link selected with the reserved controls can be
owned by the reserved limiting-ladder record. -/
theorem UnusedGroundedRecord.backwardLink_parent_ne_record
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (_hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    parent ≠ R.record := by
  intro hparentRecord
  subst parent
  obtain ⟨e, heLink⟩ := link_edgeSet_nonempty l
  have heRecord : e ∈ R.record.edgeSet := hsub.2 heLink
  have heDirection : e ∈
      (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) r).path.directionEdges
            .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, heLink⟩
  let T := selectedRequestTrace
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r
  obtain ⟨s, hs, hsd, hse⟩ :=
    PopularAuxiliary.Input.EndpointTrace.erasedCompression_directionEdges_subset_steps
      (L.popularAuxiliaryInput hL.legal) T .backward heDirection
  have hsRaw : s ∈ (L.popularAuxiliaryInput hL.legal).decodeWalkSteps
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).walk :=
    (selectedRequestTrace_steps_sublist
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).subset hs
  have heGadget : PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 ∈
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).support := by
    have heSigned : e ∈ PopularAuxiliary.Input.directedSignedEdgeSet
        .backward
        ((L.popularAuxiliaryInput hL.legal).decodeWalkSteps
          (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) r).walk) :=
      ⟨s, hsRaw, hsd, hse⟩
    rw [(L.popularAuxiliaryInput hL.legal).backwardEdges_decodeWalkSteps] at heSigned
    exact heSigned
  have heCarrier : PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 ∈
      reservedRecordCarrier R := by
    left
    right
    exact ⟨e, heRecord, rfl⟩
  by_cases heApex :
      PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 =
        requestAuxVertex r
  · cases r with
    | inl x => cases heApex
    | inr f =>
        have hef : e = f.1 := by
          exact Prod.ext
            (PopularAuxiliary.Input.LambdaVertex.edge.inj heApex).1
            (PopularAuxiliary.Input.LambdaVertex.edge.inj heApex).2
        have hsEq : s = PopularAuxiliary.Input.SignedEdge.backward e := by
          rcases s with ⟨se, sd⟩
          simp only at hsd hse
          subst sd
          subst se
          rfl
        have hnot := selectedRequestTrace_edge_backward_not_mem_reserved R f
        apply hnot
        rw [← hef]
        exact hsEq ▸ hs
  · exact strongSelectedPath_no_offApex_reservedRecord_contact R
      r heCarrier heApex heGadget

private theorem selectedRequestTrace_initial_of_start_old_reserved
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) (x : V)
    (hstart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r).start = .old x) :
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r).initial = x := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let K := L.reservedGroundedControls hL S R
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial = x
      apply J.decodeFinitePathToExit_initial_of_start_old
      exact hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial = x
      apply J.decodeFinitePathToEdgeEntry_initial_of_start_old
      exact hstart

private theorem selectedRequestTrace_initial_mem_proxy_reserved
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (i : L.groundedInfiniteRecords)
    (hstart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r).start = .proxy i) :
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r).initial ∈ i.1.support := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let K := L.reservedGroundedControls hL S R
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial ∈
        (J.proxyPath i).support
      apply J.decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
      exact hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial ∈
        (J.proxyPath i).support
      apply J.decodeFinitePathToEdgeEntry_initial_mem_proxyPath_of_start_proxy
      exact hstart

/-- The initial vertex of every request selected with reserved controls has
a finite prefix in its grounded limiting-ladder parent, starting at an
original source different from the reserved record's source. -/
theorem UnusedGroundedRecord.exists_reservedSelectedRequest_rootPrefix
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        q.start ∈ Gamma.source \ {R.record.initial} ∧
        q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) r).initial ∧
        q.support ⊆ parent.support ∧ q.edgeSet ⊆ parent.edgeSet := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let K := L.reservedGroundedControls hL S R
  let p := strongSelectedPath U S K r
  let T := selectedRequestTrace U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSelectedSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  have hpGround := strongSelectedPath_mem_groundedSourcePaths_reserved R r
  obtain ⟨hpSource, _haGround⟩ := hpGround
  let source : J.lambda.source := ⟨p.start, hpSelectedSource⟩
  have hsourceNe : source ≠ R.auxiliarySource := by
    intro hEq
    apply strongSelectedPath_start_ne_reservedAuxiliarySource R r
    exact congrArg Subtype.val hEq
  rcases J.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · let xs : L.groundedFiniteTerminalSet := ⟨x, hxFinite⟩
    have hindex : U.f source = L.finiteTerminalIndex xs := by
      have hs : source =
          ⟨.old xs.1, (J.mem_lambda_source_old xs.1).2 xs.2⟩ := by
        exact Subtype.ext hstart
      rw [congrArg U.f hs]
      rfl
    have ha : L.finiteTerminalIndex xs ∈ L.phiGround :=
      L.finiteTerminalStage_mem_phiGround hL.legal xs
    let xs' : L.finiteTerminalSet :=
      ⟨xs.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2⟩
    obtain ⟨_hfinite, parent, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec xs'
    have hstage : L.finiteTerminalStage xs' = L.finiteTerminalIndex xs := rfl
    rw [hstage] at hchosen
    have hparentSource : parent.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hpq : parent = q := Option.some.inj (hchosen.symm.trans hq)
      exact hpq ▸ hqSource
    have hTinitial : T.initial = x :=
      selectedRequestTrace_initial_of_start_old_reserved R r x hstart
    have hparentInessential :
        parent ∈ Gamma.inessentialPaths L.limitWarp :=
      L.recorded_mem_limitWarp_inessential_sourceGeometry hL.legal hchosen
    have hrootNe : R.record.initial ≠ parent.initial :=
      R.record_initial_ne_parent_initial_of_auxiliarySource_ne source
        (L.finiteTerminalIndex xs) parent hsourceNe hindex hchosen
          hparentInessential.1
    have htrace : T.initial ∈ parent.support := by
      rw [hTinitial]
      exact Gamma.terminal_mem_support hterminal
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix parent htrace
    refine ⟨parent, q, hparentInessential, ?_, hqFinish, hqSupport, hqEdges⟩
    rw [hqStart]
    exact ⟨hparentSource, fun heq =>
      hrootNe (Set.mem_singleton_iff.mp heq).symm⟩
  · have hindex : U.f source = L.groundedInfiniteStage i := by
      have hs : source = ⟨.proxy i, J.mem_lambda_source_proxy i⟩ := by
        exact Subtype.ext hstart
      rw [congrArg U.f hs]
      rfl
    have ha : L.groundedInfiniteStage i ∈ L.phiGround :=
      (L.groundedInfiniteStage_spec i).1.1
    have hchosen := (L.groundedInfiniteStage_spec i).2
    have hparentSource : i.1.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hiq : i.1 = q := Option.some.inj (hchosen.symm.trans hq)
      exact hiq ▸ hqSource
    have htrace : T.initial ∈ i.1.support :=
      selectedRequestTrace_initial_mem_proxy_reserved R r i hstart
    have hparentInessential :
        i.1 ∈ Gamma.inessentialPaths L.limitWarp :=
      L.recorded_mem_limitWarp_inessential_sourceGeometry hL.legal hchosen
    have hrootNe : R.record.initial ≠ i.1.initial :=
      R.record_initial_ne_parent_initial_of_auxiliarySource_ne source
        (L.groundedInfiniteStage i) i.1 hsourceNe hindex hchosen
          hparentInessential.1
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix i.1 htrace
    refine ⟨i.1, q, hparentInessential, ?_, hqFinish,
      hqSupport, hqEdges⟩
    rw [hqStart]
    exact ⟨hparentSource, fun heq =>
      hrootNe (Set.mem_singleton_iff.mp heq).symm⟩

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.backwardLink_parent_ne_record
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.exists_reservedSelectedRequest_rootPrefix
