/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAuxiliary
import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Source-rooted reachability inside one grounded-record trace

A finite recorded path is represented in `Lambda` backwards: its auxiliary
source is the old terminal, and the reverse gadget chain reaches every old
vertex and every edge gadget of the record.  A recorded ray is represented
by a proxy.  The proxy enters any one of its edge gadgets directly; the
zero-length `E,V` join then also reaches the tail of that edge.  Thus every
vertex of the full trace of one represented record is reachable from its
own auxiliary source without leaving that trace (apart from the proxy
source itself).

The theorem is stated for the literal `EncodedAt` relation.  In particular,
it does not identify an arbitrary source with an unrelated limiting-ladder
path and does not mix finite terminals with proxy records.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingGroundedRecordTraceReachability

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (J : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The literal record represented by one auxiliary source vertex.  This is
the lightweight part of `GroundingLegalSourceEncoding.EncodedAt`; source-set
membership is kept separately by the callers that index actual sources. -/
def Represents (J : Input Gamma I) (parent : Gamma.DPath) (source : LV J) :
    Prop :=
  (∃ p : FinitePath Gamma.graph,
      parent = .inl p ∧ source = .old p.finish) ∨
    ∃ i : I, parent = J.proxyPath i ∧ source = .proxy i

private theorem exists_finitePath_of_walk
    (J : Input Gamma I) {a b : LV J}
    (w : Walk J.lambda.graph a b) (C : Set (LV J))
    (hw : ∀ ⦃z⦄, z ∈ w.support → z ∈ C) :
    ∃ q : FinitePath J.lambda.graph,
      q.start = a ∧ q.finish = b ∧ q.support ⊆ C := by
  obtain ⟨q, hq⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := J.lambda.graph.Adj) w
  let r : FinitePath J.lambda.graph :=
    { start := a
      finish := b
      walk := q.1
      isPath := q.2 }
  refine ⟨r, rfl, rfl, ?_⟩
  intro z hz
  exact hw (hq hz)

private theorem familyEdges_of_mem_record
    (J : Input Gamma I) {p : Gamma.DPath}
    (hp : p ∈ J.ladder.paths) : p.edgeSet ⊆ J.familyEdges := by
  intro e he
  exact ⟨p, hp, he⟩

/-- The tail following an occurring edge of a finite walk, with the exact
tail endpoint retained in its type. -/
private theorem exists_walk_tail_of_mem_edgeSet {D : Digraph V} :
    ∀ {a b x y : V} (p : Walk D a b), (x, y) ∈ p.edgeSet →
      ∃ (hxy : D.Adj x y) (q : Walk D y b), q.edgeSet ⊆ p.edgeSet
  | _, _, _, _, .nil, h => by simpa using h
  | a, b, x, y, @Walk.cons _ _ _ c _ hac tail, h => by
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at h
      rcases h with h | h
      · cases h
        exact ⟨hac, tail, Set.subset_union_right⟩
      · obtain ⟨hxy, q, hq⟩ := exists_walk_tail_of_mem_edgeSet tail h
        exact ⟨hxy, q, hq.trans Set.subset_union_right⟩

/-- Every vertex of the own trace of an auxiliary-source-encoded ladder
record is reached by a finite auxiliary path whose support stays in that
trace together with the source. -/
theorem exists_auxiliaryPath_to_mem_ladderTrace_union_source
    (J : Input Gamma I) {parent : Gamma.DPath} {source z : LV J}
    (hparent : parent ∈ J.ladder.paths)
    (hsource : Represents J parent source)
    (hz : z ∈ PopularSwitching.ladderTrace J parent ∪ {source}) :
    ∃ q : FinitePath J.lambda.graph,
      q.start = source ∧ q.finish = z ∧
        q.support ⊆ PopularSwitching.ladderTrace J parent ∪ {source} := by
  rcases hsource with ⟨p, rfl, rfl⟩ | ⟨i, hparentProxy, rfl⟩
  · rcases hz with hzTrace | hzSource
    · cases z with
      | old x =>
          have hx : x ∈ p.support :=
            by
              have hx' : x ∈
                  DirectedPath.Path.support (Sum.inl p : Gamma.DPath) := by
                simpa [PopularSwitching.ladderTrace] using hzTrace
              simpa only [Path.support] using hx'
          let suffix := p.suffixFrom x hx
          have hsuffixFamily : suffix.edgeSet ⊆ J.familyEdges :=
            (p.suffixFrom_edgeSet_subset x hx).trans
              (familyEdges_of_mem_record J hparent)
          let w := GroundingCutDecoder.reverseGadgetWalk
            J suffix.walk hsuffixFamily
          obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
            exists_finitePath_of_walk J w
              (PopularSwitching.ladderTrace J (.inl p) ∪ {.old p.finish}) (by
                intro y hy
                rcases GroundingCutDecoder.mem_reverseGadgetWalk_support
                    J suffix.walk hsuffixFamily hy with
                    hyx | hyfinish | ⟨e, he, rfl⟩
                · left
                  subst y
                  simp only [PopularSwitching.ladderTrace, Set.mem_union,
                    Set.mem_image]
                  exact Or.inl ⟨suffix.start,
                    p.suffixFrom_support_subset x hx suffix.start_mem_support,
                    rfl⟩
                · right
                  simpa [suffix] using hyfinish
                · left
                  simp only [PopularSwitching.ladderTrace, Set.mem_union,
                    Set.mem_image]
                  exact Or.inr ⟨e, p.suffixFrom_edgeSet_subset x hx he,
                    by simp⟩)
          refine ⟨q, ?_, ?_, hqSupport⟩
          · simpa [w, suffix] using hqStart
          · simpa [w, suffix] using hqFinish
      | edge x y =>
          have hxy : (x, y) ∈ p.edgeSet :=
            by simpa [PopularSwitching.ladderTrace] using hzTrace
          obtain ⟨hxyAdj, tail, htailEdges⟩ :=
            exists_walk_tail_of_mem_edgeSet p.walk hxy
          have hxyFamily : (x, y) ∈ J.familyEdges :=
            familyEdges_of_mem_record J hparent hxy
          have htailFamily : tail.edgeSet ⊆ J.familyEdges :=
            htailEdges.trans (familyEdges_of_mem_record J hparent)
          let w := GroundingCutDecoder.reverseGadgetCore
            J hxyAdj tail hxyFamily htailFamily
          obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
            exists_finitePath_of_walk J w
              (PopularSwitching.ladderTrace J (.inl p) ∪ {.old p.finish}) (by
                intro a ha
                rcases GroundingCutDecoder.mem_reverseGadgetCore_support
                    J hxyAdj tail hxyFamily htailFamily ha with
                    haFinish | ⟨e, he, rfl⟩
                · right
                  simpa using haFinish
                · left
                  simp only [PopularSwitching.ladderTrace, Set.mem_union,
                    Set.mem_image]
                  rcases he with he | he
                  · subst e
                    exact Or.inr ⟨(x, y), hxy, rfl⟩
                  · exact Or.inr ⟨e, htailEdges he, by simp⟩)
          refine ⟨q, ?_, ?_, hqSupport⟩
          · simpa [w] using hqStart
          · simpa [w] using hqFinish
      | proxy j =>
          simpa [PopularSwitching.ladderTrace] using hzTrace
    · have hzEq : z = .old p.finish := by simpa using hzSource
      subst z
      let w : Walk J.lambda.graph (.old p.finish) (.old p.finish) := .nil
      exact exists_finitePath_of_walk J w
        (PopularSwitching.ladderTrace J (.inl p) ∪ {.old p.finish}) (by
          intro y hy
          right
          simpa [w] using hy)
  · obtain ⟨r, hr⟩ := J.proxy_isRay i
    rw [hr] at hparentProxy
    subst parent
    rcases hz with hzTrace | hzSource
    · cases z with
      | old x =>
          have hx : x ∈ r.support :=
            by
              have hx' : x ∈
                  DirectedPath.Path.support (Sum.inr r : Gamma.DPath) := by
                simpa [PopularSwitching.ladderTrace] using hzTrace
              simpa only [Path.support] using hx'
          obtain ⟨n, rfl⟩ := hx
          have hedgeFamily : (r n, r (n + 1)) ∈ J.familyEdges :=
            familyEdges_of_mem_record J hparent ⟨n, rfl⟩
          have hproxyEdge : J.lambda.graph.Adj
              (.proxy i) (.edge (r n) (r (n + 1))) :=
            (J.lambda_adj_proxy_edge i (r n) (r (n + 1))).2
              ⟨hedgeFamily, r n, by rw [hr]; exact r.apply_mem_support n,
                r.adj_succ n⟩
          have hedgeOld : J.lambda.graph.Adj
              (.edge (r n) (r (n + 1))) (.old (r n)) :=
            (J.lambda_adj_edge_old (r n) (r (n + 1)) (r n)).2
              ⟨hedgeFamily, Or.inl rfl⟩
          let w : Walk J.lambda.graph (.proxy i) (.old (r n)) :=
            .cons hproxyEdge (.cons hedgeOld .nil)
          exact exists_finitePath_of_walk J w
            (PopularSwitching.ladderTrace J (.inr r) ∪ {.proxy i}) (by
              intro y hy
              simp only [w, Walk.support_cons, Walk.support_nil,
                List.mem_cons, List.not_mem_nil] at hy
              rcases hy with rfl | hy
              · exact Or.inr (Set.mem_singleton _)
              · rcases hy with rfl | hy
                · exact Or.inl (by
                    simp only [PopularSwitching.ladderTrace, Set.mem_union,
                      Set.mem_image]
                    exact Or.inr ⟨(r n, r (n + 1)), ⟨n, rfl⟩, rfl⟩)
                · rcases hy with rfl | hy
                  · exact Or.inl (by
                      simp only [PopularSwitching.ladderTrace, Set.mem_union,
                        Set.mem_image]
                      exact Or.inl ⟨r n, by
                        change r n ∈ r.support
                        exact r.apply_mem_support n, rfl⟩)
                  · exact hy.elim)
      | edge x y =>
          have hxy : (x, y) ∈ r.edgeSet :=
            by simpa [PopularSwitching.ladderTrace] using hzTrace
          obtain ⟨n, hxy⟩ := hxy
          injection hxy with hx hy
          subst x
          subst y
          have hedgeFamily : (r n, r (n + 1)) ∈ J.familyEdges :=
            familyEdges_of_mem_record J hparent ⟨n, rfl⟩
          have hproxyEdge : J.lambda.graph.Adj
              (.proxy i) (.edge (r n) (r (n + 1))) :=
            (J.lambda_adj_proxy_edge i (r n) (r (n + 1))).2
              ⟨hedgeFamily, r n, by rw [hr]; exact r.apply_mem_support n,
                r.adj_succ n⟩
          let w : Walk J.lambda.graph
              (.proxy i) (.edge (r n) (r (n + 1))) :=
            .cons hproxyEdge .nil
          exact exists_finitePath_of_walk J w
            (PopularSwitching.ladderTrace J (.inr r) ∪ {.proxy i}) (by
              intro a ha
              simp only [w, Walk.support_cons, Walk.support_nil,
                List.mem_cons, List.not_mem_nil] at ha
              rcases ha with rfl | ha
              · exact Or.inr (Set.mem_singleton _)
              · rcases ha with rfl | ha
                · exact Or.inl (by
                    simp only [PopularSwitching.ladderTrace, Set.mem_union,
                      Set.mem_image]
                    exact Or.inr ⟨(r n, r (n + 1)), ⟨n, rfl⟩, rfl⟩)
                · exact ha.elim)
      | proxy j =>
          simpa [PopularSwitching.ladderTrace] using hzTrace
    · have hzEq : z = .proxy i := by simpa using hzSource
      subst z
      let w : Walk J.lambda.graph (.proxy i) (.proxy i) := .nil
      exact exists_finitePath_of_walk J w
        (PopularSwitching.ladderTrace J (.inr r) ∪ {.proxy i}) (by
          intro y hy
          right
          simpa [w] using hy)

end GroundingGroundedRecordTraceReachability

namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath Stationary
open GroundingGroundedRecordTraceReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev GroundedInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

/-- The chosen record represented by one actual source of the grounded
split auxiliary.  This is source-indexed data, independent of any later
separator, cut, or unused-record selection. -/
structure SplitGroundedAuxiliarySourceRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (source : (GroundedInput L hL).lambda.source) where
  stage : Ladder.Stage kappa
  record : Gamma.DPath
  stage_ground : stage ∈ L.phiGround
  chosen : L.chosen stage = some record
  limit_inessential : record ∈ Gamma.inessentialPaths L.limitWarp
  represents : Represents (GroundedInput L hL) record source.1
  source_index : L.splitGroundedAuxiliarySourceIndex hL source = stage

/-- Every source of the grounded split auxiliary has its literal chosen
record data.  Finite sources decode through their recorded terminal; proxy
sources decode to the represented grounded ray. -/
theorem exists_splitGroundedAuxiliarySourceRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (source : (GroundedInput L hL).lambda.source) :
    Nonempty (L.SplitGroundedAuxiliarySourceRecord hL source) := by
  let J := GroundedInput L hL
  rcases source with ⟨source, hsource⟩
  cases source with
  | old x =>
      let xs : L.groundedFiniteTerminalSet :=
        ⟨x, (J.mem_lambda_source_old x).1 hsource⟩
      obtain ⟨a, ha, parent, hchosen, hterminal⟩ := xs.2
      have hstage : L.finiteTerminalIndex xs = a := by
        exact L.finiteTerminalStage_eq_of_split hL hchosen hterminal
          (L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2)
      have hinessential :
          parent ∈ Gamma.inessentialPaths L.limitWarp := by
        apply L.recorded_mem_inessential hL.recordedPathsPersist hchosen
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2
      rcases parent with p | r
      · have hfinish : p.finish = x := Option.some.inj hterminal
        exact ⟨{
          stage := a
          record := .inl p
          stage_ground := ha.1
          chosen := hchosen
          limit_inessential := hinessential
          represents := Or.inl ⟨p, rfl,
            congrArg PopularAuxiliary.Input.LambdaVertex.old hfinish.symm⟩
          source_index := hstage }⟩
      · change none = some x at hterminal
        cases hterminal
  | edge x y =>
      exact False.elim (J.not_mem_lambda_source_edge x y hsource)
  | proxy i =>
      let a := L.groundedInfiniteStage i
      have hchosen : L.chosen a = some i.1 :=
        (L.groundedInfiniteStage_spec i).2
      have hinessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp := by
        apply L.recorded_mem_inessential hL.recordedPathsPersist hchosen
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2
      exact ⟨{
        stage := a
        record := i.1
        stage_ground := (L.groundedInfiniteStage_spec i).1.1
        chosen := hchosen
        limit_inessential := hinessential
        represents := Or.inr ⟨i, rfl, rfl⟩
        source_index := rfl }⟩

/-- Canonical source-indexed choice of the grounded record data. -/
noncomputable def splitGroundedAuxiliarySourceRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (source : (GroundedInput L hL).lambda.source) :
    L.SplitGroundedAuxiliarySourceRecord hL source :=
  Classical.choice (L.exists_splitGroundedAuxiliarySourceRecord hL source)

namespace SplitGroundedAuxiliarySourceRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitLegal}
  {source : (GroundedInput L hL).lambda.source}

/-- The decoded record is literally a member of the ladder family stored
in the grounded auxiliary. -/
theorem record_mem_ladder
    (R : L.SplitGroundedAuxiliarySourceRecord hL source) :
    R.record ∈ (GroundedInput L hL).ladder.paths :=
  R.limit_inessential.1

/-- Reachability specialization for the source-indexed grounded record. -/
theorem exists_auxiliaryPath_to_mem_ownCarrier
    (R : L.SplitGroundedAuxiliarySourceRecord hL source)
    {z : PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords}
    (hz : z ∈ PopularSwitching.ladderTrace (GroundedInput L hL) R.record ∪
      {source.1}) :
    ∃ q : FinitePath (GroundedInput L hL).lambda.graph,
      q.start = source.1 ∧ q.finish = z ∧
        q.support ⊆
          PopularSwitching.ladderTrace (GroundedInput L hL) R.record ∪
            {source.1} :=
  exists_auxiliaryPath_to_mem_ladderTrace_union_source
    (GroundedInput L hL) R.record_mem_ladder R.represents hz

end SplitGroundedAuxiliarySourceRecord
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.GroundingGroundedRecordTraceReachability.exists_auxiliaryPath_to_mem_ladderTrace_union_source
#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedAuxiliarySourceRecord
#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedAuxiliarySourceRecord.exists_auxiliaryPath_to_mem_ownCarrier
