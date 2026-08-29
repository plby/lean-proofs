/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingControls
import ErdosProblems.Erdos599.DeferredGroundingSelectedNonstationarity
import ErdosProblems.Erdos599.GroundingGroundedRecordTraceReachability
import ErdosProblems.Erdos599.GroundingRelaxedCorridor
import ErdosProblems.Erdos599.GroundingRelaxedEscape
import ErdosProblems.Erdos599.GroundingSelectedForwardOrder
import ErdosProblems.Erdos599.PopularSourceCarrierCut

/-!
# A cut-avoiding grounded record for the deferred auxiliary

The trace-reachability and source-carrier argument is independent of the
legacy grounded-split encoding.  This file instantiates it directly for the
deferred auxiliary.  The chosen source is forced into `phiGround` by adding
the nonstationary deferred hanging set to the excluded indices.

This supplies an actual cut-avoiding record, but deliberately makes no claim
about the split-specific filtered frontier `splitGroundedRelevantBB`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Stationary
open GroundingGroundedRecordTraceReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev DeferredInput
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :=
  popularAuxiliaryInput L hlegal

/-- The literal chosen record represented by one source of the deferred
auxiliary.  Groundedness is not imposed here; it is obtained later by
stationarily excluding `phiHanging`. -/
structure DeferredAuxiliarySourceRecord
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (source : (DeferredInput L hlegal).lambda.source) where
  stage : Ladder.Stage kappa
  record : Gamma.DPath
  stage_mem_phi : stage ∈ phi L
  chosen : L.chosen stage = some record
  limit_inessential : record ∈ Gamma.inessentialPaths L.limitWarp
  represents : Represents (DeferredInput L hlegal) record source.1
  source_index : auxiliarySourceIndex L hlegal source = stage

/-- Every source of the deferred auxiliary carries its exact deferred
record data. -/
theorem exists_deferredAuxiliarySourceRecord
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (source : (DeferredInput L hlegal).lambda.source) :
    Nonempty (DeferredAuxiliarySourceRecord L hlegal source) := by
  let J := DeferredInput L hlegal
  rcases source with ⟨source, hsource⟩
  cases source with
  | old x =>
      let xs : finiteTerminalSet L :=
        ⟨x, (J.mem_lambda_source_old x).1 hsource⟩
      obtain ⟨haFinite, parent, hchosen, hterminal⟩ :=
        finiteTerminalStage_spec L xs
      let a := finiteTerminalStage L xs
      have hinessential :
          parent ∈ Gamma.inessentialPaths L.limitWarp := by
        apply L.recorded_mem_inessential hlegal.recordedPathsPersist hchosen
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2
      rcases parent with p | r
      · have hfinish : p.finish = x := Option.some.inj hterminal
        exact ⟨{
          stage := a
          record := .inl p
          stage_mem_phi := haFinite.1
          chosen := hchosen
          limit_inessential := hinessential
          represents := Or.inl ⟨p, rfl,
            congrArg PopularAuxiliary.Input.LambdaVertex.old hfinish.symm⟩
          source_index := rfl }⟩
      · change none = some x at hterminal
        cases hterminal
  | edge x y =>
      exact False.elim (J.not_mem_lambda_source_edge x y hsource)
  | proxy i =>
      let a := infiniteStage L i
      have hchosen : L.chosen a = some i.1 := (infiniteStage_spec L i).2
      have hinessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp := by
        apply L.recorded_mem_inessential hlegal.recordedPathsPersist hchosen
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2
      exact ⟨{
        stage := a
        record := i.1
        stage_mem_phi := (infiniteStage_spec L i).1.1
        chosen := hchosen
        limit_inessential := hinessential
        represents := Or.inr ⟨i, rfl, rfl⟩
        source_index := rfl }⟩

/-- Canonical choice of the record represented by a deferred auxiliary
source. -/
noncomputable def deferredAuxiliarySourceRecord
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (source : (DeferredInput L hlegal).lambda.source) :
    DeferredAuxiliarySourceRecord L hlegal source :=
  Classical.choice (exists_deferredAuxiliarySourceRecord L hlegal source)

namespace DeferredAuxiliarySourceRecord

variable {L : Gamma.KappaLadder kappa} {hlegal : IsDeferredLegal L}
  {source : (DeferredInput L hlegal).lambda.source}

theorem record_mem_ladder
    (R : DeferredAuxiliarySourceRecord L hlegal source) :
    R.record ∈ (DeferredInput L hlegal).ladder.paths :=
  R.limit_inessential.1

theorem exists_auxiliaryPath_to_mem_ownCarrier
    (R : DeferredAuxiliarySourceRecord L hlegal source)
    {z : PopularAuxiliary.Input.LambdaVertex V (infiniteRecords L)}
    (hz : z ∈ PopularSwitching.ladderTrace
        (DeferredInput L hlegal) R.record ∪ {source.1}) :
    ∃ q : FinitePath (DeferredInput L hlegal).lambda.graph,
      q.start = source.1 ∧ q.finish = z ∧
        q.support ⊆ PopularSwitching.ladderTrace
          (DeferredInput L hlegal) R.record ∪ {source.1} :=
  exists_auxiliaryPath_to_mem_ladderTrace_union_source
    (DeferredInput L hlegal) R.record_mem_ladder R.represents hz

/-- An encoded deferred source does not lie in the trace of a different
limiting-ladder component. -/
theorem source_not_mem_other_trace
    (R : DeferredAuxiliarySourceRecord L hlegal source)
    {p : Gamma.DPath}
    (hp : p ∈ (DeferredInput L hlegal).ladder.paths)
    (hne : R.record ≠ p) :
    source.1 ∉ PopularSwitching.ladderTrace
      (DeferredInput L hlegal) p := by
  let J := DeferredInput L hlegal
  rcases R.represents with ⟨q, hr, hs⟩ | ⟨i, _hr, hs⟩
  · have hsourceOwn : source.1 ∈
        PopularSwitching.ladderTrace J R.record := by
      rw [hs, PopularSwitching.old_mem_ladderTrace_iff, hr]
      exact q.finish_mem_support
    intro hsourceOther
    exact Set.disjoint_left.mp
      (PopularSwitching.ladderTrace_disjoint J R.record_mem_ladder hp hne)
      hsourceOwn hsourceOther
  · rw [hs]
    exact PopularSwitching.proxy_not_mem_ladderTrace J p i

end DeferredAuxiliarySourceRecord

/-- Pairwise disjoint, internally source-reachable full record carriers for
the deferred auxiliary. -/
noncomputable def deferredSourceCarrierFamily
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :
    Popular.SourceCarrierFamily (DeferredInput L hlegal).lambda := by
  let J := DeferredInput L hlegal
  let R := deferredAuxiliarySourceRecord L hlegal
  refine {
    carrier := fun x ↦ PopularSwitching.ladderTrace J (R x).record ∪ {x.1}
    disjoint := ?_
    internally_reachable := ?_ }
  · intro x y hxy
    have hrecords : (R x).record ≠ (R y).record := by
      intro heq
      have hchosen : L.chosen (R x).stage = some (R y).record := by
        rw [(R x).chosen, heq]
      have hstages := (bookkeeping L).chosen_stage_unique
        hlegal.validBookkeeping hchosen (R y).chosen
      apply hxy
      apply auxiliarySourceIndex_injective L hlegal
      exact (R x).source_index.trans (hstages.trans (R y).source_index.symm)
    apply Set.disjoint_left.mpr
    intro z hzX hzY
    rcases hzX with hzTraceX | hzSourceX <;>
      rcases hzY with hzTraceY | hzSourceY
    · exact Set.disjoint_left.mp
        (PopularSwitching.ladderTrace_disjoint J
          (R x).record_mem_ladder (R y).record_mem_ladder hrecords)
        hzTraceX hzTraceY
    · have hzy : z = y.1 := hzSourceY
      exact (R y).source_not_mem_other_trace
        (R x).record_mem_ladder hrecords.symm (hzy ▸ hzTraceX)
    · have hzx : z = x.1 := hzSourceX
      exact (R x).source_not_mem_other_trace
        (R y).record_mem_ladder hrecords (hzx ▸ hzTraceY)
    · exact hxy (Subtype.ext ((show z = x.1 from hzSourceX).symm.trans
        (show z = y.1 from hzSourceY)))
  · intro x z hz
    exact (R x).exists_auxiliaryPath_to_mem_ownCarrier hz

/-- A grounded deferred record omitted by the selected warp whose entire
encoded trace avoids the popular cut. -/
structure DeferredCutAvoidingRecord
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) where
  stage : Ladder.Stage kappa
  stage_ground : stage ∈ phiGround L
  stage_unused :
    stage ∉ Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
      (GroundingAssembly.selectedWarp
        (popularAuxiliaryIndexed L hL) S K).paths
      (GroundingAssembly.selectedWarp
        (popularAuxiliaryIndexed L hL) S K).starts_in_source
  record : Gamma.DPath
  chosen : L.chosen stage = some record
  grounded : record.initial ∈ Gamma.source
  limit_inessential : record ∈ Gamma.inessentialPaths L.limitWarp
  auxiliarySource : (popularAuxiliaryInput L hL.legal).lambda.source
  source_index :
    (popularAuxiliaryIndexed L hL).f auxiliarySource = stage
  auxiliarySource_not_mem_cut : auxiliarySource.1 ∉ S.cut
  source_represents : Represents
    (popularAuxiliaryInput L hL.legal) record auxiliarySource.1
  trace_disjoint : Disjoint
    (PopularSwitching.ladderTrace
      (popularAuxiliaryInput L hL.legal) record) S.cut

/-- The deferred auxiliary has an actual grounded, unused record whose
whole encoded trace misses the popular cut. -/
theorem exists_deferredCutAvoidingRecord
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) :
    Nonempty (DeferredCutAvoidingRecord L hL S K) := by
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let selected := GroundingAssembly.selectedWarp U S K
  let N := Popular.initialIndicesOf U selected.paths selected.starts_in_source
  have hN : ¬ IsStationaryBelow kappa (N ∪ phiHanging L) :=
    GroundingSelection.not_isStationaryBelow_union
      U.regular U.uncountable
      (GroundingAssembly.selectedWarp_initialIndices_nonstationary U S K)
      (phiHanging_not_stationary L hL.legal)
  obtain ⟨x, hxUnused, hxCut⟩ :=
    (deferredSourceCarrierFamily L hL.legal).exists_source_disjoint_cut_avoiding
      U S.cut S.not_strongly_popular (N ∪ phiHanging L) hN
  let R0 := deferredAuxiliarySourceRecord L hL.legal x
  have hxIndex : U.f x = R0.stage := by
    rw [show U.f = auxiliarySourceIndex L hL.legal from
      (auxiliarySourceIndex_eq_sourceIndex L hL.legal).symm]
    exact R0.source_index
  have hstageGround : R0.stage ∈ phiGround L := by
    by_contra hnotGround
    apply hxUnused
    rw [hxIndex]
    exact Or.inr ⟨R0.stage_mem_phi, hnotGround⟩
  obtain ⟨p, hpChosen, hpGround⟩ := hstageGround
  have hpEq : p = R0.record :=
    Option.some.inj (hpChosen.symm.trans R0.chosen)
  subst p
  have hxCut' : Disjoint
      (PopularSwitching.ladderTrace J R0.record ∪ {x.1}) S.cut := hxCut
  have hxNotCut : x.1 ∉ S.cut := by
    intro hx
    exact Set.disjoint_left.mp hxCut' (Or.inr rfl) hx
  exact ⟨{
    stage := R0.stage
    stage_ground := ⟨R0.record, R0.chosen, hpGround⟩
    stage_unused := by
      intro hselected
      apply hxUnused
      apply Or.inl
      rw [hxIndex]
      exact hselected
    record := R0.record
    chosen := R0.chosen
    grounded := hpGround
    limit_inessential := R0.limit_inessential
    auxiliarySource := x
    source_index := hxIndex
    auxiliarySource_not_mem_cut := hxNotCut
    source_represents := R0.represents
    trace_disjoint := hxCut'.mono_left Set.subset_union_left }⟩

namespace DeferredCutAvoidingRecord

variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
  {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
  {K : GroundingSelection.Controls S}

/-- The whole reserved record cannot meet the relaxed escape region.  This
is the input-generic content of Assertion 8.15, proved from the record's
literal auxiliary-source representation and full trace avoidance. -/
theorem wholeRecord_not_meetsEscape
    (R : DeferredCutAvoidingRecord L hL S K)
    (P : (popularAuxiliaryInput L hL.legal).Fragment)
    (hfragment : P ∈ GroundingCut.fragments
      (popularAuxiliaryInput L hL.legal) S.cut)
    (hparent : P.parent = R.record)
    (hwhole : P.path = P.parent) :
    ¬ P.MeetsEscape (popularAuxiliaryInput L hL.legal) S.cut := by
  let J := popularAuxiliaryInput L hL.legal
  rintro ⟨b, hbP, ⟨E⟩⟩
  rcases R.source_represents with ⟨p, hrecord, hsource⟩ |
      ⟨i, hrecord, hsource⟩
  · have hpath : P.path = (.inl p : Gamma.DPath) :=
      hwhole.trans (hparent.trans hrecord)
    have hbFinite : b ∈ p.support := by
      simpa only [hpath, DirectedPath.Path.support] using hbP
    have htSource : p.finish ∈ J.finiteSource := by
      apply (J.mem_lambda_source_old p.finish).1
      rw [← hsource]
      exact R.auxiliarySource.2
    have htNotCut :
        (PopularAuxiliary.Input.LambdaVertex.old p.finish : J.LV) ∉ S.cut := by
      intro ht
      apply R.auxiliarySource_not_mem_cut
      rw [hsource]
      exact ht
    have hbeforeEq : GroundingCut.BeforeEq P.path b p.finish := by
      rw [hpath]
      exact GroundingCut.beforeEq_terminal rfl hbFinite
    have hroute : ∃ q : FinitePath J.lambda.graph,
        q.start = .old p.finish ∧ q.finish ∈ J.lambda.target ∧
          J.lambda.Avoids q S.cut := by
      by_cases hEq : b = p.finish
      · subst b
        exact GroundingRelaxedCorridor.exists_ordinaryEscape_of_relaxed_of_start_mem
          J S.cut (Or.inr htSource) E
      · exact GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
          J S.cut P hfragment ⟨hbeforeEq, hEq⟩ htNotCut E
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ := hroute
    exact PopularAuxiliary.Input.no_avoiding_source_target_path
      J.lambda S.cut S.separates q
      (hqStart ▸ (J.mem_lambda_source_old p.finish).2 htSource)
      hqTarget hqAvoid
  · obtain ⟨r, hr⟩ := J.proxy_isRay i
    have hrecordRay : R.record = (.inr r : Gamma.DPath) :=
      hrecord.trans hr
    have hpath : P.path = (.inr r : Gamma.DPath) :=
      hwhole.trans (hparent.trans hrecordRay)
    have hbRay : b ∈ r.support := by
      simpa only [hpath, DirectedPath.Path.support] using hbP
    obtain ⟨n, hn⟩ := hbRay
    have hbefore : GroundingCut.Before P.path b (r (n + 1)) := by
      rw [hpath]
      refine ⟨⟨n, n + 1, hn, rfl, Nat.le_succ n⟩, ?_⟩
      intro hEq
      exact Nat.ne_of_lt (Nat.lt_succ_self n)
        (r.injective (hn.trans hEq))
    have hproxyNotCut :
        (PopularAuxiliary.Input.LambdaVertex.proxy i : J.LV) ∉ S.cut := by
      intro hi
      apply R.auxiliarySource_not_mem_cut
      rw [hsource]
      exact hi
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingSelectedForwardOrder.exists_avoiding_proxy_reverse_to_relaxedEscape
        J S.cut P hfragment (hparent.trans hrecord) hproxyNotCut hbefore E
    exact PopularAuxiliary.Input.no_avoiding_source_target_path
      J.lambda S.cut S.separates q
      (hqStart ▸ J.mem_lambda_source_proxy i) hqTarget hqAvoid

end DeferredCutAvoidingRecord

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_deferredCutAvoidingRecord
