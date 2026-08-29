/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingGroundedCarrierControls
import ErdosProblems.Erdos599.DeferredGroundingAssertion818Decoder
import ErdosProblems.Erdos599.GroundingInputRelevantPruning
import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingFragmentUniqueness
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingSelectedForwardOrder

/-!
# Relevant pruning for all deferred selected starting records

Every selected starting record supplied by the grounded-carrier controls is
inessential in the limiting ladder and its full auxiliary carrier misses the
popular cut.  They can therefore all be put into the input-level discarded
family.  The resulting relevant boundary is disjoint from every discarded
starting record.

No assertion is made about a different equal-origin hanging component met
later by a selected route.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

namespace DeferredAuxiliarySourceRecord

/-- Full carrier avoidance implies that no edge of the represented record is
deleted by the auxiliary cut. -/
private theorem edgeSet_disjoint_CE_of_ownCarrier_disjoint
    (x : (J).lambda.source)
    (R : DeferredAuxiliarySourceRecord L hL.legal x)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace J R.record ∪ {x.1}) S.cut) :
    Disjoint R.record.edgeSet (GroundingCut.CE J S.cut) := by
  apply Set.disjoint_left.mpr
  intro e he hCE
  exact Set.disjoint_left.mp hcarrier
    (Or.inl
      ((PopularSwitching.edge_mem_ladderTrace_iff J R.record e.1 e.2).mpr he))
    hCE.1

/-- A whole deferred source record whose carrier avoids the cut cannot meet
the relaxed escape region. -/
theorem wholeRecord_not_meetsEscape_of_ownCarrier_disjoint
    (x : (J).lambda.source)
    (R : DeferredAuxiliarySourceRecord L hL.legal x)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace J R.record ∪ {x.1}) S.cut)
    (P : (J).Fragment)
    (hfragment : P ∈ GroundingCut.fragments J S.cut)
    (hparent : P.parent = R.record)
    (hwhole : P.path = P.parent) :
    ¬ P.MeetsEscape J S.cut := by
  rintro ⟨b, hbP, ⟨E⟩⟩
  have hxNotCut : x.1 ∉ S.cut := by
    intro hx
    exact Set.disjoint_left.mp hcarrier (Or.inr rfl) hx
  rcases R.represents with ⟨p, hrecord, hsource⟩ |
      ⟨i, hrecord, hsource⟩
  · have hpath : P.path = (.inl p : Gamma.DPath) :=
      hwhole.trans (hparent.trans hrecord)
    have hbFinite : b ∈ p.support := by
      simpa only [hpath, DirectedPath.Path.support] using hbP
    have htSource : p.finish ∈ (J).finiteSource := by
      apply ((J).mem_lambda_source_old p.finish).1
      rw [← hsource]
      exact x.2
    have htNotCut :
        (PopularAuxiliary.Input.LambdaVertex.old p.finish : (J).LV) ∉ S.cut := by
      intro ht
      apply hxNotCut
      rw [hsource]
      exact ht
    have hbeforeEq : GroundingCut.BeforeEq P.path b p.finish := by
      rw [hpath]
      exact GroundingCut.beforeEq_terminal rfl hbFinite
    have hroute : ∃ q : FinitePath (J).lambda.graph,
        q.start = .old p.finish ∧ q.finish ∈ (J).lambda.target ∧
          (J).lambda.Avoids q S.cut := by
      by_cases hEq : b = p.finish
      · subst b
        exact GroundingRelaxedCorridor.exists_ordinaryEscape_of_relaxed_of_start_mem
          J S.cut (Or.inr htSource) E
      · exact GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
          J S.cut P hfragment ⟨hbeforeEq, hEq⟩ htNotCut E
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ := hroute
    exact PopularAuxiliary.Input.no_avoiding_source_target_path
      (J).lambda S.cut S.separates q
      (hqStart ▸ ((J).mem_lambda_source_old p.finish).2 htSource)
      hqTarget hqAvoid
  · obtain ⟨r, hr⟩ := (J).proxy_isRay i
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
        (PopularAuxiliary.Input.LambdaVertex.proxy i : (J).LV) ∉ S.cut := by
      rw [← hsource]
      exact hxNotCut
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingSelectedForwardOrder.exists_avoiding_proxy_reverse_to_relaxedEscape
        J S.cut P hfragment (hparent.trans hrecord) hproxyNotCut hbefore E
    exact PopularAuxiliary.Input.no_avoiding_source_target_path
      (J).lambda S.cut S.separates q
      (hqStart ▸ (J).mem_lambda_source_proxy i) hqTarget hqAvoid

end DeferredAuxiliarySourceRecord

/-! ## A generic family of deferred starting records -/

variable {A : Type u}
variable (x : A → (popularAuxiliaryInput L hL.legal).lambda.source)
variable (R : ∀ a, DeferredAuxiliarySourceRecord L hL.legal (x a))
variable (hcarrier : ∀ a, Disjoint
  (PopularSwitching.ladderTrace (popularAuxiliaryInput L hL.legal)
    (R a).record ∪ {(x a).1}) S.cut)

/-- The input-level pruning data discarding every member of a selected
starting-record family. -/
def sourceRecordPruningData :
    GroundingInputRelevantPruning.Data J S.cut where
  discarded := Set.range fun a ↦ (R a).record
  discarded_not_essential := by
    rintro p ⟨a, rfl⟩ hpEssential
    exact (R a).limit_inessential.2 hpEssential
  whole_discarded_not_meetsEscape := by
    intro P hfragment hwhole hdiscarded
    obtain ⟨a, hparent⟩ := hdiscarded
    exact (R a).wholeRecord_not_meetsEscape_of_ownCarrier_disjoint
      (x a) (hcarrier a) P hfragment hparent.symm hwhole

/-- Every two vertices of a parent remain connected when no parent edge is
deleted. -/
private theorem survivingConnected_parent_of_edgeSet_disjoint
    (parent : Gamma.DPath)
    (hCE : Disjoint parent.edgeSet (GroundingCut.CE J S.cut))
    {a b : V} (ha : a ∈ parent.support) (hb : b ∈ parent.support) :
    GroundingCut.SurvivingConnected J S.cut parent a b := by
  by_cases hab : a = b
  · subst b
    exact GroundingFragmentRelation.survivingConnected_refl
      J S.cut parent ha
  rcases GroundingCut.beforeEq_total ha hb with hbefore | hbefore
  · obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before ⟨hbefore, hab⟩
    refine ⟨p, Or.inl ⟨hpStart, hpFinish⟩, ?_, hpEdges,
      hCE.mono_left hpEdges⟩
    intro z hz
    by_cases hzFinish : z = p.finish
    · simpa only [hzFinish, hpFinish] using hb
    · obtain ⟨w, hzw⟩ :=
        p.walk.exists_outgoing_edge_of_mem_of_ne_finish hz hzFinish
      exact (parent.edgeSet_subset_support_prod (hpEdges hzw)).1
  · have hba : b ≠ a := fun h ↦ hab h.symm
    obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before ⟨hbefore, hba⟩
    refine ⟨p, Or.inr ⟨hpStart, hpFinish⟩, ?_, hpEdges,
      hCE.mono_left hpEdges⟩
    intro z hz
    by_cases hzFinish : z = p.finish
    · simpa only [hzFinish, hpFinish] using ha
    · obtain ⟨w, hzw⟩ :=
        p.walk.exists_outgoing_edge_of_mem_of_ne_finish hz hzFinish
      exact (parent.edgeSet_subset_support_prod (hpEdges hzw)).1

private theorem fragment_support_eq_parent_of_edgeSet_disjoint
    {P : (J).Fragment} (hP : P ∈ GroundingCut.fragments J S.cut)
    (hCE : Disjoint P.parent.edgeSet (GroundingCut.CE J S.cut)) :
    P.path.support = P.parent.support := by
  apply Set.Subset.antisymm P.support_subset
  intro z hz
  rw [hP.2]
  exact ⟨hz, survivingConnected_parent_of_edgeSet_disjoint
    P.parent hCE (P.support_subset P.path.initial_mem_support) hz⟩

/-- A maximal deleted fragment of an uncut parent is literally the whole
parent path. -/
private theorem fragment_path_eq_parent_of_edgeSet_disjoint
    {P : (J).Fragment} (hP : P ∈ GroundingCut.fragments J S.cut)
    (hCE : Disjoint P.parent.edgeSet (GroundingCut.CE J S.cut)) :
    P.path = P.parent := by
  classical
  have hsupport : P.path.support = P.parent.support :=
    fragment_support_eq_parent_of_edgeSet_disjoint hP hCE
  have hinitial : P.path.initial = P.parent.initial := by
    have hforward : GroundingCut.BeforeEq P.parent P.parent.initial
        P.path.initial :=
      GroundingFragmentWarp.initial_beforeEq_of_mem
        (P.support_subset P.path.initial_mem_support)
    have hbackPath : GroundingCut.BeforeEq P.path P.path.initial
        P.parent.initial :=
      GroundingFragmentWarp.initial_beforeEq_of_mem
        (hsupport.symm.subset P.parent.initial_mem_support)
    have hback : GroundingCut.BeforeEq P.parent P.path.initial
        P.parent.initial :=
      GroundingFragmentUniqueness.beforeEq_parent P hbackPath
    exact GroundingCutDecoder.beforeEq_antisymm hback hforward
  cases hParent : P.parent with
  | inl p =>
      cases hPath : P.path with
      | inl q =>
          have hsub : q.IsSubpathOf (.inl p : Gamma.DPath) := by
            constructor
            · simpa only [hPath, hParent, Path.support] using P.support_subset
            · simpa only [hPath, hParent, Path.edgeSet] using P.edges_subset
          have hqStart : q.start = p.start := by
            simpa only [hPath, hParent, Path.initial] using hinitial
          have hfinishPath : GroundingCut.BeforeEq P.path p.finish q.finish :=
            GroundingCut.beforeEq_terminal (by simp [hPath]) (by
              have hpParent : p.finish ∈ P.parent.support := by
                simpa only [hParent, Path.support] using p.finish_mem_support
              have hpPath : p.finish ∈ P.path.support :=
                hsupport.symm.subset hpParent
              simpa only [hPath, Path.support] using hpPath)
          have hfinishParent : GroundingCut.BeforeEq P.parent p.finish q.finish :=
            GroundingFragmentUniqueness.beforeEq_parent P hfinishPath
          have hreverseParent : GroundingCut.BeforeEq P.parent q.finish p.finish :=
            GroundingCut.beforeEq_terminal (by simp [hParent]) (by
              have hqPath : q.finish ∈ P.path.support := by
                simpa only [hPath, Path.support] using q.finish_mem_support
              have hqParent : q.finish ∈ P.parent.support :=
                P.support_subset hqPath
              simpa only [hParent, Path.support] using hqParent)
          have hqFinish : q.finish = p.finish :=
            GroundingCutDecoder.beforeEq_antisymm
              hreverseParent hfinishParent
          have hedge : q.edgeSet = p.edgeSet := by
            rw [Alternating.FinitePath.edgeSet_eq_position_interval p q hsub]
            ext e
            simp only [Set.mem_ofPred_eq]
            constructor
            · exact fun he ↦ he.1
            · intro he
              have hep := he
              change e ∈ p.walk.edgeSet at hep
              rw [Alternating.Walk.mem_edgeSet_iff_exists_getVert p.walk] at hep
              rcases hep with ⟨i, hi, hi', heq⟩
              have hstartIdx : p.walk.support.idxOf p.start = 0 := by
                calc
                  p.walk.support.idxOf p.start =
                      p.walk.support.idxOf
                        (p.walk.support[0]'p.support_length_pos) := by
                    rw [p.support_getElem_zero]
                  _ = 0 := by rw [p.isPath.idxOf_getElem]
              have hfinishGet :
                  p.walk.support[p.walk.length]'(by
                    rw [Alternating.Walk.support_length_eq]
                    omega) = p.finish :=
                Alternating.Walk.getElem_length_eq_end p.walk
              have hfinishIdx :
                  p.walk.support.idxOf p.finish = p.walk.length := by
                calc
                  p.walk.support.idxOf p.finish =
                      p.walk.support.idxOf
                        (p.walk.support[p.walk.length]'(by
                          rw [Alternating.Walk.support_length_eq]
                          omega)) := by rw [hfinishGet]
                  _ = p.walk.length := by rw [p.isPath.idxOf_getElem]
              have hiIdx : p.walk.support.idxOf
                  (p.walk.support[i]'(by omega)) = i := by
                rw [p.isPath.idxOf_getElem]
              refine ⟨he, ?_, ?_⟩
              · rw [heq]
                simpa only [hqStart, Prod.fst, hstartIdx, hiIdx] using
                  (Nat.zero_le i)
              · rw [heq]
                simpa only [hqFinish, Prod.fst, hfinishIdx, hiIdx] using hi
          exact congrArg Sum.inl
            (FinitePath.eq_of_start_finish_edgeSet_eq
              q p hqStart hqFinish hedge)
      | inr q =>
          exfalso
          have hqsub : q.support ⊆ p.support := by
            simpa only [hPath, hParent, Path.support] using P.support_subset
          exact (Set.infinite_range_of_injective q.injective)
            (p.support_finite.subset hqsub)
  | inr p =>
      cases hPath : P.path with
      | inl q =>
          exfalso
          have hpfinite : p.support.Finite := by
            rw [← show q.support = p.support by
              simpa only [hPath, hParent, Path.support] using hsupport]
            exact q.support_finite
          exact (Set.infinite_range_of_injective p.injective) hpfinite
      | inr q =>
          have hqInitial : q.initial = p.initial := by
            simpa only [hPath, hParent, Path.initial] using hinitial
          have hqEdges : q.edgeSet ⊆ p.edgeSet := by
            simpa only [hPath, hParent, Path.edgeSet] using P.edges_subset
          have hedge : q.edgeSet = p.edgeSet := by
            apply Set.Subset.antisymm hqEdges
            rintro e ⟨n, rfl⟩
            have hpn : p n ∈ q.support := by
              rw [show q.support = p.support by
                simpa only [hPath, hParent, Path.support] using hsupport]
              exact p.apply_mem_support n
            obtain ⟨m, hm⟩ := hpn
            have hqEdge : (q m, q (m + 1)) ∈ p.edgeSet :=
              hqEdges ⟨m, rfl⟩
            have hqEdge' : (p n, q (m + 1)) ∈ p.edgeSet := by
              simpa only [hm] using hqEdge
            have hnext : p (n + 1) = q (m + 1) :=
              (Alternating.Path.edgeSet_biUnique (.inr p : Gamma.DPath)).2
                ⟨n, rfl⟩ hqEdge'
            exact ⟨m, Prod.ext hm.symm hnext⟩
          exact congrArg Sum.inr
            (Ray.eq_of_initial_edgeSet_eq q p hqInitial hedge)

/-- The relevant boundary produced by discarding a cut-avoiding source-record
family is disjoint from every record in that family. -/
theorem sourceRecord_disjoint_relevantBB (a : A) :
    Disjoint (sourceRecordPruningData x R hcarrier).relevantBB
      (R a).record.support := by
  apply Set.disjoint_left.mpr
  intro b hbBB hbRecord
  rcases hbBB with hbCV | ⟨P, hP, hblock⟩
  · exact Set.disjoint_left.mp (hcarrier a)
      (Or.inl
        ((PopularSwitching.old_mem_ladderTrace_iff J (R a).record b).mpr
          hbRecord))
      hbCV
  · have hbP : b ∈ P.path.support := hblock ▸
      GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
    have hparent : P.parent = (R a).record :=
      Alternating.DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint
        P.parent_mem (R a).record_mem_ladder
        (P.support_subset hbP) hbRecord
    have hCERecord : Disjoint (R a).record.edgeSet
        (GroundingCut.CE J S.cut) :=
      (R a).edgeSet_disjoint_CE_of_ownCarrier_disjoint
        (x a) (hcarrier a)
    have hwhole : P.path = P.parent :=
      fragment_path_eq_parent_of_edgeSet_disjoint hP.1.1.1
        (hparent ▸ hCERecord)
    exact hP.1.1.2 ⟨hP.1.1.1, hwhole, ⟨a, hparent.symm⟩⟩

/-! ## Ordinary and strong canonical selected families -/

def selectedStartingPruningData :
    GroundingInputRelevantPruning.Data J S.cut :=
  sourceRecordPruningData
    (fun r : Request J S.cut ↦ selectedSource r)
    (fun r ↦ selectedStartingRecord r)
    (fun r ↦ selectedStartingRecord_ownCarrier_disjoint_cut r)

def selectedStartingRelevantBB : Set V :=
  (selectedStartingPruningData (L := L) (hL := hL) (S := S)).relevantBB

theorem selectedStartingRecord_disjoint_relevantBB
    (r : Request J S.cut) :
    Disjoint (selectedStartingRelevantBB (L := L) (hL := hL) (S := S))
      (selectedStartingRecord r).record.support :=
  sourceRecord_disjoint_relevantBB
    (fun r : Request J S.cut ↦ selectedSource r)
    (fun r ↦ selectedStartingRecord r)
    (fun r ↦ selectedStartingRecord_ownCarrier_disjoint_cut r) r

/-- Assertion 8.18 descent for the exact ordinary-selected starting-record
boundary. -/
theorem selectedStartingRelevantFiniteDescentDecoder :
    GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder
      (selectedStartingPruningData (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantFiniteDescentDecoder
    (selectedStartingPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

theorem selectedStartingRelevantBB_isSeparator :
    Popular.IsSeparator Gamma
      (selectedStartingRelevantBB (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantBB_isSeparator
    (selectedStartingPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

def strongSelectedStartingPruningData :
    GroundingInputRelevantPruning.Data J S.cut :=
  sourceRecordPruningData
    (fun r : Request J S.cut ↦ strongSelectedSource r)
    (fun r ↦ strongSelectedStartingRecord r)
    (fun r ↦ strongSelectedStartingRecord_ownCarrier_disjoint_cut r)

def strongSelectedStartingRelevantBB : Set V :=
  (strongSelectedStartingPruningData
    (L := L) (hL := hL) (S := S)).relevantBB

theorem strongSelectedStartingRecord_disjoint_relevantBB
    (r : Request J S.cut) :
    Disjoint
      (strongSelectedStartingRelevantBB (L := L) (hL := hL) (S := S))
      (strongSelectedStartingRecord r).record.support :=
  sourceRecord_disjoint_relevantBB
    (fun r : Request J S.cut ↦ strongSelectedSource r)
    (fun r ↦ strongSelectedStartingRecord r)
    (fun r ↦ strongSelectedStartingRecord_ownCarrier_disjoint_cut r) r

/-- Assertion 8.18 descent for the exact strong-selected starting-record
boundary. -/
theorem strongSelectedStartingRelevantFiniteDescentDecoder :
    GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder
      (strongSelectedStartingPruningData
        (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantFiniteDescentDecoder
    (strongSelectedStartingPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

theorem strongSelectedStartingRelevantBB_isSeparator :
    Popular.IsSeparator Gamma
      (strongSelectedStartingRelevantBB (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantBB_isSeparator
    (strongSelectedStartingPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.sourceRecordPruningData
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.strongSelectedStartingRecord_disjoint_relevantBB
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.strongSelectedStartingRelevantBB_isSeparator
