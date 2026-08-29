/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingGroundedRecordTraceReachability
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingRecord

/-!
# Cut avoidance for every source-indexed grounded record

The cut-avoiding-record geometry does not depend on the record being the
distinguished unused record.  It only needs the chosen grounded record,
its inessentiality in the limiting warp, its literal auxiliary-source
representation, and avoidance of the cut by its full source carrier.

This source-indexed form is the one needed while choosing every selected
request path: excluding the nonstationary set of sources whose own carrier
meets the cut makes the selected path's starting limiting component avoid
the whole relevant grounding frontier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder.SplitGroundedAuxiliarySourceRecord

open _root_.Erdos599.DirectedPath
open GroundingGroundedRecordTraceReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
variable {hground : Stationary.IsStationaryBelow kappa L.phiGround}
variable {S : Popular.PopularSeparator
  (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

local notation "J" => L.splitGroundedPopularAuxiliaryInput hL.legal

private theorem edgeSet_disjoint_CE_of_ownCarrier_disjoint
    (xsource : (J).lambda.source)
    (R : L.SplitGroundedAuxiliarySourceRecord hL.legal xsource)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace J R.record ∪ {xsource.1}) S.cut) :
    Disjoint R.record.edgeSet (GroundingCut.CE J S.cut) := by
  apply Set.disjoint_left.mpr
  intro e he hCE
  exact Set.disjoint_left.mp hcarrier
    (Or.inl
      ((PopularSwitching.edge_mem_ladderTrace_iff J R.record e.1 e.2).mpr he))
    hCE.1

private theorem wholeRecord_not_meetsEscape_of_ownCarrier_disjoint
    (xsource : (J).lambda.source)
    (R : L.SplitGroundedAuxiliarySourceRecord hL.legal xsource)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace J R.record ∪ {xsource.1}) S.cut) :
    ¬ (GroundingCut.wholeFragment J R.record R.record_mem_ladder).MeetsEscape
      J S.cut := by
  let F := GroundingCut.wholeFragment J R.record R.record_mem_ladder
  have hF : F ∈ GroundingCut.fragments J S.cut :=
    GroundingCut.wholeFragment_mem_fragments J S.cut R.record
      R.record_mem_ladder
      (edgeSet_disjoint_CE_of_ownCarrier_disjoint xsource R hcarrier)
  have hsourceNotCut : xsource.1 ∉ S.cut := by
    intro hsourceCut
    exact Set.disjoint_left.mp hcarrier
      (Or.inr (Set.mem_singleton xsource.1)) hsourceCut
  rcases R.represents with ⟨p, hrecord, hsource⟩ |
      ⟨i, hrecord, hsource⟩
  · apply L.splitGrounded_wholeFiniteRecord_not_meetsEscape
      hL.legal S.cut S.separates F hF rfl
      ⟨R.stage, R.stage_ground, R.chosen⟩
    · change R.record.terminal? = some p.finish
      simp only [hrecord, Path.terminal?_finite]
    · intro hCV
      apply hsourceNotCut
      rw [hsource]
      exact hCV
  · rintro ⟨b, hbF, ⟨E⟩⟩
    obtain ⟨r, hr⟩ := (J).proxy_isRay i
    have hrecordRay : R.record = (Sum.inr r : Gamma.DPath) :=
      hrecord.trans hr
    have hbRay : b ∈ r.support := by
      change b ∈ R.record.support at hbF
      simpa only [hrecordRay, Path.support] using hbF
    obtain ⟨n, hn⟩ := hbRay
    have hbefore : GroundingCut.Before F.path b (r (n + 1)) := by
      change GroundingCut.Before R.record b (r (n + 1))
      rw [hrecordRay]
      refine ⟨⟨n, n + 1, hn, rfl, Nat.le_succ n⟩, ?_⟩
      intro hEq
      exact Nat.ne_of_lt (Nat.lt_succ_self n)
        (r.injective (hn.trans hEq))
    have hproxyNotCut :
        (PopularAuxiliary.Input.LambdaVertex.proxy i : (J).LV) ∉ S.cut := by
      rw [← hsource]
      exact hsourceNotCut
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingSelectedForwardOrder.exists_avoiding_proxy_reverse_to_relaxedEscape
        J S.cut F hF hrecord hproxyNotCut hbefore E
    exact PopularAuxiliary.Input.no_avoiding_source_target_path
      (J).lambda S.cut S.separates q
      (hqStart ▸ (J).mem_lambda_source_proxy i) hqTarget hqAvoid

private theorem relevantG0_parent_ne_record_of_ownCarrier_disjoint
    (xsource : (J).lambda.source)
    (R : L.SplitGroundedAuxiliarySourceRecord hL.legal xsource)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace J R.record ∪ {xsource.1}) S.cut)
    (P : (J).Fragment) (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut) :
    P.parent ≠ R.record := by
  intro hparent
  have hnoEscape : ¬ P.MeetsEscape J S.cut := by
    rintro ⟨b, hbP, hbEscape⟩
    apply wholeRecord_not_meetsEscape_of_ownCarrier_disjoint
      xsource R hcarrier
    refine ⟨b, ?_, hbEscape⟩
    change b ∈ R.record.support
    rw [← hparent]
    exact P.support_subset hbP
  have hessential :=
    L.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
      hL.legal S.cut P hP hnoEscape
  exact R.limit_inessential.2 (hparent ▸ hessential)

/-- The relevant grounding frontier is disjoint from any source-indexed
grounded record whose full own carrier avoids the popular cut.  No unused
record or reserved-control hypothesis is involved. -/
theorem relevantBB_disjoint_record_of_ownCarrier_disjoint
    (xsource : (J).lambda.source)
    (R : L.SplitGroundedAuxiliarySourceRecord hL.legal xsource)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace J R.record ∪ {xsource.1}) S.cut) :
    Disjoint (L.splitGroundedRelevantBB hL.legal S.cut) R.record.support := by
  apply Set.disjoint_left.mpr
  intro b hb hbR
  rcases hb with hCV | ⟨P, hP, hblock⟩
  · exact Set.disjoint_left.mp hcarrier
      (Or.inl
        ((PopularSwitching.old_mem_ladderTrace_iff J R.record b).mpr hbR))
      hCV
  · have hPBlock :=
      (L.splitGroundedRelevantG0_subset_legacyG0 hL.legal S.cut hP).2
    have hbP : b ∈ P.path.support := hblock ▸
      GroundingCut.blockingPoint_mem_support J S.cut P hPBlock
    have hparent : P.parent = R.record :=
      Alternating.DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint
        P.parent_mem R.record_mem_ladder (P.support_subset hbP) hbR
    exact relevantG0_parent_ne_record_of_ownCarrier_disjoint
      xsource R hcarrier P hP hparent

end DWeb.KappaLadder.SplitGroundedAuxiliarySourceRecord
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedAuxiliarySourceRecord.relevantBB_disjoint_record_of_ownCarrier_disjoint
