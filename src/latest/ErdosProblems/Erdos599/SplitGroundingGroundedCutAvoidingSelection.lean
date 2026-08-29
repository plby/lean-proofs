/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingGroundedRecordTraceReachability
import ErdosProblems.Erdos599.PopularSourceCarrierCut
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingRecord

/-!
# An actual unused record whose complete trace misses the popular cut

Each auxiliary source owns the disjoint full trace of its recorded ladder
member, augmented by its own proxy if necessary.  Internal reachability of
these carriers turns cut contacts into a disjoint auxiliary warp.  Hence
their indices are nonstationary.  Excluding these and the selected initial
indices reserves a whole cut-avoiding record with no further premise.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.DWeb.KappaLadder

open _root_.Erdos599.DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace SplitGroundedAuxiliarySourceRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitLegal}
variable {source : (L.splitGroundedPopularAuxiliaryInput hL).lambda.source}

/-- An encoded source cannot belong to another ladder component's trace. -/
theorem source_not_mem_other_trace
    (R : L.SplitGroundedAuxiliarySourceRecord hL source)
    {p : Gamma.DPath}
    (hp : p ∈ (L.splitGroundedPopularAuxiliaryInput hL).ladder.paths)
    (hne : R.record ≠ p) :
    source.1 ∉ PopularSwitching.ladderTrace
      (L.splitGroundedPopularAuxiliaryInput hL) p := by
  let J := L.splitGroundedPopularAuxiliaryInput hL
  rcases R.represents with ⟨q, hr, hs⟩ | ⟨i, _hr, hs⟩
  · have hsourceOwn : source.1 ∈ PopularSwitching.ladderTrace J R.record := by
      rw [hs, PopularSwitching.old_mem_ladderTrace_iff, hr]
      exact q.finish_mem_support
    intro hsourceOther
    exact Set.disjoint_left.mp
      (PopularSwitching.ladderTrace_disjoint J R.record_mem_ladder hp hne)
      hsourceOwn hsourceOther
  · rw [hs]
    exact PopularSwitching.proxy_not_mem_ladderTrace J p i

end SplitGroundedAuxiliarySourceRecord

/-- Actual source-indexed disjoint reachable carriers of the grounded
split auxiliary. No selected route or separator enters this definition. -/
noncomputable def splitGroundedSourceCarrierFamily
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    Popular.SourceCarrierFamily (L.splitGroundedPopularAuxiliaryInput hL).lambda := by
  let J := L.splitGroundedPopularAuxiliaryInput hL
  let R := L.splitGroundedAuxiliarySourceRecord hL
  refine {
    carrier := fun x ↦ PopularSwitching.ladderTrace J (R x).record ∪ {x.1}
    disjoint := ?_
    internally_reachable := ?_ }
  · intro x y hxy
    have hrecords : (R x).record ≠ (R y).record := by
      intro heq
      have hchosen : L.chosen (R x).stage = some (R y).record := by
        rw [(R x).chosen, heq]
      have hstages := L.bookkeeping.chosen_stage_unique hL.validBookkeeping
        hchosen (R y).chosen
      exact hxy (L.splitGroundedAuxiliarySourceIndex_injective hL
        ((R x).source_index.trans (hstages.trans (R y).source_index.symm)))
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
  · intro x v hv
    exact (R x).exists_auxiliaryPath_to_mem_ownCarrier hv

/-- Strengthened unused-record selection: its whole auxiliary trace is
disjoint from the cut, not just its own auxiliary source. -/
theorem exists_splitGroundedUnusedRecord_trace_disjoint
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S) :
    ∃ R : L.SplitGroundedUnusedRecord hL hground S K,
      Disjoint (PopularSwitching.ladderTrace
        (L.splitGroundedPopularAuxiliaryInput hL.legal) R.record) S.cut := by
  let J := L.splitGroundedPopularAuxiliaryInput hL.legal
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let selected := GroundingSimultaneousDecode.strongSelectedWarp U S K
  let N := Popular.initialIndicesOf U selected.paths selected.starts_in_source
  obtain ⟨x, hxUnused, hxCut⟩ :=
    (L.splitGroundedSourceCarrierFamily hL.legal).exists_source_disjoint_cut_avoiding
      U S.cut S.not_strongly_popular N
      (GroundingSimultaneousDecode.strongSelectedWarp_initialIndices_nonstationary U S K)
  let R0 := L.splitGroundedAuxiliarySourceRecord hL.legal x
  have hxIndex : U.f x = R0.stage := by
    rw [show U.f = L.splitGroundedAuxiliarySourceIndex hL.legal from
      (L.splitGroundedAuxiliarySourceIndex_eq_sourceIndex hL.legal).symm]
    exact R0.source_index
  have hxCut' : Disjoint
      (PopularSwitching.ladderTrace J R0.record ∪ {x.1}) S.cut := hxCut
  have hxNotCut : x.1 ∉ S.cut := by
    intro hx
    exact Set.disjoint_left.mp hxCut' (Or.inr rfl) hx
  have hgroundRecord : R0.record.initial ∈ Gamma.source := by
    obtain ⟨p, hp, hpSource⟩ := R0.stage_ground
    have hpR : p = R0.record := Option.some.inj (hp.symm.trans R0.chosen)
    exact hpR ▸ hpSource
  let R : L.SplitGroundedUnusedRecord hL hground S K := {
    stage := R0.stage
    stage_ground := R0.stage_ground
    stage_unused := hxIndex ▸ hxUnused
    record := R0.record
    chosen := R0.chosen
    grounded := hgroundRecord
    limit_inessential := R0.limit_inessential
    auxiliarySource := x
    source_index := hxIndex
    auxiliarySource_not_mem_cut := hxNotCut
    source_represents := R0.represents }
  exact ⟨R, hxCut'.mono_left Set.subset_union_left⟩

/-- In particular an actual reserved original source lies outside the
entire relevant separator. -/
theorem exists_splitGroundedUnusedRecord_disjoint_relevantBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S) :
    ∃ R : L.SplitGroundedUnusedRecord hL hground S K,
      Disjoint (PopularSwitching.ladderTrace
        (L.splitGroundedPopularAuxiliaryInput hL.legal) R.record) S.cut ∧
      Disjoint (L.splitGroundedRelevantBB hL.legal S.cut) R.record.support := by
  obtain ⟨R, hcut⟩ := L.exists_splitGroundedUnusedRecord_trace_disjoint hL hground S K
  exact ⟨R, hcut, R.relevantBB_disjoint_record_of_trace_disjoint hcut⟩

#print axioms splitGroundedSourceCarrierFamily
#print axioms exists_splitGroundedUnusedRecord_trace_disjoint
#print axioms exists_splitGroundedUnusedRecord_disjoint_relevantBB

end Erdos599.DWeb.KappaLadder
