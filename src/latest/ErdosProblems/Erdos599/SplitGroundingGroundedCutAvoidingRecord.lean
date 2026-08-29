/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSourceFirst
import ErdosProblems.Erdos599.SplitGroundingGroundedUnused
import ErdosProblems.Erdos599.GroundingSelectedForwardOrder

/-!
# Cut-avoiding records do not meet the relevant grounding frontier

An unused record whose entire auxiliary trace avoids the cut is a whole
surviving fragment.  It has no escape: the finite case is Assertion 8.15,
and in the ray case any escape can be reached from the reserved proxy.
Every relevant fragment on that record would therefore have an essential
parent, contradicting the record's inessentiality.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath

universe u

namespace GroundingCut

variable {V I : Type u} {Gamma : DWeb V}

/-- Regard a whole ladder member as its own fragment. -/
def wholeFragment (J : PopularAuxiliary.Input Gamma I)
    (p : Gamma.DPath) (hp : p ∈ J.ladder.paths) : J.Fragment where
  path := p
  parent := p
  parent_mem := hp
  support_subset := Set.Subset.rfl
  edges_subset := Set.Subset.rfl

/-- If no parent edge is cut, the whole parent is a maximal surviving
fragment. This does not identify arbitrary path representations. -/
theorem wholeFragment_mem_fragments
    (J : PopularAuxiliary.Input Gamma I) (C : Set J.LV)
    (p : Gamma.DPath) (hp : p ∈ J.ladder.paths)
    (hCE : Disjoint p.edgeSet (CE J C)) :
    wholeFragment J p hp ∈ fragments J C := by
  refine ⟨hCE, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hx, ?_⟩
    change SurvivingConnected J C p p.initial x
    by_cases hix : p.initial = x
    · rw [← hix]
      exact GroundingFragmentRelation.survivingConnected_refl J C p
        p.initial_mem_support
    obtain ⟨q, hqStart, hqFinish, hqEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before
        ⟨GroundingFragmentWarp.initial_beforeEq_of_mem hx, hix⟩
    refine ⟨q, Or.inl ⟨hqStart, hqFinish⟩, ?_, hqEdges,
      hCE.mono_left hqEdges⟩
    intro y hy
    by_cases hyFinish : y = q.finish
    · exact (hyFinish.trans hqFinish) ▸ hx
    · obtain ⟨z, hyz⟩ :=
        q.walk.exists_outgoing_edge_of_mem_of_ne_finish hy hyFinish
      exact (p.edgeSet_subset_support_prod (hqEdges hyz)).1
  · exact fun hx ↦ hx.1

end GroundingCut

namespace DWeb.KappaLadder.SplitGroundedUnusedRecord

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
variable {hground : Stationary.IsStationaryBelow kappa L.phiGround}
variable {S : Popular.PopularSeparator
  (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
variable {K : GroundingSelection.Controls S}

local notation "J" => L.splitGroundedPopularAuxiliaryInput hL.legal

/-- A full trace avoiding the cut implies that no represented parent edge
is deleted. -/
theorem edgeSet_disjoint_CE_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut) :
    Disjoint R.record.edgeSet (GroundingCut.CE J S.cut) := by
  apply Set.disjoint_left.mpr
  intro e he hCE
  exact Set.disjoint_left.mp hcut
    ((PopularSwitching.edge_mem_ladderTrace_iff J R.record e.1 e.2).mpr he)
    hCE.1

/-- The whole cut-avoiding reserved record contains no relaxed escape. -/
theorem wholeRecord_not_meetsEscape_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut) :
    ¬ (GroundingCut.wholeFragment J R.record R.limit_inessential.1).MeetsEscape
      J S.cut := by
  let F := GroundingCut.wholeFragment J R.record R.limit_inessential.1
  have hF : F ∈ GroundingCut.fragments J S.cut :=
    GroundingCut.wholeFragment_mem_fragments J S.cut R.record
      R.limit_inessential.1 (R.edgeSet_disjoint_CE_of_trace_disjoint hcut)
  rcases R.source_represents with ⟨p, hrecord, hsource⟩ |
      ⟨i, hrecord, hsource⟩
  · apply L.splitGrounded_wholeFiniteRecord_not_meetsEscape
      hL.legal S.cut S.separates F hF rfl
      ⟨R.stage, R.stage_ground, R.chosen⟩
    · change R.record.terminal? = some p.finish
      simp only [hrecord, Path.terminal?_finite]
    · intro hCV
      apply R.auxiliarySource_not_mem_cut
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
    have hproxyNotCut : (PopularAuxiliary.Input.LambdaVertex.proxy i : (J).LV)
        ∉ S.cut := by
      rw [← hsource]
      exact R.auxiliarySource_not_mem_cut
    obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
      GroundingSelectedForwardOrder.exists_avoiding_proxy_reverse_to_relaxedEscape
        J S.cut F hF hrecord hproxyNotCut hbefore E
    exact PopularAuxiliary.Input.no_avoiding_source_target_path
      (J).lambda S.cut S.separates q
      (hqStart ▸ (J).mem_lambda_source_proxy i) hqTarget hqAvoid

/-- No relevant fragment can have the cut-avoiding reserved parent. -/
theorem relevantG0_parent_ne_record_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut)
    (P : (J).Fragment) (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut) :
    P.parent ≠ R.record := by
  intro hparent
  have hnoEscape : ¬ P.MeetsEscape J S.cut := by
    rintro ⟨b, hbP, hbEscape⟩
    apply R.wholeRecord_not_meetsEscape_of_trace_disjoint hcut
    refine ⟨b, ?_, hbEscape⟩
    change b ∈ R.record.support
    rw [← hparent]
    exact P.support_subset hbP
  have hessential :=
    L.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
      hL.legal S.cut P hP hnoEscape
  exact R.limit_inessential.2 (hparent ▸ hessential)

/-- The entire relevant frontier avoids a reserved record whose auxiliary
carrier avoids the cut. In particular the reserved source is not a blocker. -/
theorem relevantBB_disjoint_record_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut) :
    Disjoint (L.splitGroundedRelevantBB hL.legal S.cut) R.record.support := by
  apply Set.disjoint_left.mpr
  intro b hb hbR
  rcases hb with hCV | ⟨P, hP, hblock⟩
  · exact Set.disjoint_left.mp hcut
      ((PopularSwitching.old_mem_ladderTrace_iff J R.record b).mpr hbR) hCV
  · have hPBlock :=
      (L.splitGroundedRelevantG0_subset_legacyG0 hL.legal S.cut hP).2
    have hbP : b ∈ P.path.support := hblock ▸
      GroundingCut.blockingPoint_mem_support J S.cut P hPBlock
    have hparent : P.parent = R.record :=
      Alternating.DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint
        P.parent_mem R.limit_inessential.1 (P.support_subset hbP) hbR
    exact R.relevantG0_parent_ne_record_of_trace_disjoint hcut P hP hparent

end DWeb.KappaLadder.SplitGroundedUnusedRecord

#print axioms GroundingCut.wholeFragment_mem_fragments
#print axioms DWeb.KappaLadder.SplitGroundedUnusedRecord.relevantBB_disjoint_record_of_trace_disjoint

end Erdos599
