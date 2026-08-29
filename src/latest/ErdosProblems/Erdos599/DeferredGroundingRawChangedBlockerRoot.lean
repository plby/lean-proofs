/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawBlockerConfinement
import ErdosProblems.Erdos599.GroundingFinitePerturbationPointRooting

/-!
# Stopped roots for blockers on actually backward-changed fragments

Intrinsic grounding supplies a genuine source prefix to the blocker.
Its incoming active reference incidence is preserved by exact balance
and strict departure order. No-return rooting and blocker confinement
then give an actual source root after source-first separator stopping.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (S : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))

local notation "Lc" => canonicalDeferredLadder Gamma kappa preferred
local notation "J" => popularAuxiliaryInput Lc hL.legal
local notation "D" => reservedStrongSelectedPruningData (L := Lc) (hL := hL) (S := S)

include hkappa huncountable hNoEnter in
/-- Every nonsource vertex of a changed fragment has incoming active reference. -/
theorem canonicalDeferredLadder_rawChangedFragment_activeIncoming
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ GroundingCut.fragments J S.cut)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heP : e ∈ P.path.edgeSet)
    {b : V} (hb : b ∈ P.path.support) (hnotSource : b ∉ Gamma.source) :
    HasIncoming (reservedRawActiveReferenceEdges r) b := by
  have hsource := canonicalDeferredLadder_rawBackwardFragment_grounded
    preferred hkappa huncountable hNoEnter hL S r P hP he heP
  obtain ⟨q, hstart, hfinish, _hsupport, hedges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix P.path hb
  have hqSource : q.start ∈ Gamma.source := hstart ▸ hsource
  have hne : b ≠ q.start := fun h ↦ hnotSource (h.symm ▸ hqSource)
  obtain ⟨z, hz⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    q (hfinish ▸ q.finish_mem_support) hne
  let R : RawActivePrefix r := {
    owner := P.parent
    owner_mem := P.parent_mem
    changedEdge := e
    changed_mem := he
    changed_owner := P.edges_subset heP
    path := q
    source := hqSource
    edges := hedges.trans P.edges_subset
    cut_free := hP.1.mono_left hedges }
  exact ⟨z, R, hz⟩

include hkappa huncountable hNoEnter in
/-- At a relevant blocker, local and active-reference outgoing incidence agree. -/
theorem canonicalDeferredLadder_rawBlocker_outgoing_iff_active
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0) :
    HasOutgoing (reservedRawLocalSourceEdges r) (GroundingCut.blockingPoint J S.cut P) ↔
      HasOutgoing (reservedRawActiveReferenceEdges r) (GroundingCut.blockingPoint J S.cut P) := by
  have hb := GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (canonicalDeferredLadder_rawLocalSource_step_after_blocker
      preferred hkappa huncountable hNoEnter hL S r P hP hb
      (GroundingCut.beforeEq_refl hb) hy).1.1⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Or.inl (Or.inl ⟨hy, ?_⟩)⟩
    intro hback
    exact (canonicalDeferredLadder_rawBackwardTail_before_blocker
      preferred hkappa huncountable hNoEnter hL S r P hP hback hb).2 rfl

include hkappa huncountable hNoEnter in
/-- Exact balance preserves incoming incidence at a nonsource changed blocker. -/
theorem canonicalDeferredLadder_rawChangedBlocker_localIncoming
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heP : e ∈ P.path.edgeSet)
    (hnotSource : GroundingCut.blockingPoint J S.cut P ∉ Gamma.source) :
    HasIncoming (reservedRawLocalSourceEdges r) (GroundingCut.blockingPoint J S.cut P) := by
  classical
  let b := GroundingCut.blockingPoint J S.cut P
  have hb : b ∈ P.path.support := GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
  have hin := canonicalDeferredLadder_rawChangedFragment_activeIncoming
    preferred hkappa huncountable hNoEnter hL S r P hP.1.1.1 he heP hb hnotSource
  have hnotInitial : b ≠ (reservedStrongSelectedStartingRecord r).record.initial := by
    intro h
    exact Set.disjoint_left.1 (reservedRawRelevantFragment_disjoint_startingRecord r P hP)
      hb (h.symm ▸ (reservedStrongSelectedStartingRecord r).record.initial_mem_support)
  have hnotRequest : b ≠ requestVertex r := by
    intro h
    exact reservedRawBackwardOwner_requestVertex_not_mem r P.parent_mem he
      (P.edges_subset heP) (h ▸ P.support_subset hb)
  have hbalance : edgeBalance (reservedRawLocalSourceEdges r) b =
      edgeBalance (reservedRawActiveReferenceEdges r) b := by
    rw [reservedRawLocalSource_balance r
      (canonicalDeferredLadder_rawBackward_subset_activeReference
        preferred hkappa huncountable hNoEnter hL S r)]
    simp only [propInt, if_neg hnotInitial, if_neg hnotRequest, add_zero, sub_zero]
  have hout := canonicalDeferredLadder_rawBlocker_outgoing_iff_active
    preferred hkappa huncountable hNoEnter hL S r P hP
  change HasOutgoing (reservedRawLocalSourceEdges r) b ↔
    HasOutgoing (reservedRawActiveReferenceEdges r) b at hout
  by_contra hnoIn
  change ¬ HasIncoming (reservedRawLocalSourceEdges r) b at hnoIn
  simp only [edgeBalance, propInt, hout, if_neg hnoIn, if_pos hin] at hbalance
  omega

include hkappa huncountable hNoEnter in
/-- Every relevant blocker on a fragment changed backwards by an actual
request is rooted in the exact source-first stopped raw relation. -/
theorem canonicalDeferredLadder_rawChangedBlocker_sourceRooted
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heP : e ∈ P.path.edgeSet) :
    reservedRawSourceRooted (L := Lc) (hL := hL) (S := S)
      (GroundingCut.blockingPoint J S.cut P) := by
  by_cases hbSource : GroundingCut.blockingPoint J S.cut P ∈ Gamma.source
  · exact reservedRawSourceRooted_of_source hbSource
  have hin := canonicalDeferredLadder_rawChangedBlocker_localIncoming
    preferred hkappa huncountable hNoEnter hL S r P hP he heP hbSource
  have hcoverage := canonicalDeferredLadder_rawBackward_subset_activeReference
    preferred hkappa huncountable hNoEnter hL S r
  obtain ⟨a, ha, hreach⟩ := GroundingFinitePerturbationPointRooting.rooted_of_no_return
    (reservedRawLocalSourceEdges r) Gamma.source
    ((reservedRawLocalSource_subset_simultaneous r).trans reservedRawSimultaneousEdges_subset_adj)
    (reservedRawLocalSource_biUnique r) (reservedRawLocalSource_no_reverseRay r)
    (reservedRawLocalSource_positive_source r hcoverage) (Or.inr hin)
    (fun _ he hrest ↦ canonicalDeferredLadder_rawLocalSource_blocker_no_return
      preferred hkappa huncountable hNoEnter hL S r P hP he hrest)
  exact ⟨a, ha, canonicalDeferredLadder_rawLocalBlockerRoute_survives_stopping
    preferred hkappa huncountable hNoEnter hL S r P hP
    reservedStrongSelectedSourceFirstBB_subset_relevantBB hreach⟩

#print axioms canonicalDeferredLadder_rawChangedFragment_activeIncoming
#print axioms canonicalDeferredLadder_rawChangedBlocker_localIncoming
#print axioms canonicalDeferredLadder_rawChangedBlocker_sourceRooted

end Erdos599.DWeb.KappaLadder.Deferred
