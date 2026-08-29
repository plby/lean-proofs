/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawFragmentGrounded
import ErdosProblems.Erdos599.GroundingSurvivingEdgeFragment

/-!
# The source-prefix reference for one actual raw transaction

The reference consists of cut-free source-starting finite paths on owners
actually changed backwards by the request. Its positive boundary is in the
original source. Intrinsic fragment grounding proves that it contains every
actual backward edge. No grounding of discarded cycle vertices is assumed.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

/-- An actual finite, source-starting, cut-free path on a changed owner. -/
structure RawActivePrefix (r : Request J S.cut) where
  owner : Gamma.DPath
  owner_mem : owner ∈ (J).ladder.paths
  changedEdge : V × V
  changed_mem : changedEdge ∈ reservedRawRequestBackwardEdges r
  changed_owner : changedEdge ∈ owner.edgeSet
  path : FinitePath Gamma.graph
  source : path.start ∈ Gamma.source
  edges : path.edgeSet ⊆ owner.edgeSet
  cut_free : Disjoint path.edgeSet (GroundingCut.CE J S.cut)

def reservedRawActiveReferenceEdges (r : Request J S.cut) : Set (V × V) :=
  {e | ∃ P : RawActivePrefix r, e ∈ P.path.edgeSet}

theorem reservedRawActiveReference_subset_reference (r : Request J S.cut) :
    reservedRawActiveReferenceEdges r ⊆ (J).familyEdges := by
  rintro e ⟨P, he⟩
  exact ⟨P.owner, P.owner_mem, P.edges he⟩

theorem reservedRawActiveReference_biUnique (r : Request J S.cut) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ reservedRawActiveReferenceEdges r) :=
  ⟨fun _ _ _ he hf ↦ (J).raw_familyEdges_biUnique.1
      (reservedRawActiveReference_subset_reference r he)
      (reservedRawActiveReference_subset_reference r hf),
    fun _ _ _ he hf ↦ (J).raw_familyEdges_biUnique.2
      (reservedRawActiveReference_subset_reference r he)
      (reservedRawActiveReference_subset_reference r hf)⟩

theorem reservedRawActiveReference_positive_source (r : Request J S.cut)
    (x : V) (hx : edgeBalance (reservedRawActiveReferenceEdges r) x = 1) :
    x ∈ Gamma.source := by
  obtain ⟨⟨y, P, hxy⟩, hno⟩ := edgeBalance_eq_one_iff.mp hx
  by_cases hs : x = P.path.start
  · exact hs ▸ P.source
  obtain ⟨z, hz⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    P.path (P.path.edgeSet_subset_support_prod hxy).1 hs
  exact (hno ⟨z, P, hz⟩).elim

/-- All active reference edges not deleted by this request survive the
actual simultaneous switch; another request cannot delete them. -/
theorem reservedRawActiveReference_retained (r : Request J S.cut) :
    reservedRawActiveReferenceEdges r \ reservedRawRequestBackwardEdges r ⊆
      reservedRawRetainedEdges (L := L) (hL := hL) (S := S) := by
  rintro e ⟨⟨P, he⟩, hnot⟩
  exact (reservedRawRetained_on_backwardOwner_iff r P.owner_mem
    P.changed_mem P.changed_owner (P.edges he)).2
    ⟨fun hcut ↦ Set.disjoint_left.1 P.cut_free he hcut, hnot⟩

/-- The original endpoint of a request on an owner also puts its auxiliary
apex on that owner. The edge-request case uses incoming-owner uniqueness. -/
theorem requestAuxVertex_mem_trace_of_requestVertex_mem_owner
    (r : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    (hmem : requestVertex r ∈ Y.support) :
    requestAuxVertex r ∈ PopularSwitching.ladderTrace J Y := by
  cases r with
  | inl z => exact (PopularSwitching.old_mem_ladderTrace_iff J Y z.1).2 hmem
  | inr e =>
      exact (PopularSwitching.edge_mem_ladderTrace_iff J Y e.1.1 e.1.2).2
        ((J).referenceEdge_mem_owner_of_head hY (edgeRequest_mem_familyEdges S e) hmem)

theorem reservedRawBackwardOwner_requestVertex_not_mem
    (r : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet) :
    requestVertex r ∉ Y.support := by
  intro hmem
  exact reservedRawBackwardOwner_apex_not_mem r hY he heY
    (requestAuxVertex_mem_trace_of_requestVertex_mem_owner r hY hmem)

theorem reservedRawRequestVertex_not_mem_startingRecord (r : Request J S.cut) :
    requestVertex r ∉ (reservedStrongSelectedStartingRecord r).record.support := by
  intro hmem
  have htrace := requestAuxVertex_mem_trace_of_requestVertex_mem_owner r
    (reservedStrongSelectedStartingRecord r).record_mem_ladder hmem
  exact Set.disjoint_left.1
    ((reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut r).mono_left
      Set.subset_union_left) htrace (requestAuxVertex_mem_cut r)

theorem reservedRawActiveReference_not_incident_request (r : Request J S.cut)
    {e : V × V} (he : e ∈ reservedRawActiveReferenceEdges r) :
    e.1 ≠ requestVertex r ∧ e.2 ≠ requestVertex r := by
  obtain ⟨P, he⟩ := he
  have hnot := reservedRawBackwardOwner_requestVertex_not_mem r P.owner_mem
    P.changed_mem P.changed_owner
  have hends := P.owner.edgeSet_subset_support_prod (P.edges he)
  exact ⟨fun h ↦ hnot (h ▸ hends.1), fun h ↦ hnot (h ▸ hends.2)⟩

theorem reservedRawActiveReference_balance_request (r : Request J S.cut) :
    edgeBalance (reservedRawActiveReferenceEdges r) (requestVertex r) = 0 := by
  have hin : ¬ HasIncoming (reservedRawActiveReferenceEdges r) (requestVertex r) := by
    rintro ⟨x, hx⟩
    exact (reservedRawActiveReference_not_incident_request r hx).2 rfl
  have hout : ¬ HasOutgoing (reservedRawActiveReferenceEdges r) (requestVertex r) := by
    rintro ⟨x, hx⟩
    exact (reservedRawActiveReference_not_incident_request r hx).1 rfl
  simp only [edgeBalance, propInt, if_neg hin, if_neg hout, sub_self]

theorem reservedRawActiveReference_disjoint_prefix (r : Request J S.cut) :
    Disjoint (reservedRawActiveReferenceEdges r)
      (reservedRawOwnerAttachment r).sourcePrefix.edgeSet := by
  apply Set.disjoint_left.2
  rintro e ⟨P, heP⟩ heH
  have hsame : P.owner = (reservedStrongSelectedStartingRecord r).record :=
    DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint P.owner_mem
      (reservedStrongSelectedStartingRecord r).record_mem_ladder
      (P.owner.edgeSet_subset_support_prod (P.edges heP)).1
      (((reservedStrongSelectedStartingRecord r).record).edgeSet_subset_support_prod
        ((reservedRawOwnerAttachment r).sourcePrefix_edges heH)).1
  exact reservedRawRequestBackward_owner_ne_startingRecord r r P.owner_mem
    P.changed_mem P.changed_owner hsame

/-- Every actual backward edge has a genuine source-starting cut-free
prefix on its owner. This instantiates intrinsic fragment grounding. -/
theorem canonicalDeferredLadder_rawBackward_subset_activeReference
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut) :
    reservedRawRequestBackwardEdges r ⊆ reservedRawActiveReferenceEdges r := by
  intro e he
  let Jc := popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal
  have href := reservedRawRequestBackward_subset_cut_reference r he
  obtain ⟨P, hP, heP⟩ := GroundingSurvivingEdgeFragment.exists_fragment_containing_edge
    Jc href.1.1 href.2
  have hsource := canonicalDeferredLadder_rawBackwardFragment_grounded
    preferred hkappa huncountable hNoEnter hL S r P hP he heP
  obtain ⟨q, hstart, hfinish, _hsupport, hedges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix P.path
      (P.path.edgeSet_subset_support_prod heP).2
  have hqSource : q.start ∈ Gamma.source := hstart ▸ hsource
  have hne : e.2 ≠ q.start :=
    fun h ↦ hNoEnter (P.path.edgeSet_subset_adj heP) (h ▸ hqSource)
  obtain ⟨z, hz⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    q (hfinish ▸ q.finish_mem_support) hne
  have hze : z = e.1 := Jc.raw_familyEdges_biUnique.1
    ⟨P.parent, P.parent_mem, P.edges_subset (hedges hz)⟩ href.1.1
  let Q : RawActivePrefix r := {
    owner := P.parent
    owner_mem := P.parent_mem
    changedEdge := e
    changed_mem := he
    changed_owner := P.edges_subset heP
    path := q
    source := hqSource
    edges := hedges.trans P.edges_subset
    cut_free := hP.1.mono_left hedges }
  refine ⟨Q, ?_⟩
  change (e.1, e.2) ∈ q.edgeSet
  simpa only [hze] using hz

#print axioms reservedRawActiveReference_positive_source
#print axioms reservedRawActiveReference_retained
#print axioms canonicalDeferredLadder_rawBackward_subset_activeReference

end Erdos599.DWeb.KappaLadder.Deferred
