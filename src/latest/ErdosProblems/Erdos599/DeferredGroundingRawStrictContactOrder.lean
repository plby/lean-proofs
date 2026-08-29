/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawForwardCutGeometry
import ErdosProblems.Erdos599.GroundingSelectedEscapeExclusion

/-!
# Strict departure order at escaping relevant blockers

Actual backward tails cannot start relaxed escapes. The same holds for
forward departures on relevant fragments: the attachment is excluded by
record separation and the remaining old/edge ports use escape exclusion.
Consequently equality at an escaping blocking point is impossible.
Non-escaping terminal blockers remain a separate case.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

/-- A real backward tail cannot itself be an escaping point. -/
theorem reservedRawBackwardTail_not_mem_escapeRegion
    (r : Request J S.cut) {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) :
    e.1 ∉ (J).escapeRegion S.cut := by
  have hgate := reservedRawRequestBackward_gadget r he
  exact GroundingSelectedEscapeExclusion.edgeTail_not_mem_escapeRegion U S K r
    (reservedRawRequestBackward_subset_cut_reference r he).1.1 hgate.1
    (fun h ↦ hgate.2 (h.symm ▸ requestAuxVertex_mem_cut r))

/-- A real forward departure on a relevant fragment cannot be escaping. -/
theorem reservedRawForwardTail_not_mem_escapeRegion_on_relevantFragment
    (r : Request J S.cut) (P : (J).Fragment)
    (hP : P ∈ (reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S)).relevantG0)
    {x y : V} (he : (x, y) ∈ (reservedRawOwnerAttachment r).forwardEdges)
    (hxP : x ∈ P.path.support) : x ∉ (J).escapeRegion S.cut := by
  intro hescape
  let A := reservedRawOwnerAttachment r
  rcases he with hfirst | htail
  · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.mp hfirst)
    exact Set.disjoint_left.1 (reservedRawRelevantFragment_disjoint_startingRecord r P hP)
      hxP (hx ▸ A.anchor_mem_owner)
  · obtain ⟨⟨a, b, hab, hchoice⟩, hproper⟩ := htail
    have hc := (J).chosenConnector?_eq_some hchoice
    have haTail := (A.tail.edgeSet_subset_support_prod hab).1
    have haNotApex : a ≠ requestAuxVertex r := by
      intro h
      exact (FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U S K r) (A.tail_edges_subset hab))
        (h.trans (strongSelectedPath_finish U S K r).symm)
    rcases hc.1 with hexit | ⟨i, hai, _hxi⟩
    · cases a with
      | old z =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          have hsource := GroundingSelectedEscapeExclusion.forwardSource_of_old_connector
            J (A.tail.edgeSet_subset_adj hab) ((J).chosenConnector?_eq_some hchoice) hproper
          exact GroundingSelectedEscapeExclusion.oldForward_not_mem_escapeRegion U S K r
            hsource (A.tail_support_subset haTail) haNotApex hescape
      | edge z w =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          have hfamily : (x, w) ∈ (J).familyEdges :=
            (J).edgeNode_mem_familyEdges_of_start_in_source
              (strongSelectedPath U S K r)
              ((strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩)
              (A.tail_support_subset haTail)
          exact GroundingSelectedEscapeExclusion.edgeTail_not_mem_escapeRegion U S K r
            hfamily (A.tail_support_subset haTail) haNotApex hescape
      | proxy i => simp at hexit
    · subst a
      exact A.tail_no_proxy i haTail

section Canonical

variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hLc : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (Sc : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hLc))

local notation "Lc" => canonicalDeferredLadder Gamma kappa preferred
local notation "Jc" => popularAuxiliaryInput Lc hLc.legal
local notation "Dc" => reservedStrongSelectedPruningData (L := Lc) (hL := hLc) (S := Sc)

include hkappa huncountable hNoEnter in
/-- On an escaping relevant fragment the backward departure is strictly
before the blocking point. -/
theorem canonicalDeferredLadder_rawBackwardTail_before_escapingBlocker
    (r : Request Jc Sc.cut) (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hescape : Fragment.MeetsEscape Jc Sc.cut P)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r)
    (hxP : e.1 ∈ P.path.support) :
    GroundingCut.Before P.path e.1 (GroundingCut.blockingPoint Jc Sc.cut P) := by
  refine ⟨canonicalDeferredLadder_rawBackwardTail_beforeEq_blockingPoint
    preferred hkappa huncountable hNoEnter hLc Sc r P hP he hxP, ?_⟩
  intro heq
  apply reservedRawBackwardTail_not_mem_escapeRegion r he
  rw [heq]
  exact GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape Jc Sc.cut P hescape

include hkappa huncountable hNoEnter in
/-- All actual global forward departures on an escaping relevant fragment
are strictly before its blocking point. -/
theorem canonicalDeferredLadder_rawGlobalForwardTail_before_escapingBlocker
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hescape : Fragment.MeetsEscape Jc Sc.cut P)
    {x y : V} (he : (x, y) ∈ reservedRawForwardEdges (L := Lc) (hL := hLc) (S := Sc))
    (hxP : x ∈ P.path.support) :
    GroundingCut.Before P.path x (GroundingCut.blockingPoint Jc Sc.cut P) := by
  refine ⟨canonicalDeferredLadder_rawGlobalForwardTail_beforeEq_blockingPoint
    preferred hkappa huncountable hNoEnter hLc Sc P hP he hxP, ?_⟩
  intro heq
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp he
  apply reservedRawForwardTail_not_mem_escapeRegion_on_relevantFragment r P hP hr hxP
  rw [heq]
  exact GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape Jc Sc.cut P hescape

end Canonical

#print axioms reservedRawBackwardTail_not_mem_escapeRegion
#print axioms reservedRawForwardTail_not_mem_escapeRegion_on_relevantFragment
#print axioms canonicalDeferredLadder_rawBackwardTail_before_escapingBlocker
#print axioms canonicalDeferredLadder_rawGlobalForwardTail_before_escapingBlocker

end Erdos599.DWeb.KappaLadder.Deferred
