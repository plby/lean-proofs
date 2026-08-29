/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawOldCutGeometry

/-!
# Actual inserted departures avoid the old-vertex cut

An old departure gadget is excluded by cut normalization. An edge departure
gadget belongs to the actual backward set, whose tail is already proved
outside the old cut. The initial attachment and restored prefix are on the
cut-free starting record. No erased/raw relation identification is used.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Cut normalization at every nonfinal gadget of the actual selected path. -/
theorem reservedStrongSelected_offApex_not_mem_cut
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    (r : Request (popularAuxiliaryInput L hL.legal) S.cut)
    {a : (popularAuxiliaryInput L hL.legal).LV}
    (ha : a ∈ (strongSelectedPath (popularAuxiliaryIndexed L hL) S
      (reservedGroundedCarrierControls L hL S) r).support)
    (hne : a ≠ requestAuxVertex r) : a ∉ S.cut := by
  intro hcut
  exact hne (Set.mem_singleton_iff.mp
    (GroundingAssembly.normalizedRequestFan_cut_normalized S
      (reservedGroundedCarrierControls L hL S) r
      (strongSelectedPath_mem_controlledRequestFan (popularAuxiliaryIndexed L hL) S
        (reservedGroundedCarrierControls L hL S) r).1 ⟨ha, hcut⟩))

variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (S : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))

local notation "Lc" => canonicalDeferredLadder Gamma kappa preferred
local notation "J" => popularAuxiliaryInput Lc hL.legal
local notation "U" => popularAuxiliaryIndexed Lc hL
local notation "K" => reservedGroundedCarrierControls Lc hL S

include hkappa huncountable hNoEnter in
/-- Every actual inserted forward edge has its tail outside the old cut. -/
theorem canonicalDeferredLadder_rawForwardTail_not_mem_CV
    (r : Request J S.cut) {x y : V}
    (he : (x, y) ∈ (reservedRawOwnerAttachment r).forwardEdges) :
    x ∉ GroundingCut.CV J S.cut := by
  intro hxC
  let A := reservedRawOwnerAttachment r
  rcases he with hfirst | htail
  · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.mp hfirst)
    have hxOwner : x ∈ (reservedStrongSelectedStartingRecord r).record.support :=
      hx ▸ A.anchor_mem_owner
    exact Set.disjoint_left.1
      ((reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut r).mono_left
        Set.subset_union_left)
      ((PopularSwitching.old_mem_ladderTrace_iff J _ x).2 hxOwner) hxC
  · obtain ⟨⟨a, b, hab, hchoice⟩, _hne⟩ := htail
    have hc := (J).chosenConnector?_eq_some hchoice
    have haTail := (A.tail.edgeSet_subset_support_prod hab).1
    have habOriginal := A.tail_edges_subset hab
    have haNotApex : a ≠ requestAuxVertex r := by
      intro h
      exact (FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U S K r) habOriginal)
        (h.trans (strongSelectedPath_finish U S K r).symm)
    rcases hc.1 with hexit | ⟨i, hai, _hxi⟩
    · cases a with
      | old z =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          exact reservedStrongSelected_offApex_not_mem_cut r
            (A.tail_support_subset haTail) haNotApex hxC
      | edge z w =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          have hfamily : (x, w) ∈ (J).familyEdges :=
            (J).edgeNode_mem_familyEdges_of_start_in_source
              (strongSelectedPath U S K r)
              ((strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩)
              (A.tail_support_subset haTail)
          have hback : (x, w) ∈ reservedRawRequestBackwardEdges r := by
            rw [reservedRawRequestBackward_eq_tail_diff_cut]
            refine ⟨⟨haTail, hfamily⟩, ?_⟩
            intro hcut
            exact reservedStrongSelected_offApex_not_mem_cut r
              (A.tail_support_subset haTail) haNotApex hcut.1
          exact canonicalDeferredLadder_rawBackwardTail_not_mem_CV
            preferred hkappa huncountable hNoEnter hL S r hback hxC
      | proxy i => simp at hexit
    · subst a
      exact A.tail_no_proxy i haTail

include hkappa huncountable hNoEnter in
/-- The entire simultaneous inserted relation has no departure from CV. -/
theorem canonicalDeferredLadder_rawInsertedTail_not_mem_CV
    {x y : V}
    (he : (x, y) ∈ reservedRawInsertedEdges (L := Lc) (hL := hL) (S := S)) :
    x ∉ GroundingCut.CV J S.cut := by
  intro hxC
  rcases he with hforward | hprefix
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hforward
    exact canonicalDeferredLadder_rawForwardTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S r hr hxC
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hprefix
    exact Set.disjoint_left.1 (reservedRawOwnerAttachment_prefix_grounded_and_avoids r).2
      (Or.inl hxC) ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).1

include hkappa huncountable hNoEnter in
/-- The actual global forward blocking bound has no old-cut disjunct. -/
theorem canonicalDeferredLadder_rawGlobalForwardTail_beforeEq_blockingPoint
    (P : (J).Fragment)
    (hP : P ∈ (reservedStrongSelectedPruningData (L := Lc) (hL := hL) (S := S)).relevantG0)
    {x y : V} (he : (x, y) ∈ reservedRawForwardEdges (L := Lc) (hL := hL) (S := S))
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x (GroundingCut.blockingPoint J S.cut P) :=
  (reservedRawGlobalForwardTail_beforeEq_or_mem_CV P hP he hxP).resolve_right
    (canonicalDeferredLadder_rawInsertedTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hL S (Or.inl he))

#print axioms canonicalDeferredLadder_rawForwardTail_not_mem_CV
#print axioms canonicalDeferredLadder_rawInsertedTail_not_mem_CV
#print axioms canonicalDeferredLadder_rawGlobalForwardTail_beforeEq_blockingPoint

end Erdos599.DWeb.KappaLadder.Deferred
