/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawStrictContactOrder

/-!
# Terminal blockers and strict order at every relevant blocker

A non-escaping relevant fragment ends on an essential reference owner.
Finite auxiliary sources lie on inessential records, so they cannot be
old departures on that fragment. Edge departures survive the cut and are
edges of the fragment itself; they cannot leave its terminal. Together
with escape exclusion this makes every actual departure bound strict.
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
local notation "D" => reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S)

/-- A finite deferred auxiliary source cannot lie on an essential owner. -/
theorem finiteTerminalSet_not_mem_essential_support
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    {x : V} (hx : x ∈ (popularAuxiliaryInput L hlegal).finiteSource)
    {Y : Gamma.DPath} (hY : Y ∈ (popularAuxiliaryInput L hlegal).essentialLadder) :
    x ∉ Y.support := by
  obtain ⟨a, _ha, p, hchosen, hterminal⟩ := hx
  have hp : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hlegal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  intro hxY
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
    (hlegal.warpStages (finalStage kappa)) hY
    ⟨x, Gamma.terminal_mem_support hterminal, hxY⟩) hp

/-- Relevance without escape forces an essential parent. -/
theorem reservedRelevantFragment_parent_essential_of_not_meetsEscape
    (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    (hno : ¬ Fragment.MeetsEscape J S.cut P) : P.parent ∈ (J).essentialLadder := by
  obtain ⟨t, ht, Y, hY, htY⟩ := hP.2.resolve_left hno
  have hsame : P.parent = Y := DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint
    P.parent_mem hY.1 (P.support_subset (Gamma.terminal_mem_support ht))
    (Gamma.terminal_mem_support htY)
  exact hsame ▸ hY

/-- A surviving reference edge on a fragment cannot leave its terminal. -/
theorem reservedSurvivingEdge_tail_ne_fragment_terminal
    (P : (J).Fragment) (hP : P ∈ GroundingCut.fragments J S.cut)
    {x y t : V} (hx : x ∈ P.path.support) (he : (x, y) ∈ (J).familyEdges)
    (hcut : (x, y) ∉ GroundingCut.CE J S.cut)
    (ht : P.path.terminal? = some t) : x ≠ t := by
  have heP := GroundingSurvivingEdgeFragment.edge_mem_fragment J P hP hx he hcut
  cases hp : P.path with
  | inl p =>
      have hfinish : p.finish = t :=
        Option.some.inj (by simpa only [hp, Path.terminal?] using ht)
      have hedge : (x, y) ∈ p.edgeSet := by simpa only [hp, Path.edgeSet] using heP
      exact fun h ↦ FinitePath.source_ne_finish_of_mem_edgeSet p hedge (h.trans hfinish.symm)
  | inr p => simp [hp] at ht

/-- There is no actual forward departure from a non-escaping relevant terminal. -/
theorem reservedRawForwardTail_ne_nonescaping_terminal
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    (hno : ¬ Fragment.MeetsEscape J S.cut P) {x y t : V}
    (he : (x, y) ∈ (reservedRawOwnerAttachment r).forwardEdges)
    (hxP : x ∈ P.path.support) (ht : P.path.terminal? = some t) : x ≠ t := by
  let A := reservedRawOwnerAttachment r
  have hessential := reservedRelevantFragment_parent_essential_of_not_meetsEscape P hP hno
  rcases he with hfirst | htail
  · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.mp hfirst)
    exact (Set.disjoint_left.1 (reservedRawRelevantFragment_disjoint_startingRecord r P hP)
      hxP (hx ▸ A.anchor_mem_owner)).elim
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
          rcases hsource with hoff | hfinite
          · exact (hoff.2 ⟨P.parent, P.parent_mem, P.support_subset hxP⟩).elim
          · exact (finiteTerminalSet_not_mem_essential_support L hL.legal hfinite
              hessential (P.support_subset hxP)).elim
      | edge z w =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          have hfamily : (x, w) ∈ (J).familyEdges :=
            (J).edgeNode_mem_familyEdges_of_start_in_source
              (strongSelectedPath U S K r)
              ((strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩)
              (A.tail_support_subset haTail)
          exact reservedSurvivingEdge_tail_ne_fragment_terminal P hP.1.1.1 hxP hfamily
            (fun hcut ↦ reservedStrongSelected_offApex_not_mem_cut r
              (A.tail_support_subset haTail) haNotApex hcut.1) ht
      | proxy i => simp at hexit
    · subst a
      exact (A.tail_no_proxy i haTail).elim

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
/-- Every actual backward departure precedes its relevant blocker strictly. -/
theorem canonicalDeferredLadder_rawBackwardTail_before_blocker
    (r : Request Jc Sc.cut) (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r)
    (hxP : e.1 ∈ P.path.support) :
    GroundingCut.Before P.path e.1 (GroundingCut.blockingPoint Jc Sc.cut P) := by
  by_cases hescape : Fragment.MeetsEscape Jc Sc.cut P
  · exact canonicalDeferredLadder_rawBackwardTail_before_escapingBlocker
      preferred hkappa huncountable hNoEnter hLc Sc r P hP hescape he hxP
  · obtain ⟨t, ht, _htCut⟩ := hP.2.resolve_left hescape
    refine ⟨canonicalDeferredLadder_rawBackwardTail_beforeEq_blockingPoint
      preferred hkappa huncountable hNoEnter hLc Sc r P hP he hxP, ?_⟩
    rw [GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape Jc Sc.cut P hescape ht]
    have href := reservedRawRequestBackward_subset_cut_reference r he
    exact reservedSurvivingEdge_tail_ne_fragment_terminal P hP.1.1.1 hxP
      href.1.1 href.2 ht

include hkappa huncountable hNoEnter in
/-- Every global inserted forward departure strictly precedes a relevant blocker. -/
theorem canonicalDeferredLadder_rawGlobalForwardTail_before_blocker
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0) {x y : V}
    (he : (x, y) ∈ reservedRawForwardEdges (L := Lc) (hL := hLc) (S := Sc))
    (hxP : x ∈ P.path.support) :
    GroundingCut.Before P.path x (GroundingCut.blockingPoint Jc Sc.cut P) := by
  by_cases hescape : Fragment.MeetsEscape Jc Sc.cut P
  · exact canonicalDeferredLadder_rawGlobalForwardTail_before_escapingBlocker
      preferred hkappa huncountable hNoEnter hLc Sc P hP hescape he hxP
  · obtain ⟨t, ht, _htCut⟩ := hP.2.resolve_left hescape
    refine ⟨canonicalDeferredLadder_rawGlobalForwardTail_beforeEq_blockingPoint
      preferred hkappa huncountable hNoEnter hLc Sc P hP he hxP, ?_⟩
    rw [GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape Jc Sc.cut P hescape ht]
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp he
    exact reservedRawForwardTail_ne_nonescaping_terminal r P hP hescape hr hxP ht

end Canonical

#print axioms finiteTerminalSet_not_mem_essential_support
#print axioms reservedRawForwardTail_ne_nonescaping_terminal
#print axioms canonicalDeferredLadder_rawBackwardTail_before_blocker
#print axioms canonicalDeferredLadder_rawGlobalForwardTail_before_blocker

end Erdos599.DWeb.KappaLadder.Deferred
