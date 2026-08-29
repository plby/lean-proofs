/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawLocalSourceRoot

/-!
# Old requests on reference owners and the actual backward-tail cut exception

Own-apex trace avoidance forces an old request on a reference owner to be
its target-marker initial. Actual request sinks are outside the original
source, so no such request lies on a grounded owner. A backward tail has
an outgoing reference edge and cannot be a finite auxiliary source. This
removes the old-cut exception from its actual blocking-order bound.
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

/-- An old request on a reference owner is a target marker. The zero join
alternative would violate the actual own-apex trace avoidance. -/
theorem reservedOldRequest_mem_targetMarkers_of_mem_owner
    (z : oldRequests J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    (hzY : z.1 ∈ Y.support) : z.1 ∈ (J).targetMarkers := by
  let r : Request J S.cut := .inl z
  let p := strongSelectedPath U S K r
  have hpSource : p.start ∈ (J).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  have hfinish : p.finish = LambdaVertex.old z.1 := strongSelectedPath_finish U S K r
  have hne : (LambdaVertex.old z.1 : (J).LV) ≠ p.start := by
    intro h
    apply requestAuxVertex_not_mem_source r
    change LambdaVertex.old z.1 ∈ (J).lambda.source
    exact h ▸ hpSource
  obtain ⟨a, ha⟩ := Walk.exists_edge_to_of_mem_of_ne_start p.walk
    (hfinish ▸ p.finish_mem_support) hne
  have haNotApex : a ≠ requestAuxVertex r := by
    intro h
    exact FinitePath.source_ne_finish_of_mem_edgeSet p ha (h.trans hfinish.symm)
  have haNotTrace : a ∉ PopularSwitching.ladderTrace J Y := by
    intro haTrace
    apply Set.disjoint_left.1 (reservedStrongSelectedPath_avoids_ownApexCarrier r)
      (p.edgeSet_subset_support_prod ha).1
    exact ⟨⟨Y, hY, (PopularSwitching.old_mem_ladderTrace_iff J Y z.1).2 hzY,
      haTrace⟩, by simpa only [Set.mem_singleton_iff] using haNotApex⟩
  have hnotOff : z.1 ∉ (J).offLadder :=
    fun hz ↦ hz.2 ⟨Y, hY, hzY⟩
  have htarget (hz : z.1 ∈ (J).offLadder ∪ (J).targetMarkers) :
      z.1 ∈ (J).targetMarkers := hz.resolve_left hnotOff
  have hadj := p.edgeSet_subset_adj ha
  cases a with
  | old x => exact htarget ((J).lambda_adj_old_old x z.1 |>.1 hadj).2.1
  | proxy i => exact htarget ((J).lambda_adj_proxy_old i z.1 |>.1 hadj).1
  | edge x y =>
      have h := (J).lambda_adj_edge_old x y z.1 |>.1 hadj
      rcases h.2 with hzero | hforward
      · exact (haNotTrace ((PopularSwitching.edge_mem_ladderTrace_iff J Y x y).2
          ((J).referenceEdge_mem_owner_of_tail hY h.1 (hzero ▸ hzY)))).elim
      · exact htarget hforward.1

/-- Deferred target markers are the initial vertices of their actual
limiting reference owners. -/
theorem reservedOldRequest_owner_initial
    (z : oldRequests J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    (hzY : z.1 ∈ Y.support) : Y.initial = z.1 := by
  have htarget := reservedOldRequest_mem_targetMarkers_of_mem_owner z hY hzY
  obtain ⟨Z, hZ, hinitial⟩ :=
    targetMarkers_subset_limitWarp_initialSet L hL.legal htarget
  have hZY : Z = Y := DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint hZ hY
    (hinitial ▸ Z.initial_mem_support) hzY
  exact hZY ▸ hinitial

section Canonical

variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hLc : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (Sc : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hLc))

local notation "Lc" => canonicalDeferredLadder Gamma kappa preferred
local notation "Jc" => popularAuxiliaryInput Lc hLc.legal

include hkappa huncountable hNoEnter in
/-- No actual old request lies on a source-grounded reference owner. -/
theorem canonicalDeferredLadder_oldRequest_not_mem_grounded_owner
    (z : oldRequests Jc Sc.cut) {Y : Gamma.DPath} (hY : Y ∈ (Jc).ladder.paths)
    (hground : Y.initial ∈ Gamma.source) : z.1 ∉ Y.support := by
  intro hzY
  have hstart := reservedOldRequest_owner_initial z hY hzY
  apply canonicalDeferredLadder_rawRequest_not_source
    preferred hkappa huncountable hNoEnter hLc Sc (.inl z)
  change z.1 ∈ Gamma.source
  exact hstart ▸ hground

include hkappa huncountable hNoEnter in
/-- The old-cut exception is impossible for every actual backward tail. -/
theorem canonicalDeferredLadder_rawBackwardTail_not_mem_CV
    (r : Request Jc Sc.cut) {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) :
    e.1 ∉ GroundingCut.CV Jc Sc.cut := by
  intro hxC
  have href := reservedRawRequestBackward_subset_cut_reference r he
  obtain ⟨Y, hY, heY⟩ := href.1.1
  have hground := canonicalDeferredLadder_rawBackwardOwner_grounded
    preferred hkappa huncountable hNoEnter hLc Sc r hY he heY
  have hnotFinite : e.1 ∉ (Jc).finiteSource := by
    intro hfinite
    exact (popularAuxiliary_hasBoundaryIncidence Lc hLc.legal).finite_source_sink
      hfinite ⟨e.2, Y, hY, heY⟩
  let z : oldRequests Jc Sc.cut := ⟨e.1, hxC, hnotFinite⟩
  exact canonicalDeferredLadder_oldRequest_not_mem_grounded_owner
    preferred hkappa huncountable hNoEnter hLc Sc z hY hground
    (Y.edgeSet_subset_support_prod heY).1

include hkappa huncountable hNoEnter in
/-- The actual backward-tail blocking bound has no old-cut disjunct. -/
theorem canonicalDeferredLadder_rawBackwardTail_beforeEq_blockingPoint
    (r : Request Jc Sc.cut) (P : (Jc).Fragment)
    (hP : P ∈ (reservedStrongSelectedPruningData (L := Lc) (hL := hLc) (S := Sc)).relevantG0)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r)
    (hxP : e.1 ∈ P.path.support) :
    GroundingCut.BeforeEq P.path e.1 (GroundingCut.blockingPoint Jc Sc.cut P) :=
  (reservedRawBackwardTail_beforeEq_or_mem_CV r P hP he hxP).resolve_right
    (canonicalDeferredLadder_rawBackwardTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hLc Sc r he)

end Canonical

#print axioms reservedOldRequest_owner_initial
#print axioms canonicalDeferredLadder_oldRequest_not_mem_grounded_owner
#print axioms canonicalDeferredLadder_rawBackwardTail_not_mem_CV
#print axioms canonicalDeferredLadder_rawBackwardTail_beforeEq_blockingPoint

end Erdos599.DWeb.KappaLadder.Deferred
