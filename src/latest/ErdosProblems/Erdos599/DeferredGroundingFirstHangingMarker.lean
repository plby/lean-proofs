/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawUnchangedFragmentRoot

/-!
# Ordinary escape exclusion and the first hanging essential fragment

Endpoint-open finite descent forces a source-first blocker with an ordinary
auxiliary escape to be a source. A first hanging essential fragment starts
at a target marker; if that marker were outside the cut, its trivial escape
would make it the blocker and contradict hangingness. Its cut initial is
therefore an actual old request and is already rooted. Any unrooted blocker
on this fragment must be strictly later, not silently discarded.
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
local notation "D" => reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S)
local notation "T" => reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)

/-- Deferred accumulated initial provenance also covers hanging final members. -/
theorem IsDeferredLegal.hanging_initial_mem_markerSet
    {L : Gamma.KappaLadder kappa} (hlegal : IsDeferredLegal L)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp) (hhang : Y.initial ∉ Gamma.source) :
    Y.initial ∈ L.markerSet := by
  rcases hlegal.accumulatedInitialProvenance (finalStage kappa) Y hY with
    hs | ⟨a, _ha, hm⟩
  · exact (hhang hs).elim
  · exact ⟨a, hm⟩

/-- A hanging essential limiting owner starts at an actual target marker. -/
theorem deferred_hangingEssential_initial_mem_targetMarkers
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    {Y : Gamma.DPath} (hY : Y ∈ (popularAuxiliaryInput L hlegal).essentialLadder)
    (hhang : Y.initial ∉ Gamma.source) :
    Y.initial ∈ (popularAuxiliaryInput L hlegal).targetMarkers :=
  ⟨hlegal.hanging_initial_mem_markerSet hY.1 hhang, Y, hY, Y.initial_mem_support⟩

/-- A target marker outside the old cut has its literal trivial ordinary escape. -/
theorem deferred_targetMarker_canReach_avoiding
    {b : V} (hb : b ∈ (J).targetMarkers) (hnot : b ∉ GroundingCut.CV J S.cut) :
    (J).lambda.CanReachTargetAvoiding S.cut (.old b) := by
  let q : FinitePath (J).lambda.graph := FinitePath.trivial (J).lambda.graph (.old b)
  refine ⟨q, ⟨rfl, (J).mem_lambda_target_old b |>.2 hb⟩, ?_⟩
  change Disjoint q.support S.cut
  apply Set.disjoint_left.mpr
  intro a ha haC
  have heq : a = LambdaVertex.old b := by simpa [q] using ha
  apply hnot
  change LambdaVertex.old b ∈ S.cut
  exact heq ▸ haC

/-- The given ordinary escape is retained, rather than weakened to the
source-or-virtual disjunction. -/
theorem reservedSourceFirstBlocker_source_of_ordinaryEscape
    (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    (hbT : GroundingCut.blockingPoint J S.cut P ∈ T)
    (hcan : (J).lambda.CanReachTargetAvoiding S.cut
      (.old (GroundingCut.blockingPoint J S.cut P))) :
    GroundingCut.blockingPoint J S.cut P ∈ Gamma.source := by
  obtain ⟨R, hsource, hfinish, hroof, _hb, hfirst⟩ := hbT
  obtain ⟨q, ⟨hqStart, hqTarget⟩, hqAvoid⟩ := hcan
  have hqStartR : q.start = LambdaVertex.old R.finish :=
    hqStart.trans (congrArg LambdaVertex.old hfinish.symm)
  let E : GroundingRelaxedEscape.RelaxedEscape J S.cut R.finish := {
    route := q
    start_eq := Or.inl hqStartR
    target := hqTarget
    avoids := hqAvoid
    old_not_mem := fun hc ↦ Set.disjoint_left.1 hqAvoid q.start_mem_support
      (hqStartR.symm ▸ hc) }
  have hfinishP : R.finish ∈ P.path.support := by
    rw [hfinish]
    exact GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
  have hescape : Fragment.MeetsEscape J S.cut P := ⟨R.finish, hfinishP, ⟨E⟩⟩
  have hs := GroundingInputRelevantDecoder.endpointOpen_ordinary_escape_implies_source
    D (popularAuxiliary_sourceCovered L hL.legal) S.separates R hsource hroof
    (fun {_} hx ↦ hfirst _ hx) P hP hfinish.symm hescape E hqStartR
  exact hfinish ▸ hs

/-- In the first hanging essential case, source-first membership forces
the initial target marker to be in the old cut. -/
theorem reservedSourceFirst_hangingEssentialFirst_initial_mem_CV
    (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    (hbT : GroundingCut.blockingPoint J S.cut P ∈ T)
    (hessential : P.parent ∈ (J).essentialLadder)
    (hhang : P.parent.initial ∉ Gamma.source)
    (hfirst : P.path.initial = P.parent.initial) :
    P.path.initial ∈ GroundingCut.CV J S.cut := by
  by_contra hnotC
  have hmarker : P.path.initial ∈ (J).targetMarkers := hfirst ▸
    deferred_hangingEssential_initial_mem_targetMarkers L hL.legal hessential hhang
  have hcan := deferred_targetMarker_canReach_avoiding hmarker hnotC
  have hRR : P.path.initial ∈ (J).escapeRegion S.cut :=
    ⟨GroundingRelaxedEscape.RelaxedEscape.ofOrdinary J S.cut hcan⟩
  have hescape : Fragment.MeetsEscape J S.cut P :=
    ⟨P.path.initial, P.path.initial_mem_support, hRR⟩
  have hblock : GroundingCut.blockingPoint J S.cut P = P.path.initial :=
    GroundingCutDecoder.beforeEq_antisymm
      (GroundingCut.blockingPoint_beforeEq_escape J S.cut P hescape
        P.path.initial_mem_support hRR)
      (GroundingFragmentWarp.initial_beforeEq_of_mem
        (GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2))
  have hsource := reservedSourceFirstBlocker_source_of_ordinaryEscape P hP hbT
    (hblock.symm ▸ hcan)
  exact hhang (hfirst ▸ hblock ▸ hsource)

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
local notation "Tc" => reservedStrongSelectedSourceFirstBB (L := Lc) (hL := hLc) (S := Sc)

/-- An unrooted source-first blocker has no ordinary auxiliary escape. -/
theorem canonicalDeferredLadder_unrootedBlocker_no_ordinaryEscape
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hbT : GroundingCut.blockingPoint Jc Sc.cut P ∈ Tc)
    (hnotRoot : ¬ reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
      (GroundingCut.blockingPoint Jc Sc.cut P)) :
    ¬ (Jc).lambda.CanReachTargetAvoiding Sc.cut
      (.old (GroundingCut.blockingPoint Jc Sc.cut P)) := by
  intro hcan
  exact hnotRoot (reservedRawSourceRooted_of_source
    (reservedSourceFirstBlocker_source_of_ordinaryEscape P hP hbT hcan))

include hkappa huncountable hNoEnter in
/-- The cut marker initial is itself an actual old request, hence rooted. -/
theorem canonicalDeferredLadder_hangingEssentialFirst_initial_sourceRooted
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hbT : GroundingCut.blockingPoint Jc Sc.cut P ∈ Tc)
    (hessential : P.parent ∈ (Jc).essentialLadder)
    (hhang : P.parent.initial ∉ Gamma.source)
    (hfirst : P.path.initial = P.parent.initial) :
    reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc) P.path.initial := by
  have hiCV := reservedSourceFirst_hangingEssentialFirst_initial_mem_CV
    P hP hbT hessential hhang hfirst
  have hiNotFinite : P.path.initial ∉ (Jc).finiteSource := by
    intro hiFinite
    exact finiteTerminalSet_not_mem_essential_support Lc hLc.legal hiFinite hessential
      (P.support_subset P.path.initial_mem_support)
  let z : oldRequests Jc Sc.cut := ⟨P.path.initial, hiCV, hiNotFinite⟩
  exact canonicalDeferredLadder_rawRequest_sourceRooted
    preferred hkappa huncountable hNoEnter hLc Sc (.inl z)

include hkappa huncountable hNoEnter in
/-- The essential remaining case has a rooted cut initial strictly before
the unrooted blocker. This does not assert that the gap can be traversed
after stopping. -/
theorem canonicalDeferredLadder_unrootedEssentialBlocker_cut_initial_strict
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hbT : GroundingCut.blockingPoint Jc Sc.cut P ∈ Tc)
    (hessential : P.parent ∈ (Jc).essentialLadder)
    (hnotRoot : ¬ reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
      (GroundingCut.blockingPoint Jc Sc.cut P)) :
    P.path.initial ∈ GroundingCut.CV Jc Sc.cut ∧
      reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc) P.path.initial ∧
      GroundingCut.Before P.path P.path.initial (GroundingCut.blockingPoint Jc Sc.cut P) := by
  obtain ⟨hfirst, hhang, _hnoCut, _hunchanged⟩ :=
    canonicalDeferredLadder_rawUnrootedBlocker_first_hanging
      preferred hkappa huncountable hNoEnter hLc Sc P hP hnotRoot
  have hiRoot := canonicalDeferredLadder_hangingEssentialFirst_initial_sourceRooted
    preferred hkappa huncountable hNoEnter hLc Sc P hP hbT hessential hhang hfirst
  refine ⟨reservedSourceFirst_hangingEssentialFirst_initial_mem_CV
    P hP hbT hessential hhang hfirst, hiRoot,
    GroundingFragmentWarp.initial_beforeEq_of_mem
      (GroundingCut.blockingPoint_mem_support Jc Sc.cut P hP.1.2), ?_⟩
  exact fun heq ↦ hnotRoot (heq ▸ hiRoot)

/-- The inessential remaining case must have a genuine virtual escape;
the escape-free relevant alternative would make its parent essential. -/
theorem canonicalDeferredLadder_unrootedInessentialBlocker_virtualEscape
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hbT : GroundingCut.blockingPoint Jc Sc.cut P ∈ Tc)
    (hnotEssential : P.parent ∉ (Jc).essentialLadder)
    (hnotRoot : ¬ reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
      (GroundingCut.blockingPoint Jc Sc.cut P)) :
    Nonempty (GroundingInputRelevantDecoder.RelevantVirtualEscape Jc Sc.cut
      (GroundingCut.blockingPoint Jc Sc.cut P)) := by
  have hescape : Fragment.MeetsEscape Jc Sc.cut P := by
    by_contra hno
    exact hnotEssential (reservedRelevantFragment_parent_essential_of_not_meetsEscape P hP hno)
  rcases reservedStrongSelected_sourceFirst_escapeBlocker_source_or_virtual
      hbT P hP rfl hescape with hs | hv
  · exact (hnotRoot (reservedRawSourceRooted_of_source hs)).elim
  · exact hv

end Canonical

#print axioms GroundingInputRelevantDecoder.endpointOpen_ordinary_escape_implies_source
#print axioms reservedSourceFirstBlocker_source_of_ordinaryEscape
#print axioms reservedSourceFirst_hangingEssentialFirst_initial_mem_CV
#print axioms canonicalDeferredLadder_unrootedEssentialBlocker_cut_initial_strict
#print axioms canonicalDeferredLadder_unrootedInessentialBlocker_virtualEscape

end Erdos599.DWeb.KappaLadder.Deferred
