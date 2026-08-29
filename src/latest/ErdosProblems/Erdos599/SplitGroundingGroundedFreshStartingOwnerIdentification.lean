/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshStartingRecord
import ErdosProblems.Erdos599.SplitGroundingGroundedLastContactComponentSplice
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantBackwardNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedSourceGeometry

/-!
# Identifying a canonical selected route's starting owner

The source gadget of a canonical selected request names one literal grounded
record of the limiting ladder.  The decoded selected trace starts on that
record.  Warp disjointness therefore identifies any limiting-ladder owner
which contains the decoded trace initial with this canonical starting record.

This is the precise self-owner premise needed by the source's last-contact
component replacement; it does not identify arbitrary later ladder
components contacted by the selected route.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev StartingIdentificationInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev StartingIdentificationIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev StartingIdentificationControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

/-- The decoded selected trace starts on the exact grounded record represented
by its actual canonical auxiliary source. -/
theorem splitGroundedFreshAvoidingCanonicalSelectedTrace_initial_mem_startingRecord
    (r : Request
      (StartingIdentificationInput (L := L) (hL := hL)) S.cut) :
    (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) r).initial ∈
      (L.splitGroundedFreshAvoidingCanonicalStartingRecord
        (hnotFresh := hnotFresh) r).record.support := by
  let q := strongSelectedPath
    (StartingIdentificationIndexed (L := L) (hL := hL)
      (hground := hground)) S
    (StartingIdentificationControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)) r
  let x := L.splitGroundedFreshAvoidingCanonicalSelectedSource
    (hnotFresh := hnotFresh) r
  let R := L.splitGroundedFreshAvoidingCanonicalStartingRecord
    (hnotFresh := hnotFresh) r
  rcases R.represents with ⟨p, hrecord, hsource⟩ |
      ⟨i, hrecord, hsource⟩
  · have hstart : q.start = .old p.finish := by
      simpa only [q, x,
        splitGroundedFreshAvoidingCanonicalSelectedSource] using hsource
    have hinitial := L.splitGroundedSelectedRequestTrace_initial_of_start_old
      hL hground S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      r p.finish hstart
    rw [hrecord]
    change (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) r).initial ∈
        p.support
    rw [hinitial]
    exact p.finish_mem_support
  · have hstart : q.start = .proxy i := by
      simpa only [q, x,
        splitGroundedFreshAvoidingCanonicalSelectedSource] using hsource
    have hinitial := L.splitGroundedSelectedRequestTrace_initial_mem_proxyPath
      hL hground S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      r i hstart
    change (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) r).initial ∈
        R.record.support
    rw [hrecord]
    exact hinitial

/-- Uniqueness of the canonical starting owner inside the limiting warp. -/
theorem splitGroundedFreshAvoidingCanonical_startingOwner_eq
    (r : Request
      (StartingIdentificationInput (L := L) (hL := hL)) S.cut)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (hinitial : (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) r).initial ∈
        Y.support) :
    Y = (L.splitGroundedFreshAvoidingCanonicalStartingRecord
      (hnotFresh := hnotFresh) r).record := by
  let R := L.splitGroundedFreshAvoidingCanonicalStartingRecord
    (hnotFresh := hnotFresh) r
  exact Alternating.DWeb.IsWarp.eq_of_mem_support
    (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.disjoint
    hY R.record_mem_ladder hinitial
      (L.splitGroundedFreshAvoidingCanonicalSelectedTrace_initial_mem_startingRecord
        (hnotFresh := hnotFresh) r)

/-- A literal splice whose old owner contains its selected trace initial is
exactly a starting-record splice and hence its old owner avoids the complete
relevant boundary. -/
theorem SplitGroundedLastContactComponentSplice.oldOwner_disjoint_relevantBB_of_traceInitial
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
    (howner : X.oldOwner ∈ L.limitWarp)
    (hinitial : (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest X.contact.owner.1)).initial ∈ X.oldOwner.support) :
    Disjoint (L.splitGroundedRelevantBB hL.legal S.cut)
      X.oldOwner.support := by
  have heq := L.splitGroundedFreshAvoidingCanonical_startingOwner_eq
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
    (chosenRequest X.contact.owner.1) X.oldOwner howner hinitial
  rw [heq]
  exact L.splitGroundedFreshAvoidingCanonicalStartingRecord_disjoint_relevantBB
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
      (chosenRequest X.contact.owner.1)

/-- Therefore every source-first relevant-boundary point of a self-owner
replacement component lies on its selected suffix. -/
theorem SplitGroundedLastContactComponentSplice.selfOwner_frontier_mem_suffix
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
    (howner : X.oldOwner ∈ L.limitWarp)
    (hinitial : (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest X.contact.owner.1)).initial ∈ X.oldOwner.support)
    {b : V}
    (hbB : b ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
    (hb : b ∈ X.replacementCarrier) :
    b ∈ X.contact.normalizedSuffix.path.vertexSet := by
  apply X.frontier_mem_normalizedSuffix
    (B := L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
  · exact (X.oldOwner_disjoint_relevantBB_of_traceInitial
      howner hinitial).mono_left
        (L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut)
  · exact hbB
  · exact hb

/-- A terminal forward splice in the native-frontier backward recursion
cannot return to its canonical starting record when the original finite
segment still ends on the source-first frontier.  The recursion preserves
the old parent, while every canonical starting record avoids the complete
relevant boundary.  This eliminates the genuine duplicate-start case
without transporting a root through the discarded old tail. -/
theorem splitGroundedFreshRelevant_no_selfStarting_forwardSplice
    (initial state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
      state.parent state.rootPath state.deleted)
    (hsame : state.parent = initial.parent)
    (hfrontier : initial.rootPath.finish ∈
      L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
    (hinitial : (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest splice.contact.owner.1)).initial ∈
        state.parent.support) : False := by
  have howner := L.splitGroundedFreshAvoidingCanonical_startingOwner_eq
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
    (chosenRequest splice.contact.owner.1) state.parent state.parent_mem
      hinitial
  have hfinishParent : initial.rootPath.finish ∈ state.parent.support := by
    rw [hsame]
    exact initial.rootPath_support initial.rootPath.finish_mem_support
  have hfinishRecord : initial.rootPath.finish ∈
      (L.splitGroundedFreshAvoidingCanonicalStartingRecord
        (hnotFresh := hnotFresh)
        (chosenRequest splice.contact.owner.1)).record.support := by
    rw [← howner]
    exact hfinishParent
  exact Set.disjoint_left.mp
    (L.splitGroundedFreshAvoidingCanonicalStartingRecord_disjoint_relevantBB
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
      (chosenRequest splice.contact.owner.1))
    (L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut hfrontier)
      hfinishRecord

/-- In a normalized obstruction whose original segment still reaches the
source-first frontier, the terminal self-control forward splice is therefore
necessarily an off-starting-component splice.  This is the exact residual
after the duplicate-start case has been removed by the canonical carrier
avoidance built into the selector. -/
theorem splitGroundedFreshRelevant_forwardSplice_traceInitial_not_mem_parent
    (initial state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
      state.parent state.rootPath state.deleted)
    (hsame : state.parent = initial.parent)
    (hfrontier : initial.rootPath.finish ∈
      L.splitGroundedRelevantSourceFirstBB hL.legal S.cut) :
    (selectedRequestTrace
      (StartingIdentificationIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (StartingIdentificationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest splice.contact.owner.1)).initial ∉
        state.parent.support := by
  intro hinitial
  exact L.splitGroundedFreshRelevant_no_selfStarting_forwardSplice
    initial state splice hsame hfrontier hinitial

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonicalSelectedTrace_initial_mem_startingRecord
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonical_startingOwner_eq
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedLastContactComponentSplice.selfOwner_frontier_mem_suffix
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_no_selfStarting_forwardSplice
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_forwardSplice_traceInitial_not_mem_parent
