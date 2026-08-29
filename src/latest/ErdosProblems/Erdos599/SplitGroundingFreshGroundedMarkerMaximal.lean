/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshMarkerMaximal
import ErdosProblems.Erdos599.SplitGroundingGroundedAuxiliary

/-!
# Maximal-rung exclusion in the grounded split auxiliary

The grounded split auxiliary has the same limiting ladder, old vertices and
target markers as the full split auxiliary; only its proxy type is smaller.
The presentation-independent pre-marker transport therefore gives the same
fresh same-stage exclusion directly, without relabelling auxiliary paths.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

private theorem groundedTargetMarker_mem_splitTargetMarkers
    (L : G.KappaLadder kappa) (hlegal : L.IsSplitLegal) {y : V}
    (hy : y ∈ (L.splitGroundedPopularAuxiliaryInput hlegal).targetMarkers) :
    y ∈ (L.splitPopularAuxiliaryInput hlegal).targetMarkers := by
  simpa only [splitGroundedPopularAuxiliaryInput,
    splitPopularAuxiliaryInput, PopularAuxiliary.Input.targetMarkers,
    PopularAuxiliary.Input.essentialLadder] using hy

/-- A finite fresh record has no target-pure grounded-auxiliary route to its
own retained same-stage marker. -/
theorem canonicalLadder_no_freshFinite_grounded_equalTargetPureRoute
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (f : FinitePath G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inl f)
    (q : FinitePath
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.graph)
    (hs : q.start ∈
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.source)
    (hpure :
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).IsTargetPure q)
    {y : V} (hqstart : q.start = .old f.finish)
    (hqfinish : q.finish = .old y)
    (hmarker : (canonicalLadder G kappa preferred).marker a.1 = some y)
    (htarget : y ∈
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).targetMarkers) :
    False := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let J := L.splitGroundedPopularAuxiliaryInput hlegal
  change L.freshGroundRecordPath hlegal a = .inl f at hrecord
  change q.start ∈ J.lambda.source at hs
  change J.IsTargetPure q at hpure
  change L.marker a.1 = some y at hmarker
  change y ∈ J.targetMarkers at htarget
  have htargetSplit : y ∈ (L.splitPopularAuxiliaryInput hlegal).targetMarkers :=
    groundedTargetMarker_mem_splitTargetMarkers L hlegal htarget
  have hpArrow : L.freshGroundRecordPath hlegal a ∈
      L.arrowPart a.1 :=
    L.freshGroundRecordPath_mem_arrowPart hlegal a
  have hpEssential : L.freshGroundRecordPath hlegal a ∈
      G.essentialWarpPart (L.arrowPart a.1) := by
    by_contra hpEssential
    have hpInessential : L.freshGroundRecordPath hlegal a ∈
        G.inessentialPaths (L.arrowPart a.1) :=
      ⟨hpArrow, hpEssential⟩
    have hxStrict : f.finish ∈
        G.strictRoof (G.terminalFrontier (L.arrowPart a.1)) := by
      apply G.terminal_mem_strictRoof_of_mem_inessentialPaths hpInessential
      rw [hrecord]
      rfl
    have hrun : PopularAuxiliary.Input.RunsFromTo f.finish y
        (J.decodeWalkSteps q.walk) :=
      J.decodeWalkSteps_runs_from_entry q.walk
        (by rw [hqstart]; rfl) (by rw [hqfinish]; rfl)
    have hyRoof : y ∈ G.roof
        (G.terminalFrontier (L.arrowPart a.1)) :=
      canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
        preferred hkappa huncountable hNoEnter J rfl a.1 q hs hpure
        hrun hxStrict
    exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter hmarker htargetSplit hyRoof
  exact canonicalLadder_no_freshFinite_of_essential_arrowPart
    preferred hkappa huncountable hNoEnter a f hrecord hpEssential hmarker

/-- A fresh ray proxy has no target-pure grounded-auxiliary route to its own
retained same-stage marker. -/
theorem canonicalLadder_no_freshRay_grounded_equalTargetPureRoute
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (r : Ray G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inr r)
    (q : FinitePath
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.graph)
    (hs : q.start ∈
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.source)
    (hpure :
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).IsTargetPure q)
    (i : (canonicalLadder G kappa preferred).groundedInfiniteRecords)
    (hqstart : q.start = .proxy i) {y : V}
    (hqfinish : q.finish = .old y)
    (hiStage :
      (canonicalLadder G kappa preferred).groundedInfiniteStage i = a.1)
    (hmarker : (canonicalLadder G kappa preferred).marker a.1 = some y)
    (htarget : y ∈
      ((canonicalLadder G kappa preferred).splitGroundedPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).targetMarkers) :
    False := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let J := L.splitGroundedPopularAuxiliaryInput hlegal
  change L.freshGroundRecordPath hlegal a = .inr r at hrecord
  change q.start ∈ J.lambda.source at hs
  change J.IsTargetPure q at hpure
  change L.groundedInfiniteStage i = a.1 at hiStage
  change L.marker a.1 = some y at hmarker
  change y ∈ J.targetMarkers at htarget
  have htargetSplit : y ∈ (L.splitPopularAuxiliaryInput hlegal).targetMarkers :=
    groundedTargetMarker_mem_splitTargetMarkers L hlegal htarget
  have hiChosen : L.chosen a.1 = some i.1 := by
    rw [← hiStage]
    exact (L.groundedInfiniteStage_spec i).2
  have hiRecord : i.1 = (Sum.inr r : G.DPath) := by
    apply Option.some.inj
    rw [← hrecord]
    exact hiChosen.symm.trans (L.chosen_freshGroundRecordPath hlegal a)
  have hproxy : J.proxyPath i = (Sum.inr r : G.DPath) := by
    change L.splitGroundedInfinitePath hlegal i = (Sum.inr r : G.DPath)
    simpa only [splitGroundedInfinitePath] using hiRecord
  obtain ⟨z, hzProxy, hrun⟩ :=
    J.decodeWalkSteps_runs_from_eq_proxy q.walk hqstart
      (by rw [hqfinish]; rfl)
  have hzRay : z ∈ r.support := by
    rw [hproxy] at hzProxy
    exact hzProxy
  have hzStrict : z ∈ G.strictRoof
      (G.terminalFrontier (L.arrowPart a.1)) :=
    canonicalLadder_freshRay_support_subset_strictRoof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a r hrecord hzRay
  have hyRoof : y ∈ G.roof
      (G.terminalFrontier (L.arrowPart a.1)) :=
    canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
      preferred hkappa huncountable hNoEnter J rfl a.1 q hs hpure
      hrun hzStrict
  exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter hmarker htargetSplit hyRoof

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_no_freshFinite_grounded_equalTargetPureRoute
#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_no_freshRay_grounded_equalTargetPureRoute
