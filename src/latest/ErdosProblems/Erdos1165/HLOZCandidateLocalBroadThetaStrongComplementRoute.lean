/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongTransportPayment
import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadSourceStrongRoute

/-!
# Candidate-local complement routed to measurable on-time strong payments

The earlier geometric route retained the strong source base but discarded
the target rank-reach and on-time clock.  This version keeps those facts in
each genuine transport branch, so the output is the measurable transported
event whose measure series was proved separately.
-/

open Set

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongComplementRoute

open ExternalProposition44 HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaGeometry.LowGapFailedPair
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaRoute
open HLOZCandidateLocalBroadThetaStrongSourcePaymentSeries
open HLOZCandidateLocalBroadThetaStrongTransportPayment
open HLOZFullBetaRegimeSplit HLOZGapRandomClockScreen
open HLOZLowGapProductEndgame HLOZNoLazyFullBetaProductBranch HLOZPathEvents
open HLOZSourceEndpointTransportTable HLOZThetaOneSourceShift
open HLOZTilingEndpointBandExtraction HLOZTilingGapBandExtraction
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem onTimeProductBetaCandidateLocalComplementEvent_subset_strongOnTime_union_origin
    (t : DominoTiling) {m : ℕ} (hm : 2 ≤ m) :
    onTimeProductBetaCandidateLocalComplementEvent t m (m / 2) ⊆
      candidateLocalBroadStrongSourceOnTimePayment t m ∪
        candidateLocalBroadCheckerOriginPayment t m := by
  intro s hs
  have hdata := mem_onTimeProductBetaCandidateLocalComplementEvent_iff.mp hs
  rcases hdata with ⟨hproduct, hvalid, hlow⟩
  rcases hproduct.2 with ⟨p, j, hfull, hbeta⟩
  let x := s p.nNew
  let o := compatibleOrientation x
  have hwindow : localTime s p.nOld x ∈
      HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m
        (candidateLocalBroadWidth48 m) :=
    selected_mem_broadSourceWindow p (by omega) hfull hbeta
  have hexternal : pathPhasedExternalLocalTime t o s p.nOld x < m / 2 :=
    hlow p j hfull hbeta
  have horientation : OrientationCompatible o x :=
    compatibleOrientation_compatible x
  have hbelow := selected_and_partner_lt_level p
  have holdThree : p.oldRank ≤ 3 := by
    have := p.rank_lt
    have := p.newRank_le_four
    omega
  have holdCutoff : p.nOld ≤ hlozCutoff44 m := by
    rw [← levelCutoffTime_upperTailDelta_eq_hlozCutoff44, ← p.oldClock]
    exact pathTruncatedLevelTime_le m p.oldRank
      (levelCutoffTime upperTailDelta m) s
  by_cases hxbase : IsTilingBase t x
  · have htheta : x ∈ orientedBroadSourceLowThetaStrongBases t o m
        (candidateLocalBroadWidth48 m) (m / 2) s p.nOld :=
      mem_orientedBroadSourceLowThetaStrongBases_of_base hvalid hxbase
        horientation hwindow hexternal hbelow.2
    have hclock : creationTimeNat m p.oldRank s = p.nOld :=
      creationTimeNat_eq_of_creation p.oldCreation
    apply Or.inl
    apply rankPayment_mem_candidateLocal p.oldRank_pos holdThree
    apply transportedBroadStrongSourceOnTimeEvent_mem_rankPayment
      (o := o) (cls := .canonical)
    have htarget : s ∈ broadStrongSourceOnTimeEvent t o m p.oldRank := by
      refine ⟨⟨p.nOld, p.oldCreation.1⟩, ?_, ?_⟩
      · simpa only [hclock] using holdCutoff
      · rw [hclock]
        exact ⟨x, htheta⟩
    simpa only [transportedBroadStrongSourceOnTimeEvent,
      sourceTransportTargetTiling, sourceTransportTargetOrientation,
      sourceTransportPath, Set.mem_preimage, id_eq] using htarget
  · cases t with
    | checker d =>
        let omega := stepsOfWalk s
        have hsEq : trajectory omega = s := hvalid
        have ho : o = .shifted := by
          have hadmissible := checker_admissible_of_class_and_compatible d o
            .opposite x (by simp [dominantEndpointClass, hxbase]) horientation
          exact hadmissible
        by_cases horigin : s ∈ checkerOriginShiftExceptionEvent d m
            p.oldRank (candidateLocalBroadWidth48 m)
        · apply Or.inr
          have horiginOld : m ≤ localTime s p.nOld 0 := by
            change m ≤ localTime s (creationTimeNat m p.oldRank s) 0 at horigin
            rwa [creationTimeNat_eq_of_creation p.oldCreation] at horigin
          rw [candidateLocalBroadCheckerOriginPayment]
          have holdCutoffLevel : p.nOld ≤ levelCutoffTime upperTailDelta m := by
            simpa only [levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
              using holdCutoff
          exact horiginOld.trans
            (localTime_mono_time s 0 holdCutoffLevel)
        · have horiginLt : localTime s p.nOld 0 < m := by
            have h := not_mem_checkerOriginShiftExceptionEvent horigin
            rw [creationTimeNat_eq_of_creation p.oldCreation] at h
            exact h
          have hcreationOmega : ThresholdCreation (trajectory omega) m
              p.oldRank p.nOld := by
            simpa only [hsEq] using p.oldCreation
          have htheta : x - trajectory omega 1 ∈
              orientedBroadSourceLowThetaStrongBases
                (shiftedCheckerTiling d) .even m
                (candidateLocalBroadWidth48 m) (m / 2)
                (oneStepRecenter (trajectory omega)) (p.nOld - 1) := by
            apply
              oppositeChecker_mem_orientedBroadSourceLowThetaStrongBases_oneStepRecenter
                omega d hm p.oldRank_pos hcreationOmega
            · simpa only [hsEq] using hxbase
            · simpa only [hsEq] using hwindow
            · simpa only [hsEq, ho] using hexternal
            · simpa only [hsEq] using hbelow.2
          have hclock : creationTimeNat m p.oldRank
              (oneStepRecenter (trajectory omega)) = p.nOld - 1 := by
            have h := creationTimeNat_oneStepRecenter_eq_pred_of_creation
              omega hm p.oldRank_pos hcreationOmega
                (by simpa only [hsEq] using horiginLt)
            simpa only [hsEq, creationTimeNat_eq_of_creation p.oldCreation]
              using h
          have hNpos := thresholdCreation_time_pos_of_two_le omega hm
            p.oldRank_pos hcreationOmega
          have hshiftCreation : ThresholdCreation
              (oneStepRecenter (trajectory omega)) m p.oldRank
                (p.nOld - 1) := by
            apply thresholdCreation_oneStepRecenter omega (p.nOld - 1) m
              p.oldRank (by omega)
            · simpa only [Nat.sub_add_cancel hNpos] using hcreationOmega
            · simpa only [Nat.sub_add_cancel hNpos, hsEq] using horiginLt
          apply Or.inl
          apply rankPayment_mem_candidateLocal p.oldRank_pos holdThree
          apply transportedBroadStrongSourceOnTimeEvent_mem_rankPayment
            (o := o) (cls := .opposite)
          simp only [transportedBroadStrongSourceOnTimeEvent,
            sourceTransportTargetTiling, sourceTransportTargetOrientation,
            sourceTransportPath, Set.mem_preimage]
          have htarget : oneStepRecenter (trajectory omega) ∈
              broadStrongSourceOnTimeEvent (shiftedCheckerTiling d) .even m
                p.oldRank := by
            refine ⟨⟨p.nOld - 1, hshiftCreation.1⟩, ?_, ?_⟩
            · rw [hclock]
              exact (Nat.sub_le _ _).trans holdCutoff
            · rw [hclock]
              exact ⟨x - trajectory omega 1, htheta⟩
          simpa only [hsEq, shiftedCheckerTarget, shiftedCheckerTiling]
            using htarget
    | evenColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedBroadSourceLowThetaStrongBases
              (reflectedColumnTiling .evenColumns) o m
              (candidateLocalBroadWidth48 m) (m / 2)
              (horizontalReflectPath s) p.nOld :=
          oppositeColumn_mem_orientedBroadSourceLowThetaStrongBases_horizontalReflect
            (t := .evenColumns) trivial o hvalid hxbase horientation
              hwindow hexternal hbelow.2
        have hcreation :=
          (thresholdCreation_horizontalReflectPath s m p.oldRank p.nOld
            (by omega)).2 p.oldCreation
        have hclock : creationTimeNat m p.oldRank (horizontalReflectPath s) =
            p.nOld := creationTimeNat_eq_of_creation hcreation
        apply Or.inl
        apply rankPayment_mem_candidateLocal p.oldRank_pos holdThree
        apply transportedBroadStrongSourceOnTimeEvent_mem_rankPayment
          (o := o) (cls := .opposite)
        simp only [transportedBroadStrongSourceOnTimeEvent,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, Set.mem_preimage]
        change horizontalReflectPath s ∈
          broadStrongSourceOnTimeEvent (reflectedColumnTiling .evenColumns) o m
            p.oldRank
        refine ⟨⟨p.nOld, hcreation.1⟩, ?_, ?_⟩
        · simpa only [hclock] using holdCutoff
        · rw [hclock]
          exact ⟨horizontalReflectPoint x, htheta⟩
    | oddColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedBroadSourceLowThetaStrongBases
              (reflectedColumnTiling .oddColumns) o m
              (candidateLocalBroadWidth48 m) (m / 2)
              (horizontalReflectPath s) p.nOld :=
          oppositeColumn_mem_orientedBroadSourceLowThetaStrongBases_horizontalReflect
            (t := .oddColumns) trivial o hvalid hxbase horientation
              hwindow hexternal hbelow.2
        have hcreation :=
          (thresholdCreation_horizontalReflectPath s m p.oldRank p.nOld
            (by omega)).2 p.oldCreation
        have hclock : creationTimeNat m p.oldRank (horizontalReflectPath s) =
            p.nOld := creationTimeNat_eq_of_creation hcreation
        apply Or.inl
        apply rankPayment_mem_candidateLocal p.oldRank_pos holdThree
        apply transportedBroadStrongSourceOnTimeEvent_mem_rankPayment
          (o := o) (cls := .opposite)
        simp only [transportedBroadStrongSourceOnTimeEvent,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, Set.mem_preimage]
        change horizontalReflectPath s ∈
          broadStrongSourceOnTimeEvent (reflectedColumnTiling .oddColumns) o m
            p.oldRank
        refine ⟨⟨p.nOld, hcreation.1⟩, ?_, ?_⟩
        · simpa only [hclock] using holdCutoff
        · rw [hclock]
          exact ⟨horizontalReflectPoint x, htheta⟩

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongComplementRoute
