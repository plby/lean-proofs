/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadSourceLowThetaGeometry
import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaRoute

/-!
# Candidate-local complement routed to the one-sided broad source screen

Unlike the older global-Theta over-approximation, this payment is exactly the
event tested by `broadSourceThetaCoordinateBad`: the retained external count
is below the displayed candidate threshold.
-/

open Set

namespace Erdos1165.HLOZCandidateLocalBroadSourceLowThetaRoute

open HLOZCandidateLocalBroadSourceLowThetaGeometry
open HLOZCandidateLocalBroadThetaGeometry
open HLOZCandidateLocalBroadThetaGeometry.LowGapFailedPair
open HLOZCandidateLocalBroadThetaProduct HLOZCandidateLocalBroadThetaRoute
open HLOZFullBetaRegimeSplit HLOZGapRandomClockScreen
open HLOZNoLazyFullBetaProductBranch HLOZPathEvents
open HLOZSourceEndpointTransportTable HLOZThetaOneSourceShift
open HLOZTilingEndpointBandExtraction HLOZTilingGapBandExtraction
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def broadSourceLowThetaTransportRow
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m rank externalThreshold : ℕ) : Set WalkPath :=
  {s | (orientedBroadSourceLowThetaBases
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls)
      m (candidateLocalBroadWidth48 m) externalThreshold
      (sourceTransportPath t cls s)
      (creationTimeNat m rank (sourceTransportPath t cls s))).Nonempty}

def candidateLocalBroadSourceLowThetaPayment
    (t : DominoTiling) (m externalThreshold : ℕ) : Set WalkPath :=
  ⋃ rank : Fin 3, ⋃ o : Orientation, ⋃ cls : DominantEndpointClass,
    broadSourceLowThetaTransportRow t o cls m (rank + 1) externalThreshold

theorem onTimeProductBetaCandidateLocalComplementEvent_subset_lowTheta_union_origin
    (t : DominoTiling) {m externalThreshold : ℕ} (hm : 2 ≤ m) :
    onTimeProductBetaCandidateLocalComplementEvent t m externalThreshold ⊆
      candidateLocalBroadSourceLowThetaPayment t m externalThreshold ∪
        candidateLocalBroadCheckerOriginPayment t m := by
  intro s hs
  have hdata :=
    (mem_onTimeProductBetaCandidateLocalComplementEvent_iff.mp hs)
  rcases hdata with ⟨hproduct, hvalid, hlow⟩
  rcases hproduct.2 with ⟨p, j, hfull, hbeta⟩
  let x := s p.nNew
  let o := compatibleOrientation x
  let cls := dominantEndpointClass t x
  have hwindow : localTime s p.nOld x ∈
      HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m
        (candidateLocalBroadWidth48 m) :=
    selected_mem_broadSourceWindow p (by omega) hfull hbeta
  have hexternal : pathPhasedExternalLocalTime t o s p.nOld x <
      externalThreshold := hlow p j hfull hbeta
  have horientation : OrientationCompatible o x :=
    compatibleOrientation_compatible x
  have hrankFin : p.oldRank - 1 < 3 := by
    have holdThree : p.oldRank ≤ 3 := by
      have := p.rank_lt
      have := p.newRank_le_four
      omega
    omega
  let rank : Fin 3 := ⟨p.oldRank - 1, hrankFin⟩
  have hrank : (rank : ℕ) + 1 = p.oldRank := by
    change p.oldRank - 1 + 1 = p.oldRank
    have := p.oldRank_pos
    omega
  by_cases hxbase : IsTilingBase t x
  · have htheta : x ∈ orientedBroadSourceLowThetaBases t o m
        (candidateLocalBroadWidth48 m) externalThreshold s p.nOld :=
      mem_orientedBroadSourceLowThetaBases_of_base hvalid hxbase
        horientation hwindow hexternal
    have hclock : creationTimeNat m p.oldRank s = p.nOld :=
      creationTimeNat_eq_of_creation p.oldCreation
    apply Or.inl
    rw [candidateLocalBroadSourceLowThetaPayment]
    refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
      Set.mem_iUnion.mpr ⟨.canonical, ?_⟩⟩⟩
    simp only [broadSourceLowThetaTransportRow, Set.mem_ofPred_eq,
      sourceTransportTargetTiling, sourceTransportTargetOrientation,
      sourceTransportPath, id_eq, hrank, hclock]
    exact ⟨x, htheta⟩
  · cases t with
    | checker d =>
        let omega := stepsOfWalk s
        have hsEq : trajectory omega = s := hvalid
        have ho : o = .shifted := by
          have hadmissible := checker_admissible_of_class_and_compatible d o
            .opposite x (by simp [dominantEndpointClass, hxbase])
              horientation
          exact hadmissible
        by_cases horigin : s ∈ checkerOriginShiftExceptionEvent d m
            p.oldRank (candidateLocalBroadWidth48 m)
        · apply Or.inr
          have horiginOld : m ≤ localTime s p.nOld 0 := by
            change m ≤ localTime s (creationTimeNat m p.oldRank s) 0 at horigin
            rwa [creationTimeNat_eq_of_creation p.oldCreation] at horigin
          have holdCutoff : p.nOld ≤ levelCutoffTime upperTailDelta m := by
            rw [← p.oldClock]
            exact pathTruncatedLevelTime_le m p.oldRank
              (levelCutoffTime upperTailDelta m) s
          rw [candidateLocalBroadCheckerOriginPayment]
          exact horiginOld.trans (localTime_mono_time s 0 holdCutoff)
        · have horiginLt : localTime s p.nOld 0 < m := by
            have h := not_mem_checkerOriginShiftExceptionEvent horigin
            rw [creationTimeNat_eq_of_creation p.oldCreation] at h
            exact h
          have htheta : x - trajectory omega 1 ∈
              orientedBroadSourceLowThetaBases (shiftedCheckerTiling d) .even
                m (candidateLocalBroadWidth48 m) externalThreshold
                (oneStepRecenter (trajectory omega)) (p.nOld - 1) := by
            apply
              oppositeChecker_mem_orientedBroadSourceLowThetaBases_oneStepRecenter
                omega d hm p.oldRank_pos
            · simpa only [hsEq] using p.oldCreation
            · simpa only [hsEq] using hxbase
            · simpa only [hsEq] using hwindow
            · simpa only [hsEq, ho] using hexternal
          have hclock : creationTimeNat m p.oldRank
              (oneStepRecenter (trajectory omega)) = p.nOld - 1 := by
            have h := creationTimeNat_oneStepRecenter_eq_pred_of_creation
              omega hm p.oldRank_pos (by simpa only [hsEq] using p.oldCreation)
                (by simpa only [hsEq] using horiginLt)
            simpa only [hsEq, creationTimeNat_eq_of_creation p.oldCreation]
              using h
          apply Or.inl
          rw [candidateLocalBroadSourceLowThetaPayment]
          refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
            Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
          simp only [broadSourceLowThetaTransportRow, Set.mem_ofPred_eq,
            sourceTransportTargetTiling, sourceTransportTargetOrientation,
            sourceTransportPath, hrank, ← hsEq, hclock]
          exact ⟨x - trajectory omega 1, htheta⟩
    | evenColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedBroadSourceLowThetaBases
              (reflectedColumnTiling .evenColumns) o m
              (candidateLocalBroadWidth48 m) externalThreshold
              (horizontalReflectPath s) p.nOld :=
          oppositeColumn_mem_orientedBroadSourceLowThetaBases_horizontalReflect
            (t := .evenColumns) trivial o hvalid hxbase horientation
              hwindow hexternal
        have hcreation :=
          (thresholdCreation_horizontalReflectPath s m p.oldRank p.nOld
            (by omega)).2 p.oldCreation
        have hclock : creationTimeNat m p.oldRank (horizontalReflectPath s) =
            p.nOld := creationTimeNat_eq_of_creation hcreation
        apply Or.inl
        rw [candidateLocalBroadSourceLowThetaPayment]
        refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
          Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
        simp only [broadSourceLowThetaTransportRow, Set.mem_ofPred_eq,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, hrank, hclock]
        exact ⟨horizontalReflectPoint x, htheta⟩
    | oddColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedBroadSourceLowThetaBases
              (reflectedColumnTiling .oddColumns) o m
              (candidateLocalBroadWidth48 m) externalThreshold
              (horizontalReflectPath s) p.nOld :=
          oppositeColumn_mem_orientedBroadSourceLowThetaBases_horizontalReflect
            (t := .oddColumns) trivial o hvalid hxbase horientation
              hwindow hexternal
        have hcreation :=
          (thresholdCreation_horizontalReflectPath s m p.oldRank p.nOld
            (by omega)).2 p.oldCreation
        have hclock : creationTimeNat m p.oldRank (horizontalReflectPath s) =
            p.nOld := creationTimeNat_eq_of_creation hcreation
        apply Or.inl
        rw [candidateLocalBroadSourceLowThetaPayment]
        refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
          Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
        simp only [broadSourceLowThetaTransportRow, Set.mem_ofPred_eq,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, hrank, hclock]
        exact ⟨horizontalReflectPoint x, htheta⟩

end

end Erdos1165.HLOZCandidateLocalBroadSourceLowThetaRoute
