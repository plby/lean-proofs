/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadSourceLowThetaRoute

/-!
# Strong one-sided candidate-local source route

The actual-endpoint-increment carrier needs both endpoints of the selected
source domino below level `m`.  This module retains that fact in the physical
payment event and proves it survives the genuine checker recentering and
column reflection transports.
-/

open Set

namespace Erdos1165.HLOZCandidateLocalBroadSourceStrongRoute

open HLOZCandidateLocalBroadSourceLowThetaGeometry
open HLOZCandidateLocalBroadThetaGeometry
open HLOZCandidateLocalBroadThetaGeometry.LowGapFailedPair
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaRoute
open HLOZFullBetaRegimeSplit HLOZGapRandomClockScreen
open HLOZNoLazyFullBetaProductBranch HLOZPathEvents
open HLOZSourceEndpointTransportTable HLOZThetaOneSourceShift
open HLOZTilingEndpointBandExtraction HLOZTilingGapBandExtraction
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One-sided broad source bases with the additional honest source-rank
condition on the mate endpoint. -/
def orientedBroadSourceLowThetaStrongBases
    (t : DominoTiling) (o : Orientation)
    (m width externalThreshold : ℕ) (s : WalkPath) (n : ℕ) : Finset Point := by
  classical
  exact (orientedBroadSourceLowThetaBases t o m width externalThreshold s n).filter
    fun b ↦ localTime s n (tilingPartner t b) < m

theorem mem_orientedBroadSourceLowThetaStrongBases_of_base
    {t : DominoTiling} {o : Orientation}
    {m width externalThreshold n : ℕ} {s : WalkPath} {b : Point}
    (hvalid : s ∈ validStepWalk)
    (hbase : IsTilingBase t b)
    (hcompatible : OrientationCompatible o b)
    (hwindow : localTime s n b ∈
      HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime t o s n b < externalThreshold)
    (hpartner : localTime s n (tilingPartner t b) < m) :
    b ∈ orientedBroadSourceLowThetaStrongBases t o m width
      externalThreshold s n := by
  rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter]
  exact ⟨mem_orientedBroadSourceLowThetaBases_of_base hvalid hbase hcompatible
    hwindow hexternal, hpartner⟩

theorem oppositeChecker_mem_orientedBroadSourceLowThetaStrongBases_oneStepRecenter
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k n width externalThreshold : ℕ} {x : Point}
    (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hxbase : ¬ IsTilingBase (.checker d) x)
    (hwindow : localTime (trajectory omega) n x ∈
      HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime (.checker d) .shifted
      (trajectory omega) n x < externalThreshold)
    (hpartner : localTime (trajectory omega) n
      (tilingPartner (.checker d) x) < m) :
    x - trajectory omega 1 ∈
      orientedBroadSourceLowThetaStrongBases (shiftedCheckerTiling d) .even
        m width externalThreshold (oneStepRecenter (trajectory omega))
        (n - 1) := by
  rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter]
  refine ⟨oppositeChecker_mem_orientedBroadSourceLowThetaBases_oneStepRecenter
    omega d hm hk hcreation hxbase hwindow hexternal, ?_⟩
  have hn : 0 < n :=
    thresholdCreation_time_pos_of_two_le omega hm hk hcreation
  have hnPred : n - 1 + 1 = n := by omega
  rw [tilingPartner_shiftedChecker_sub omega d x hxbase]
  by_cases hpartnerZero : tilingPartner (.checker d) x = 0
  · rw [hpartnerZero]
    rw [hpartnerZero] at hpartner
    have horigin := localTime_oneStepRecenter_origin_add_one omega (n - 1)
    rw [hnPred] at horigin
    omega
  · rw [localTime_oneStepRecenter_eq_of_ne_origin omega (n - 1)
      (tilingPartner (.checker d) x) hpartnerZero, hnPred]
    exact hpartner

theorem oppositeColumn_mem_orientedBroadSourceLowThetaStrongBases_horizontalReflect
    {t : DominoTiling} (ht : IsColumnTiling t) (o : Orientation)
    {m n width externalThreshold : ℕ} {s : WalkPath} {x : Point}
    (hvalid : s ∈ validStepWalk)
    (hxbase : ¬ IsTilingBase t x)
    (hcompatible : OrientationCompatible o x)
    (hwindow : localTime s n x ∈
      HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime t o s n x < externalThreshold)
    (hpartner : localTime s n (tilingPartner t x) < m) :
    horizontalReflectPoint x ∈
      orientedBroadSourceLowThetaStrongBases (reflectedColumnTiling t) o
        m width externalThreshold (horizontalReflectPath s) n := by
  rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter]
  refine ⟨oppositeColumn_mem_orientedBroadSourceLowThetaBases_horizontalReflect
    ht o hvalid hxbase hcompatible hwindow hexternal, ?_⟩
  rw [tilingPartner_reflectedColumn ht, localTime_horizontalReflectPath]
  exact hpartner

def broadSourceLowThetaStrongTransportRow
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m rank externalThreshold : ℕ) : Set WalkPath :=
  {s | (orientedBroadSourceLowThetaStrongBases
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls)
      m (candidateLocalBroadWidth48 m) externalThreshold
      (sourceTransportPath t cls s)
      (creationTimeNat m rank (sourceTransportPath t cls s))).Nonempty}

def candidateLocalBroadSourceLowThetaStrongPayment
    (t : DominoTiling) (m externalThreshold : ℕ) : Set WalkPath :=
  ⋃ rank : Fin 3, ⋃ o : Orientation, ⋃ cls : DominantEndpointClass,
    broadSourceLowThetaStrongTransportRow t o cls m (rank + 1)
      externalThreshold

theorem onTimeProductBetaCandidateLocalComplementEvent_subset_strong_lowTheta_union_origin
    (t : DominoTiling) {m externalThreshold : ℕ} (hm : 2 ≤ m) :
    onTimeProductBetaCandidateLocalComplementEvent t m externalThreshold ⊆
      candidateLocalBroadSourceLowThetaStrongPayment t m externalThreshold ∪
        candidateLocalBroadCheckerOriginPayment t m := by
  intro s hs
  have hdata := mem_onTimeProductBetaCandidateLocalComplementEvent_iff.mp hs
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
  have hbelow := selected_and_partner_lt_level p
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
  · have htheta : x ∈ orientedBroadSourceLowThetaStrongBases t o m
        (candidateLocalBroadWidth48 m) externalThreshold s p.nOld :=
      mem_orientedBroadSourceLowThetaStrongBases_of_base hvalid hxbase
        horientation hwindow hexternal hbelow.2
    have hclock : creationTimeNat m p.oldRank s = p.nOld :=
      creationTimeNat_eq_of_creation p.oldCreation
    apply Or.inl
    rw [candidateLocalBroadSourceLowThetaStrongPayment]
    refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
      Set.mem_iUnion.mpr ⟨.canonical, ?_⟩⟩⟩
    simp only [broadSourceLowThetaStrongTransportRow, Set.mem_ofPred_eq,
      sourceTransportTargetTiling, sourceTransportTargetOrientation,
      sourceTransportPath, id_eq, hrank, hclock]
    exact ⟨x, htheta⟩
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
              orientedBroadSourceLowThetaStrongBases
                (shiftedCheckerTiling d) .even m
                (candidateLocalBroadWidth48 m) externalThreshold
                (oneStepRecenter (trajectory omega)) (p.nOld - 1) := by
            apply
              oppositeChecker_mem_orientedBroadSourceLowThetaStrongBases_oneStepRecenter
                omega d hm p.oldRank_pos
            · simpa only [hsEq] using p.oldCreation
            · simpa only [hsEq] using hxbase
            · simpa only [hsEq] using hwindow
            · simpa only [hsEq, ho] using hexternal
            · simpa only [hsEq] using hbelow.2
          have hclock : creationTimeNat m p.oldRank
              (oneStepRecenter (trajectory omega)) = p.nOld - 1 := by
            have h := creationTimeNat_oneStepRecenter_eq_pred_of_creation
              omega hm p.oldRank_pos (by simpa only [hsEq] using p.oldCreation)
                (by simpa only [hsEq] using horiginLt)
            simpa only [hsEq, creationTimeNat_eq_of_creation p.oldCreation]
              using h
          apply Or.inl
          rw [candidateLocalBroadSourceLowThetaStrongPayment]
          refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
            Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
          simp only [broadSourceLowThetaStrongTransportRow, Set.mem_ofPred_eq,
            sourceTransportTargetTiling, sourceTransportTargetOrientation,
            sourceTransportPath, hrank, ← hsEq, hclock]
          exact ⟨x - trajectory omega 1, htheta⟩
    | evenColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedBroadSourceLowThetaStrongBases
              (reflectedColumnTiling .evenColumns) o m
              (candidateLocalBroadWidth48 m) externalThreshold
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
        rw [candidateLocalBroadSourceLowThetaStrongPayment]
        refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
          Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
        simp only [broadSourceLowThetaStrongTransportRow, Set.mem_ofPred_eq,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, hrank, hclock]
        exact ⟨horizontalReflectPoint x, htheta⟩
    | oddColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedBroadSourceLowThetaStrongBases
              (reflectedColumnTiling .oddColumns) o m
              (candidateLocalBroadWidth48 m) externalThreshold
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
        rw [candidateLocalBroadSourceLowThetaStrongPayment]
        refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
          Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
        simp only [broadSourceLowThetaStrongTransportRow, Set.mem_ofPred_eq,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, hrank, hclock]
        exact ⟨horizontalReflectPoint x, htheta⟩

end

end Erdos1165.HLOZCandidateLocalBroadSourceStrongRoute
