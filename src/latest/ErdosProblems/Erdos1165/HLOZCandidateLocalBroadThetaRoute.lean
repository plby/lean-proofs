/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaGeometry
import ErdosProblems.Erdos1165.HLOZCheckerOriginShiftPayment
import ErdosProblems.Erdos1165.HLOZSourceEndpointTransportTable

/-!
# Candidate-local complement routes to broad global Theta

The no-lazy product complement says that every selected low-beta failed-pair
endpoint has phased external count below the requested threshold.  Such an
endpoint belongs to a broad global Theta slice after the finite endpoint
transport.  This file packages the deterministic finite union.  Checker
one-step recentering has the already named origin obstruction; column
reflection has none.
-/

open Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaRoute

open HLOZCandidateLocalBroadThetaGeometry
open HLOZCandidateLocalBroadThetaGeometry.LowGapFailedPair
open HLOZCandidateLocalBroadThetaProduct HLOZFullBetaRegimeSplit
open HLOZCheckerOriginShiftPayment
open HLOZGapRandomClockScreen
open HLOZNoLazyFullBetaProductBranch HLOZPathEvents
open HLOZSourceEndpointTransportTable HLOZSourceOrientedThetaBalance
open HLOZThetaOneSourceShift HLOZTilingEndpointBandExtraction
open HLOZTilingGapBandExtraction
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One transported broad global-Theta row. -/
def broadGlobalThetaTransportRow
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m rank externalThreshold : ℕ) : Set WalkPath :=
  {s | (orientedGlobalThetaBases
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls)
      m (candidateLocalBroadWidth48 m) externalThreshold
      (externalThreshold + 1) (sourceTransportPath t cls s)
      (creationTimeNat m rank (sourceTransportPath t cls s))).Nonempty}

/-- The finite three-rank, two-orientation, two-spatial-class broad payment. -/
def candidateLocalBroadGlobalThetaPayment
    (t : DominoTiling) (m externalThreshold : ℕ) : Set WalkPath :=
  ⋃ rank : Fin 3, ⋃ o : Orientation, ⋃ cls : DominantEndpointClass,
    broadGlobalThetaTransportRow t o cls m (rank + 1) externalThreshold

/-- The on-time checker obstruction, paid at the deterministic cutoff. -/
def candidateLocalBroadCheckerOriginPayment
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  match t with
  | .checker _ => cutoffOriginLocalTimeEvent m
  | .evenColumns | .oddColumns => ∅

private theorem orientationCompatible_reflect
    (o : Orientation) (x : Point) :
    OrientationCompatible o (horizontalReflectPoint x) ↔
      OrientationCompatible o x := by
  cases o <;> rcases x with ⟨x₁, x₂⟩ <;>
    simp [OrientationCompatible, EvenPoint, OddPoint, pointParity,
      horizontalReflectPoint]

/-- Every valid low-beta product path whose selected endpoints all miss the
external threshold lies in the finite broad global-Theta payment, except for
the explicit checker-origin obstruction. -/
theorem onTimeProductBetaCandidateLocalComplementEvent_subset_broadTheta_union_origin
    (t : DominoTiling) {m externalThreshold : ℕ} (hm : 2 ≤ m) :
    onTimeProductBetaCandidateLocalComplementEvent t m externalThreshold ⊆
      candidateLocalBroadGlobalThetaPayment t m externalThreshold ∪
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
        (candidateLocalBroadWidth48 m) := by
    exact selected_mem_broadSourceWindow p (by omega) hfull hbeta
  have hexternal : pathPhasedExternalLocalTime t o s p.nOld x <
      externalThreshold := by
    exact hlow p j hfull hbeta
  have horientation : OrientationCompatible o x := by
    exact compatibleOrientation_compatible x
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
  · have hcls : cls = .canonical := by
      simp [cls, dominantEndpointClass, hxbase]
    have htheta : x ∈ orientedGlobalThetaBases t o m
        (candidateLocalBroadWidth48 m) externalThreshold
        (externalThreshold + 1) s p.nOld :=
      mem_orientedGlobalThetaBases_of_base_sourceWindow_external_lt
        hvalid hxbase horientation hwindow hexternal
    have hclock : creationTimeNat m p.oldRank s = p.nOld :=
      creationTimeNat_eq_of_creation p.oldCreation
    apply Or.inl
    rw [candidateLocalBroadGlobalThetaPayment]
    refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
      Set.mem_iUnion.mpr ⟨.canonical, ?_⟩⟩⟩
    simp only [broadGlobalThetaTransportRow, Set.mem_ofPred_eq,
      sourceTransportTargetTiling, sourceTransportTargetOrientation,
      sourceTransportPath, id_eq, hrank, hclock]
    exact ⟨x, htheta⟩
  · have hcls : cls = .opposite := by
      simp [cls, dominantEndpointClass, hxbase]
    cases t with
    | checker d =>
        let omega := stepsOfWalk s
        have hsEq : trajectory omega = s := hvalid
        have ho : o = .shifted := by
          have hadmissible := checker_admissible_of_class_and_compatible d o
            .opposite x (by simpa only [cls] using hcls) horientation
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
              orientedGlobalThetaBases (shiftedCheckerTiling d) .even m
                (candidateLocalBroadWidth48 m) externalThreshold
                (externalThreshold + 1)
                (oneStepRecenter (trajectory omega)) (p.nOld - 1) := by
            apply oppositeChecker_mem_orientedGlobalThetaBases_oneStepRecenter
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
          rw [candidateLocalBroadGlobalThetaPayment]
          refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
            Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
          simp only [broadGlobalThetaTransportRow, Set.mem_ofPred_eq,
            sourceTransportTargetTiling, sourceTransportTargetOrientation,
            sourceTransportPath, hrank, ← hsEq, hclock]
          exact ⟨x - trajectory omega 1, htheta⟩
    | evenColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedGlobalThetaBases (reflectedColumnTiling .evenColumns) o m
              (candidateLocalBroadWidth48 m) externalThreshold
              (externalThreshold + 1) (horizontalReflectPath s) p.nOld :=
          oppositeColumn_mem_orientedGlobalThetaBases_horizontalReflect
            (t := .evenColumns) trivial o hvalid hxbase horientation
              hwindow hexternal
        have hcreation :=
          (thresholdCreation_horizontalReflectPath s m p.oldRank p.nOld
            (by omega)).2 p.oldCreation
        have hclock : creationTimeNat m p.oldRank (horizontalReflectPath s) =
            p.nOld := creationTimeNat_eq_of_creation hcreation
        apply Or.inl
        rw [candidateLocalBroadGlobalThetaPayment]
        refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
          Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
        simp only [broadGlobalThetaTransportRow, Set.mem_ofPred_eq,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, hrank, hclock]
        exact ⟨horizontalReflectPoint x, htheta⟩
    | oddColumns =>
        have htheta : horizontalReflectPoint x ∈
            orientedGlobalThetaBases (reflectedColumnTiling .oddColumns) o m
              (candidateLocalBroadWidth48 m) externalThreshold
              (externalThreshold + 1) (horizontalReflectPath s) p.nOld :=
          oppositeColumn_mem_orientedGlobalThetaBases_horizontalReflect
            (t := .oddColumns) trivial o hvalid hxbase horientation
              hwindow hexternal
        have hcreation :=
          (thresholdCreation_horizontalReflectPath s m p.oldRank p.nOld
            (by omega)).2 p.oldCreation
        have hclock : creationTimeNat m p.oldRank (horizontalReflectPath s) =
            p.nOld := creationTimeNat_eq_of_creation hcreation
        apply Or.inl
        rw [candidateLocalBroadGlobalThetaPayment]
        refine Set.mem_iUnion.mpr ⟨rank, Set.mem_iUnion.mpr ⟨o,
          Set.mem_iUnion.mpr ⟨.opposite, ?_⟩⟩⟩
        simp only [broadGlobalThetaTransportRow, Set.mem_ofPred_eq,
          sourceTransportTargetTiling, sourceTransportTargetOrientation,
          sourceTransportPath, hrank, hclock]
        exact ⟨horizontalReflectPoint x, htheta⟩

/-- The checker-origin part of the candidate-local complement has a finite
measure series without a lower-deviation premise: its creation clock was
already truncated at the deterministic cutoff. -/
theorem simpleRandomWalk_candidateLocalBroadCheckerOriginPayment_series_ne_top
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalBroadCheckerOriginPayment t m) ≠ ∞ := by
  cases t with
  | checker d =>
      simpa only [candidateLocalBroadCheckerOriginPayment] using
        simpleRandomWalk_cutoffOriginLocalTimeEvent_series_ne_top
  | evenColumns => simp [candidateLocalBroadCheckerOriginPayment]
  | oddColumns => simp [candidateLocalBroadCheckerOriginPayment]

end

end Erdos1165.HLOZCandidateLocalBroadThetaRoute
