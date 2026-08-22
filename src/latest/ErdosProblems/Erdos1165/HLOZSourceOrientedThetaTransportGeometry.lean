/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZRawShellCreationBridge
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaTransportPayment

/-!
# Orientation-refined endpoint transport geometry

The older source transport bounds the unfiltered dominant family.  The
source atoms are indexed by the temporal orientation of the dominant
endpoint, so the cardinal transport must preserve that filter.  Checker
opposite endpoints all enter the even target chain after one-step
recentering; horizontal reflection preserves the orientation class for the
column pair.
-/

open Set

namespace Erdos1165.HLOZSourceOrientedThetaTransportGeometry

open HLOZPathEvents HLOZRawShellCreationBridge
open HLOZShellZeroReplacementWindows HLOZSourceEndpointTransportTable
open HLOZThetaOneSourceShift HLOZThetaSourceBalance
open LazyDecomposition PreStoppingSpatialLaw SpatialInsertionFiber
open TilingLazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem orientedCanonicalDominantNearBasesAtCreation_eq_vTwo
    (t : DominoTiling) (o : Orientation) (m k w : ℕ) (s : WalkPath)
    (hnext : thresholdCount s (creationTimeNat m k s) (m + 1) = 0) :
    orientedCanonicalDominantNearBasesAtCreation t o m k w s =
      orientedTilingVTwoAtCreation t o m k w s := by
  unfold orientedCanonicalDominantNearBasesAtCreation
  rw [tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_of_next_zero
    t m k w s hnext]
  rfl

private theorem checker_vTwoAtCreation_eq_orientedEven
    (d : Tilings.CheckerDirection) (m k w : ℕ) (s : WalkPath) :
    tilingVTwoAtCreation (.checker d) m k w s =
      orientedTilingVTwoAtCreation (.checker d) .even m k w s := by
  classical
  ext b
  rw [orientedTilingVTwoAtCreation, mem_orientedTilingVTwoBases_iff]
  constructor
  · intro hb
    refine ⟨hb, ?_⟩
    rw [tilingVTwoAtCreation, tilingVTwoBases, Finset.mem_filter] at hb
    have hbbase := isTilingBase_of_mem_visitedTilingBases hb.1
    simpa only [OrientationCompatible, IsTilingBase, canonicalEastTiling]
      using (isTilingBase_canonicalEast_iff_evenPoint b).mp hbbase
  · exact fun hb ↦ hb.1

theorem orientedOppositeChecker_card_le_shifted_vTwoAtCreation
    (omega : StepPath) (d : Tilings.CheckerDirection) (o : Orientation)
    {m k w N : ℕ} (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k N)
    (hnext : thresholdCount (trajectory omega) N (m + 1) = 0)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m k w) :
    (orientedOppositeDominantNearEndpointsAtCreation (.checker d) o m k w
        (trajectory omega)).card ≤
      (orientedTilingVTwoAtCreation (shiftedCheckerTiling d) .even m k w
        (oneStepRecenter (trajectory omega))).card := by
  classical
  cases o with
  | even =>
      have hempty : orientedOppositeDominantNearEndpointsAtCreation
          (.checker d) .even m k w (trajectory omega) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rw [orientedOppositeDominantNearEndpointsAtCreation,
          Finset.mem_filter, tilingOppositeDominantNearEndpointsAtCreation,
          Finset.mem_filter] at hx
        have hclass : dominantEndpointClass (.checker d) x = .opposite := by
          simp [dominantEndpointClass, hx.1.2]
        have hadmissible := checker_admissible_of_class_and_compatible d
          .even .opposite x hclass hx.2
        exact Orientation.noConfusion hadmissible
      rw [hempty]
      simp
  | shifted =>
      calc
        (orientedOppositeDominantNearEndpointsAtCreation (.checker d)
            .shifted m k w (trajectory omega)).card ≤
          (tilingOppositeDominantNearEndpointsAtCreation (.checker d)
            m k w (trajectory omega)).card := Finset.card_filter_le _ _
        _ ≤ (tilingVTwoAtCreation (shiftedCheckerTiling d) m k w
            (oneStepRecenter (trajectory omega))).card :=
          oppositeDominant_card_le_shifted_vTwoAtCreation omega d hm hk
            hcreation hnext hgoodOrigin
        _ = (orientedTilingVTwoAtCreation (shiftedCheckerTiling d) .even
            m k w (oneStepRecenter (trajectory omega))).card := by
          simpa only [shiftedCheckerTiling] using congrArg Finset.card
            (checker_vTwoAtCreation_eq_orientedEven (oppositeDirection d)
              m k w (oneStepRecenter (trajectory omega)))

theorem orientationCompatible_horizontalReflectPoint_iff
    (o : Orientation) (x : Point) :
    OrientationCompatible o (horizontalReflectPoint x) ↔
      OrientationCompatible o x := by
  cases o <;> rcases x with ⟨x₁, x₂⟩ <;>
    simp [OrientationCompatible, EvenPoint, OddPoint, pointParity,
      horizontalReflectPoint]

theorem orientedOppositeColumn_card_le_reflected_vTwoAtCreation
    {t : DominoTiling} (ht : IsColumnTiling t) (o : Orientation)
    (s : WalkPath) {m k w N : ℕ} (hm : 0 < m)
    (hcreation : ThresholdCreation s m k N)
    (hnext : thresholdCount s N (m + 1) = 0) :
    (orientedOppositeDominantNearEndpointsAtCreation t o m k w s).card ≤
      (orientedTilingVTwoAtCreation (reflectedColumnTiling t) o
        m k w (horizontalReflectPath s)).card := by
  classical
  have hreflectCreation :=
    (thresholdCreation_horizontalReflectPath s m k N hm).2 hcreation
  have hclock : creationTimeNat m k s = N :=
    creationTimeNat_eq_of_creation hcreation
  have hreflectClock :
      creationTimeNat m k (horizontalReflectPath s) = N :=
    creationTimeNat_eq_of_creation hreflectCreation
  let S := orientedOppositeDominantNearEndpointsAtCreation t o m k w s
  have hsub : S.image horizontalReflectPoint ⊆
      orientedTilingVTwoAtCreation (reflectedColumnTiling t) o
        m k w (horizontalReflectPath s) := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    have hxS' := hxS
    dsimp only [S] at hxS'
    rw [orientedOppositeDominantNearEndpointsAtCreation,
      Finset.mem_filter, tilingOppositeDominantNearEndpointsAtCreation,
      Finset.mem_filter] at hxS'
    rcases hxS' with ⟨⟨hxDominantFamily, hxNotBase⟩, hxOrientation⟩
    rw [tilingDominantNearBasesAtCreation, Finset.mem_image] at hxDominantFamily
    obtain ⟨b, hbNear, hbx⟩ := hxDominantFamily
    have hbNear' := hbNear
    rw [tilingNearFavoriteBasesAtCreation, Finset.mem_filter] at hbNear'
    rw [hclock] at hbx hbNear'
    have hxDominance := tilingDominantEndpointAt_partner_le t s N b
    rw [hbx] at hxDominance
    have hxNear : tilingXiPlusAt t s N x ∈
        shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w := by
      rw [← hbx, tilingXiPlusAt_dominantEndpoint]
      exact hbNear'.2
    have hmaxLt := (thresholdCount_eq_zero_iff_forall_lt
      s N (m + 1) (by omega)).mp hnext
    have hxSource : localTime s N x ∈ shellZeroSourceTotalWindow m w := by
      rw [tilingXiPlusAt_eq_base_of_partner_le hxDominance] at hxNear
      rw [Finset.mem_union] at hxNear
      rcases hxNear with hsource | hreplacement
      · exact hsource
      · have hge := (mem_shellZeroReplacementTotalWindow.mp hreplacement).1
        have hlt := hmaxLt x
        omega
    have hxVTwo : tilingVTwoAt (reflectedColumnTiling t)
        (shellZeroSourceTotalWindow m w) (horizontalReflectPath s) N
          (horizontalReflectPoint x) := by
      rw [tilingVTwoAt_horizontalReflectPath_iff ht]
      exact ⟨hxDominance, hxSource⟩
    rw [orientedTilingVTwoAtCreation, hreflectClock,
      mem_orientedTilingVTwoBases_iff, tilingVTwoBases,
      Finset.mem_filter]
    refine ⟨⟨?_, hxVTwo⟩, ?_⟩
    · rw [visitedTilingBases, Finset.mem_image]
      refine ⟨horizontalReflectPoint x, ?_, ?_⟩
      · rw [mem_visitedSites_iff_localTime_pos,
          localTime_horizontalReflectPath]
        have hxlower := (mem_shellZeroSourceTotalWindow.mp hxSource).1
        omega
      · rw [tilingBase, if_pos
          ((isTilingBase_reflectedColumn_iff_not ht x).2 hxNotBase)]
    · exact (orientationCompatible_horizontalReflectPoint_iff o x).2
        hxOrientation
  calc
    S.card = (S.image horizontalReflectPoint).card :=
      (Finset.card_image_of_injective S
        (Function.Involutive.injective
          horizontalReflectPoint_involutive)).symm
    _ ≤ _ := Finset.card_le_card hsub

end

end Erdos1165.HLOZSourceOrientedThetaTransportGeometry
