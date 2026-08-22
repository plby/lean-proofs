/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairHarmonic
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairPhysicalBalance
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSourceCapCover
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaPositiveSlotProduct

/-!
# Harmonic payment for raw positive-prefix interface growth

The raw adjacent-row growth event is covered by its canonical exact-pair
source cap.  On the positive-prefix branch, canonical external-code recovery
supplies the fixed-prefix hypothesis needed by the actual-rank replacement.
Physical balance restricts from the broad support to the exact pair support,
so the variable-rank harmonic theorem applies directly.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairRawHarmonic

open HLOZAllSixBandProductClosure
open HLOZDynamicThresholdedScreening
open HLOZGapRandomClockScreen
open HLOZPathEvents
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairHarmonic
open HLOZPositiveInterfacePairPhysicalBalance
open HLOZPositiveInterfacePairSourceCapCover
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePhysicalBalanceData
open HLOZProposition48Candidates
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaPositiveSlotProduct
open HLOZVariableDeltaHistoryCapSummation
open LazyDecomposition
open NearFavoriteThresholded
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One fixed-clock raw adjacent-shell growth event on the branch where the
deleted external creation prefix is physically nonempty. -/
def positiveInterfacePositiveRawGrowthEvent
    (t : DominoTiling) (m cutoff n : ℕ) (band : RandomClockBand)
    (threshold : ℕ → ℕ) (shell : ℕ) : Set WalkPath :=
  {s |
    ThresholdCreation s m band.oldRank n ∧
      thresholdCount s n (m + 1) = 0 ∧
      s ∈ validStepWalk ∧
      s ∈ thresholdedGrowthFailure
        (tilingBandOccupancy t m cutoff band) threshold shellGrowth48 shell ∧
      s ∈ positiveExternalCreationPrefix t band.orientation m band.oldRank}

/-- A balanced fixed-clock positive-prefix raw interface failure is paid by
the exact pair-rank harmonic factor. -/
theorem simpleRandomWalk_positiveInterfacePositiveRawGrowthEvent_le
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {threshold : ℕ → ℕ} {shell : ℕ}
    (hm : 1 < m)
    (hphase : band.vertexPhase = false)
    (hthreshold : 0 < band.externalThreshold)
    (hclock : n ≤ cutoff)
    (balance : PhysicalInterfaceBalanceData t band.orientation m
      band.oldRank band.externalThreshold (shellWidth48 m) shell) :
    simpleRandomWalk (positiveInterfacePositiveRawGrowthEvent t m cutoff n
        band threshold shell) ≤
      variableDeltaHarmonic (2 * cutoff + 1) *
        ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell) := by
  apply simpleRandomWalk_event_le_variableDeltaHarmonic hm band.oldRank_pos
    threshold cutoff
      (positiveInterfacePositiveRawGrowthEvent t m cutoff n band threshold
        shell)
  · intro s hs
    rcases hs with ⟨hcreation, hnext, hvalid, hfailure, hpositive⟩
    rcases exists_positiveInterfaceExternalPairSourceCap_of_raw_growth hm
      hphase hthreshold hcreation hnext hclock hvalid hfailure with
      ⟨eta, cap, hcode, hcap⟩
    refine ⟨eta, cap, ?_,
      positiveInterfaceExternalPairArithmetic_of_physicalBalance balance
        hthreshold eta cap, hcap⟩
    change 0 <
      (fixedOrientedTypedExternalWordCode t band.orientation
          (creationTimeNat m band.oldRank s) s).initial.1.length +
        2 * (fixedOrientedTypedExternalWordCode t band.orientation
          (creationTimeNat m band.oldRank s) s).retainedCount +
        (fixedOrientedTypedExternalWordCode t band.orientation
          (creationTimeNat m band.oldRank s) s).tail.1.length at hpositive
    rw [← hcode] at hpositive
    exact hpositive

end

end Erdos1165.HLOZPositiveInterfacePairRawHarmonic
