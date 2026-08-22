/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaGeometry

/-!
# One-sided broad source-Theta geometry

The candidate-local complement supplies the literal inequality
`external count < externalThreshold`.  The two-sided global-Theta set with
upper endpoint `externalThreshold + 1` is a strict over-approximation and is
not the event estimated by the broad one-coordinate product.  This file
records the one-sided physical set which matches that product exactly.
-/

namespace Erdos1165.HLOZCandidateLocalBroadSourceLowThetaGeometry

open HLOZCandidateLocalBroadThetaGeometry
open HLOZPathEvents HLOZSourceEndpointExternalTransport
open HLOZShellZeroReplacementWindows HLOZSourceOrientedExternalLocalTime
open HLOZThetaOneSourceShift LazyDecomposition
open SpatialInsertionFiber TilingLazyDecomposition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Broad source-window bases whose oriented retained count is below the
candidate threshold.  There is no dominance condition and no spurious
upper-side external failure. -/
def orientedBroadSourceLowThetaBases
    (t : DominoTiling) (o : Orientation)
    (m width externalThreshold : ℕ) (s : WalkPath) (n : ℕ) : Finset Point := by
  classical
  exact (visitedTilingBases t s n).filter fun b ↦
    OrientationCompatible o b ∧
      localTime s n b ∈ shellZeroSourceTotalWindow m width ∧
      HLOZSourceOrientedExternalLocalTime.tilingSourceExternalBaseLocalTime
        t o s n b < externalThreshold

theorem mem_orientedBroadSourceLowThetaBases_of_base
    {t : DominoTiling} {o : Orientation}
    {m width externalThreshold n : ℕ} {s : WalkPath} {b : Point}
    (hvalid : s ∈ validStepWalk)
    (hbase : IsTilingBase t b)
    (hcompatible : OrientationCompatible o b)
    (hwindow : localTime s n b ∈ shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime t o s n b < externalThreshold) :
    b ∈ orientedBroadSourceLowThetaBases t o m width externalThreshold s n := by
  classical
  rw [orientedBroadSourceLowThetaBases, Finset.mem_filter]
  have hpos : 0 < localTime s n b := by
    have hmLower := (mem_shellZeroSourceTotalWindow.mp hwindow).1
    omega
  have hvisited : b ∈ visitedTilingBases t s n := by
    rw [visitedTilingBases, Finset.mem_image]
    refine ⟨b, (mem_visitedSites_iff_localTime_pos s n b).2 hpos, ?_⟩
    simp only [tilingBase, if_pos hbase]
  refine ⟨hvisited, hcompatible, hwindow, ?_⟩
  rw [tilingSourceExternalBaseLocalTime_eq_pathPhased_of_compatible
    t o s n b hvalid hcompatible]
  exact hexternal

theorem oppositeChecker_mem_orientedBroadSourceLowThetaBases_oneStepRecenter
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k n width externalThreshold : ℕ} {x : Point}
    (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hxbase : ¬ IsTilingBase (.checker d) x)
    (hwindow : localTime (trajectory omega) n x ∈
      shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime (.checker d) .shifted
      (trajectory omega) n x < externalThreshold) :
    x - trajectory omega 1 ∈
      orientedBroadSourceLowThetaBases (shiftedCheckerTiling d) .even
        m width externalThreshold (oneStepRecenter (trajectory omega))
        (n - 1) := by
  have hn : 0 < n :=
    thresholdCreation_time_pos_of_two_le omega hm hk hcreation
  have hnPred : n - 1 + 1 = n := by omega
  have hxzero : x ≠ 0 := by
    intro hx
    apply hxbase
    subst x
    change Tilings.checkerEven 0 = true
    decide
  have hvalid : oneStepRecenter (trajectory omega) ∈ validStepWalk := by
    rw [oneStepRecenter_trajectory]
    exact trajectory_mem_validStepWalk _
  have htargetBase : IsTilingBase (shiftedCheckerTiling d)
      (x - trajectory omega 1) :=
    (isTilingBase_shiftedChecker_iff_not omega d x).2 hxbase
  have htargetCompatible :
      OrientationCompatible .even (x - trajectory omega 1) := by
    change EvenPoint (x - trajectory omega 1)
    apply (isTilingBase_canonicalEast_iff_evenPoint _).mp
    simpa only [shiftedCheckerTiling, IsTilingBase, canonicalEastTiling]
      using htargetBase
  have htargetWindow : localTime (oneStepRecenter (trajectory omega))
      (n - 1) (x - trajectory omega 1) ∈
        shellZeroSourceTotalWindow m width := by
    rw [localTime_oneStepRecenter_eq_of_ne_origin omega (n - 1) x hxzero,
      hnPred]
    exact hwindow
  have htargetExternal :
      pathPhasedExternalLocalTime (shiftedCheckerTiling d) .even
        (oneStepRecenter (trajectory omega)) (n - 1)
          (x - trajectory omega 1) < externalThreshold := by
    rw [pathPhasedExternalLocalTime_oneStepRecenter omega d (n - 1) x,
      hnPred]
    exact hexternal
  exact mem_orientedBroadSourceLowThetaBases_of_base hvalid htargetBase
    htargetCompatible htargetWindow htargetExternal

theorem oppositeColumn_mem_orientedBroadSourceLowThetaBases_horizontalReflect
    {t : DominoTiling} (ht : IsColumnTiling t) (o : Orientation)
    {m n width externalThreshold : ℕ} {s : WalkPath} {x : Point}
    (hvalid : s ∈ validStepWalk)
    (hxbase : ¬ IsTilingBase t x)
    (hcompatible : OrientationCompatible o x)
    (hwindow : localTime s n x ∈ shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime t o s n x < externalThreshold) :
    horizontalReflectPoint x ∈
      orientedBroadSourceLowThetaBases (reflectedColumnTiling t) o
        m width externalThreshold (horizontalReflectPath s) n := by
  have htargetValid : horizontalReflectPath s ∈ validStepWalk := by
    have hs : trajectory (stepsOfWalk s) = s := hvalid
    rw [← hs, horizontalReflectPath_trajectory]
    exact trajectory_mem_validStepWalk _
  have htargetBase : IsTilingBase (reflectedColumnTiling t)
      (horizontalReflectPoint x) :=
    (isTilingBase_reflectedColumn_iff_not ht x).2 hxbase
  have htargetCompatible : OrientationCompatible o
      (horizontalReflectPoint x) := by
    cases o <;> rcases x with ⟨x₁, x₂⟩ <;>
      simp_all [OrientationCompatible, EvenPoint, OddPoint, pointParity,
        horizontalReflectPoint]
  have htargetWindow : localTime (horizontalReflectPath s) n
      (horizontalReflectPoint x) ∈ shellZeroSourceTotalWindow m width := by
    rw [localTime_horizontalReflectPath]
    exact hwindow
  have htargetExternal : pathPhasedExternalLocalTime
      (reflectedColumnTiling t) o (horizontalReflectPath s) n
        (horizontalReflectPoint x) < externalThreshold := by
    rw [pathPhasedExternalLocalTime_horizontalReflect ht]
    exact hexternal
  exact mem_orientedBroadSourceLowThetaBases_of_base htargetValid htargetBase
    htargetCompatible htargetWindow htargetExternal

end

end Erdos1165.HLOZCandidateLocalBroadSourceLowThetaGeometry
