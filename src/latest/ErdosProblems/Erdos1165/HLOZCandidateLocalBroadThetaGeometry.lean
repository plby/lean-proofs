/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaProduct
import ErdosProblems.Erdos1165.HLOZNoLazyFullBetaProductBranch
import ErdosProblems.Erdos1165.HLOZSourceEndpointExternalTransport

/-!
# Geometry of the broad candidate-local Theta slot

The failed-pair endpoint selected by the full beta decomposition is not
necessarily the dominant endpoint of its tiling domino.  This file records
the source-correct facts which do not require dominance:

* its local time is in the broad source window;
* both it and its mate are strictly below level `m` at the old creation
  clock; and
* once the selected endpoint has been normalized to a tiling base, a low
  endpoint-chain count puts that base in the global (not V2-restricted)
  oriented Theta set.
-/

open Set

namespace Erdos1165.HLOZCandidateLocalBroadThetaGeometry

open HLOZCandidateLocalBroadThetaProduct HLOZFullBetaRegimeSplit
open HLOZGapBetaArithmetic HLOZPathEvents
open HLOZGapRandomClockScreen HLOZNoLazyFullBetaProductBranch
open HLOZProposition48Candidates
open HLOZSourceOrientedExternalLocalTime HLOZSourceOrientedThetaBalance
open HLOZSourceEndpointExternalTransport
open HLOZShellZeroReplacementWindows
open HLOZThetaOneSourceShift HLOZTilingGapBandExtraction
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber
open TilingLazyDecomposition TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- No level-`m+1` site has appeared yet at the old failed-pair clock. -/
theorem LowGapFailedPair.noNext_at_old
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) :
    thresholdCount s p.nOld (m + 1) = 0 := by
  have holdTerminal : p.nOld ≤ p.nTerminal := by
    have holdFour : p.oldRank < 4 := p.rank_lt.trans_le p.newRank_le_four
    exact (creation_time_lt p.oldRank_pos (by omega)
      holdFour p.oldCreation p.terminalCreation).le
  have hmono := thresholdCount_mono_time s (m + 1) holdTerminal
  change thresholdCount s p.nOld (m + 1) ≤
    thresholdCount s p.nTerminal (m + 1) at hmono
  rw [p.noNext] at hmono
  omega

/-- At the old creation clock the selected endpoint and its mate are both
strictly below level `m`.  The mate conclusion uses the failed-pair
separation from the old favorite dominoes, not a dominance assertion. -/
theorem LowGapFailedPair.selected_and_partner_lt_level
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) :
    localTime s p.nOld (s p.nNew) < m ∧
      localTime s p.nOld (tilingPartner t (s p.nNew)) < m := by
  have hxLt : localTime s p.nOld (s p.nNew) < m := by
    have hfailure := p.deficitFailure
    omega
  have holdTerminal : p.nOld ≤ p.nTerminal := by
    have holdFour : p.oldRank < 4 := p.rank_lt.trans_le p.newRank_le_four
    exact (creation_time_lt p.oldRank_pos (by omega)
      holdFour p.oldCreation p.terminalCreation).le
  have hfavorite : thresholdSites s p.nOld m = favoriteSites s p.nOld :=
    thresholdSites_eq_favoriteSites_at_creation_of_terminal
      p.oldRank_pos p.oldCreation holdTerminal p.noNext
  have hpartnerNotFavorite :
      tilingPartner t (s p.nNew) ∉ favoriteSites s p.nOld := by
    intro hpartner
    exact (p.separated (tilingPartner t (s p.nNew)) hpartner).2
      ((sameDomino_iff_partner_eq t (s p.nNew)
        (tilingPartner t (s p.nNew))).2 rfl)
  have hpartnerLe :
      localTime s p.nOld (tilingPartner t (s p.nNew)) ≤ m := by
    have hzero := noNext_at_old p
    have hall := (thresholdCount_eq_zero_iff_forall_lt s p.nOld (m + 1)
      (Nat.zero_lt_succ m)).mp hzero
    have hpoint := hall (tilingPartner t (s p.nNew))
    omega
  refine ⟨hxLt, ?_⟩
  by_contra hnot
  apply hpartnerNotFavorite
  rw [← hfavorite]
  exact (mem_thresholdSites_iff s p.nOld m
    (tilingPartner t (s p.nNew)) (by omega)).mpr
      (Nat.le_of_not_gt hnot)

/-- The selected low-beta endpoint lies in the broad source interval
`[m-width+1,m)`. -/
theorem LowGapFailedPair.selected_mem_broadSourceWindow
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s)
    (hm : 1 ≤ m)
    (hfull : FullFailedPairBetaBand p j)
    (hbeta : deficitExponent48 (meshExponent p.scale) (j + 1) ≤
      (7 / 10 : ℝ)) :
    localTime s p.nOld (s p.nNew) ∈
      shellZeroSourceTotalWindow m (candidateLocalBroadWidth48 m) := by
  rcases hfull with ⟨_hj, _hband, hupper⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpower : (m : ℝ) ^
        deficitExponent48 (meshExponent p.scale) (j + 1) ≤
      (m : ℝ) ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR hbeta
  have hdeficit : p.deficit < candidateLocalBroadWidth48 m :=
    hupper.trans_le (Nat.ceil_mono hpower)
  have hwidthLe : candidateLocalBroadWidth48 m ≤ m := by
    unfold candidateLocalBroadWidth48
    apply Nat.ceil_le.mpr
    calc
      (m : ℝ) ^ (7 / 10 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
      _ = m := by rw [Real.rpow_one]
  have hsum := p.localTime_add_deficit
  have hselectedLt : localTime s p.nOld (s p.nNew) < m := by
    have hfailure := p.deficitFailure
    omega
  rw [mem_shellZeroSourceTotalWindow]
  constructor <;> omega

/-- A normalized base in the broad source window with external count below
the lower threshold belongs to the paper's global oriented Theta slice.
There is deliberately no base-versus-mate dominance hypothesis. -/
theorem mem_orientedGlobalThetaBases_of_base_sourceWindow_external_lt
    {t : DominoTiling} {o : Orientation} {m width externalLow externalHigh n : ℕ}
    {s : WalkPath} {b : Point}
    (hvalid : s ∈ validStepWalk)
    (hbase : IsTilingBase t b)
    (hcompatible : OrientationCompatible o b)
    (hwindow : localTime s n b ∈ shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime t o s n b < externalLow) :
    b ∈ orientedGlobalThetaBases t o m width externalLow externalHigh s n := by
  classical
  rw [orientedGlobalThetaBases, Finset.mem_filter]
  have hpos : 0 < localTime s n b := by
    have hmLower := (mem_shellZeroSourceTotalWindow.mp hwindow).1
    omega
  have hvisited : b ∈ visitedTilingBases t s n := by
    rw [visitedTilingBases, Finset.mem_image]
    refine ⟨b, (mem_visitedSites_iff_localTime_pos s n b).2 hpos, ?_⟩
    simp only [tilingBase, if_pos hbase]
  refine ⟨hvisited, hcompatible,
    Finset.mem_union_left _ hwindow, ?_⟩
  rw [tilingSourceExternalBaseLocalTime_eq_pathPhased_of_compatible
    t o s n b hvalid hcompatible]
  omega

/-- Opposite checker endpoints enter the global Theta slice after the actual
one-step recentering.  The only exceptional obstruction is the displayed
origin local time, which is paid separately in the checker route. -/
theorem oppositeChecker_mem_orientedGlobalThetaBases_oneStepRecenter
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k n width externalLow externalHigh : ℕ} {x : Point}
    (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hxbase : ¬ IsTilingBase (.checker d) x)
    (hwindow : localTime (trajectory omega) n x ∈
      shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime (.checker d) .shifted
      (trajectory omega) n x < externalLow) :
    x - trajectory omega 1 ∈
      orientedGlobalThetaBases (shiftedCheckerTiling d) .even m width
        externalLow externalHigh (oneStepRecenter (trajectory omega))
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
          (x - trajectory omega 1) < externalLow := by
    rw [pathPhasedExternalLocalTime_oneStepRecenter omega d (n - 1) x,
      hnPred]
    exact hexternal
  exact mem_orientedGlobalThetaBases_of_base_sourceWindow_external_lt
    hvalid htargetBase htargetCompatible htargetWindow htargetExternal

/-- Opposite endpoints of a column tiling enter the global Theta slice of
the reflected column pairing.  Reflection has no origin loss. -/
theorem oppositeColumn_mem_orientedGlobalThetaBases_horizontalReflect
    {t : DominoTiling} (ht : IsColumnTiling t) (o : Orientation)
    {m n width externalLow externalHigh : ℕ} {s : WalkPath} {x : Point}
    (hvalid : s ∈ validStepWalk)
    (hxbase : ¬ IsTilingBase t x)
    (hcompatible : OrientationCompatible o x)
    (hwindow : localTime s n x ∈ shellZeroSourceTotalWindow m width)
    (hexternal : pathPhasedExternalLocalTime t o s n x < externalLow) :
    horizontalReflectPoint x ∈
      orientedGlobalThetaBases (reflectedColumnTiling t) o m width
        externalLow externalHigh (horizontalReflectPath s) n := by
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
        (horizontalReflectPoint x) < externalLow := by
    rw [pathPhasedExternalLocalTime_horizontalReflect ht]
    exact hexternal
  exact mem_orientedGlobalThetaBases_of_base_sourceWindow_external_lt
    htargetValid htargetBase htargetCompatible htargetWindow htargetExternal

end

end Erdos1165.HLOZCandidateLocalBroadThetaGeometry
