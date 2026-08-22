/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerOriginShiftPayment
import ErdosProblems.Erdos1165.HLOZLowGapProductEndgame
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaPositiveSourcePayment
import ErdosProblems.Erdos1165.TilingOrientedRetainedCoordinateSupport

/-!
# The zero deleted-prefix source-Theta branch is a fixed-origin event

At positive creation time a shifted external code already has a one-step
initial prefix.  Hence a zero deleted prefix can only have even temporal
orientation.  Its unique represented, orientation-compatible domino base
is the origin itself.  The source `I₁` window therefore forces a large
fixed-origin local time.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaZeroPrefixOrigin

open ExternalProposition44 HLOZFixedPointLocalTimeTail HLOZGapEstimate
open HLOZCheckerOriginShiftPayment HLOZGapReturn HLOZLowGapProductEndgame
open HLOZPathEvents HLOZProposition48Candidates
open HLOZSharpWindowProductClosure
open HLOZShellZeroReplacementWindows HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaPositiveSlotProduct
open HLOZSourceOrientedThetaPositiveSourcePayment
open HLOZSourceOrientedThetaWindowSplit HLOZThetaSourceBalance
open LazyDecomposition SpatialInsertionFiber
open TilingLazyDecomposition TilingOrientedRetainedCoordinateSupport
open TilingOrientedShellSupportSelector
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open HLOZUpperEstimates
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Fixed-origin local time at the source shell lower endpoint. -/
def cutoffOriginShellLocalTimeEvent (m : ℕ) : Set WalkPath :=
  originLocalTimeEvent (hlozCutoff44 m) (m - shellWidth48 m)

theorem zeroPrefixRestrictedThetaSourceEvent_subset_originShell
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hk : 0 < k) :
    zeroPrefixRestrictedThetaSourceEvent t o m k ⊆
      cutoffOriginShellLocalTimeEvent m := by
  classical
  intro s hs
  rcases hs with
    ⟨hvalid, hreach, hclock, ⟨b, hbsource⟩, hzeroPrefix⟩
  have hm : 1 < m := by
    have hbwindow := (Finset.mem_filter.mp hbsource).2
    simp only [mem_shellZeroSourceTotalWindow] at hbwindow
    omega
  have hcreation : 0 < creationTimeNat m k s := by
    have hcreate : ThresholdCreation s m k (creationTimeNat m k s) := by
      simpa only [creationTimeNat, hreach, dif_pos] using
        thresholdCreation_natFind hreach
    by_contra hn
    have hzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
    have hsite := position_mem_thresholdSites_of_creation hk hcreate
    have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
    have hlocal : localTime s 0 (s 0) = 1 := by
      simp [localTime, localTimePrefix, pathPrefix]
    rw [hzero, hlocal] at hlevel
    omega
  change ¬0 <
      (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s).initial.1.length +
        2 * (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k s) s).retainedCount +
        (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k s) s).tail.1.length at hzeroPrefix
  have hlengthZero :
      (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s).initial.1.length +
        2 * (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k s) s).retainedCount +
        (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k s) s).tail.1.length = 0 := by
    omega
  cases o with
  | shifted =>
      have hinitial :
          (fixedOrientedTypedExternalWordCode t .shifted
            (creationTimeNat m k s) s).initial.1.length = 1 := by
        simp [fixedOrientedTypedExternalWordCode, orientedInitialPrefix,
          incrementPrefixList, List.length_take]
        omega
      rw [hinitial] at hlengthZero
      omega
  | even =>
      have hretained :
          (fixedOrientedTypedExternalWordCode t .even
            (creationTimeNat m k s) s).retainedCount = 0 := by
        omega
      have hbtheta := (Finset.mem_filter.mp hbsource).1
      have hbwindow := (Finset.mem_filter.mp hbsource).2
      rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
        Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
      have hcompat : OrientationCompatible .even b := hbtheta.1.2
      have hbVTwo : b ∈ orientedTilingVTwoBases t .even
          (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
            shellZeroReplacementTotalWindow m (shellWidth48 m))
          s (creationTimeNat m k s) :=
        (mem_orientedTilingVTwoBases_iff t .even _ s _ b).2
          ⟨hbtheta.1.1, hcompat⟩
      have hwindowZero : 0 ∉
          shellZeroSourceTotalWindow m (shellWidth48 m) ∪
            shellZeroReplacementTotalWindow m (shellWidth48 m) := by
        simp only [Finset.mem_union, mem_shellZeroSourceTotalWindow,
          mem_shellZeroReplacementTotalWindow]
        omega
      have hrepresented :=
        orientedTilingVTwoBases_subset_fixedExternalDominoBases t .even _ s
          (creationTimeNat m k s) hvalid hwindowZero hbVTwo
      unfold tilingExternalDominoBases at hrepresented
      rcases Finset.mem_image.mp hrepresented with ⟨j, _hj, hjbase⟩
      have hjzero : j = 0 := by
        apply Fin.ext
        have hjlt : j.val < 1 := by simpa [hretained] using j.isLt
        omega
      subst j
      have hstart :
          (fixedOrientedTypedExternalWordCode t .even
            (creationTimeNat m k s) s).start = (0, 0) := by
        rfl
      have hbase : tilingBase t (0, 0) = b := by
        rw [rawExternalBase_zero, hstart] at hjbase
        exact hjbase
      have horiginCompat : OrientationCompatible .even (0, 0) := by
        rfl
      have hbOrigin : (0, 0) = b :=
        eq_of_tilingBase_eq_of_orientationCompatible t horiginCompat
          hcompat hbase
      rw [← hbOrigin] at hbwindow
      have hlower : m - shellWidth48 m ≤
          localTime s (creationTimeNat m k s) (0, 0) := by
        simp only [mem_shellZeroSourceTotalWindow] at hbwindow
        omega
      change m - shellWidth48 m ≤
        localTime s (hlozCutoff44 m) (0, 0)
      exact hlower.trans (localTime_mono_time s (0, 0) hclock)

theorem eventually_simpleRandomWalk_cutoffOriginShellLocalTimeEvent_le_exp :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (cutoffOriginShellLocalTimeEvent m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
  have hdeadline := eventually_log_originDeadline_le_four_sqrt
  have hlogSq := eventually_log_sq_le_sqrt
  have hcutoff : ∀ᶠ m : ℕ in atTop, 1 ≤ levelCutoffTime upperTailDelta m :=
    (tendsto_levelCutoffTime upperTailDelta).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hdeadline, hlogSq, hcutoff,
      eventually_shellWidth48_moderate_nat,
      eventually_ge_atTop (8 : ℕ)] with
      m hdeadlineM hlogSqM hcutoffM hwidth hm
  rw [levelCutoffTime_upperTailDelta_eq_hlozCutoff44] at hdeadlineM hcutoffM
  let deadline := hlozCutoff44 m + 1
  let escape : ℝ := 1 / (100 * Real.log (deadline : ℝ))
  let returns := m - shellWidth48 m - 1
  have hmpos : (0 : ℝ) < m := by positivity
  have hsqrt : 0 < Real.sqrt (m : ℝ) := by positivity
  have hdeadlineNat : 2 ≤ deadline := by dsimp only [deadline]; omega
  have hlogPos : 0 < Real.log (deadline : ℝ) :=
    Real.log_pos (by exact_mod_cast hdeadlineNat)
  have hescapePos : 0 < escape := by
    dsimp only [escape]
    positivity
  have hescapeOne : escape ≤ 1 := by
    dsimp only [escape]
    have hlogTwo : Real.log 2 ≥ 1 / 2 :=
      Real.log_two_gt_d9.le.trans' (by norm_num)
    have hlogLower : 1 / 2 ≤ Real.log (deadline : ℝ) :=
      hlogTwo.trans
        (Real.log_le_log (by norm_num) (by exact_mod_cast hdeadlineNat))
    apply (div_le_one (by positivity : 0 < 100 * Real.log (deadline : ℝ))).2
    nlinarith
  have hescapeLower : 1 / (400 * Real.sqrt (m : ℝ)) ≤ escape := by
    dsimp only [escape, deadline] at hdeadlineM ⊢
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hreturnsNat : m ≤ 2 * returns := by
    dsimp only [returns]
    omega
  have hreturns : (m : ℝ) / 2 ≤ (returns : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simpa [mul_comm] using (show (m : ℝ) ≤ 2 * returns by
      exact_mod_cast hreturnsNat)
  have hproduct : (1 / 800 : ℝ) * Real.sqrt (m : ℝ) ≤
      escape * (returns : ℝ) := by
    have hmul := mul_le_mul hescapeLower hreturns (by positivity) hescapePos.le
    have hsqrtSq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
      Real.mul_self_sqrt hmpos.le
    calc
      (1 / 800 : ℝ) * Real.sqrt (m : ℝ) =
          (1 / (400 * Real.sqrt (m : ℝ))) * ((m : ℝ) / 2) := by
        field_simp
        nlinarith
      _ ≤ escape * (returns : ℝ) := hmul
  have hdominates : (1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      escape * (returns : ℝ) := by
    calc
      (1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
          (1 / 2000 : ℝ) * Real.sqrt (m : ℝ) := by gcongr
      _ ≤ (1 / 800 : ℝ) * Real.sqrt (m : ℝ) := by
        gcongr
        norm_num
      _ ≤ _ := hproduct
  have hthreshold : 2 ≤ m - shellWidth48 m := by
    dsimp only [returns] at hreturnsNat
    omega
  calc
    simpleRandomWalk (cutoffOriginShellLocalTimeEvent m) ≤
        Gap.geometricReturnCost escape returns := by
      exact simpleRandomWalk_originLocalTimeEvent_le hcutoffM hthreshold
    _ ≤ Gap.exponentialReturnCost escape returns :=
      Gap.geometricReturnCost_le_exponentialReturnCost hescapePos.le
        hescapeOne _
    _ ≤ ENNReal.ofReal
        (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith

theorem simpleRandomWalk_cutoffOriginShellLocalTimeEvent_series_ne_top :
    ∑' m, simpleRandomWalk (cutoffOriginShellLocalTimeEvent m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk
    cutoffOriginShellLocalTimeEvent (by norm_num : (0 : ℝ) < 1 / 2000)
    eventually_simpleRandomWalk_cutoffOriginShellLocalTimeEvent_le_exp

theorem simpleRandomWalk_zeroPrefixRestrictedThetaSourceEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (zeroPrefixRestrictedThetaSourceEvent t o m k) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    simpleRandomWalk_cutoffOriginShellLocalTimeEvent_series_ne_top
  apply ENNReal.tsum_le_tsum
  intro m
  exact measure_mono
    (zeroPrefixRestrictedThetaSourceEvent_subset_originShell t o m k hk)

end

end Erdos1165.HLOZSourceOrientedThetaZeroPrefixOrigin
