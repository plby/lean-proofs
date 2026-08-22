/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongPositivePayment
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaZeroPrefixOrigin

/-!
# Zero-prefix broad strong source is a fixed-origin tail
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongZeroPrefixOrigin

open ExternalProposition44 HLOZFixedPointLocalTimeTail HLOZGapEstimate
open HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaStrongCreationCover
open HLOZCheckerOriginShiftPayment HLOZGapReturn HLOZLowGapProductEndgame
open HLOZPathEvents HLOZSourceOrientedThetaPositiveSlotProduct
open HLOZSharpWindowProductClosure HLOZShellZeroReplacementWindows
open HLOZUpperEstimates LazyDecomposition ScreeningInstantiation
open SpatialInsertionFiber TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedVisitedBaseExternalSupport
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def cutoffOriginBroadLocalTimeEvent (m : ℕ) : Set WalkPath :=
  originLocalTimeEvent (hlozCutoff44 m) (m - candidateLocalBroadWidth48 m)

theorem zeroPrefixBroadStrongSourceEvent_subset_origin
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    zeroPrefixBroadStrongSourceEvent t o m k
        (candidateLocalBroadWidth48 m) (m / 2) ⊆
      cutoffOriginBroadLocalTimeEvent m := by
  classical
  intro s hs
  rcases hs with
    ⟨hvalid, hreach, hclock, ⟨b, hbstrong⟩, hzeroPrefix⟩
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
          (creationTimeNat m k s) s).tail.1.length = 0 := by omega
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
            (creationTimeNat m k s) s).retainedCount = 0 := by omega
      rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter] at hbstrong
      have hblower := hbstrong.1
      rw [HLOZCandidateLocalBroadSourceLowThetaGeometry.orientedBroadSourceLowThetaBases,
        Finset.mem_filter] at hblower
      rcases hblower with ⟨hvisited, hcompat, hbwindow, _hexternal⟩
      have hbase : tilingBase t b = b := by
        rw [visitedTilingBases, Finset.mem_image] at hvisited
        obtain ⟨x, _hx, hxbase⟩ := hvisited
        rw [← hxbase]
        exact tilingBase_idem t x
      have hpositive : 0 < localTime s (creationTimeNat m k s) b := by
        simp only [mem_shellZeroSourceTotalWindow] at hbwindow
        omega
      have hrepresented := tilingBase_mem_fixedExternalDominoBases_of_positive
        t .even s (creationTimeNat m k s) hvalid hcreation b hbase hcompat
          hpositive
      unfold tilingExternalDominoBases at hrepresented
      rcases Finset.mem_image.mp hrepresented with ⟨j, _hj, hjbase⟩
      have hjzero : j = 0 := by
        apply Fin.ext
        have hjlt : j.val < 1 := by simpa [hretained] using j.isLt
        omega
      subst j
      have hstart :
          (fixedOrientedTypedExternalWordCode t .even
            (creationTimeNat m k s) s).start = (0, 0) := by rfl
      have hbaseOrigin : tilingBase t (0, 0) = b := by
        rw [rawExternalBase_zero, hstart] at hjbase
        exact hjbase
      have horiginCompat : OrientationCompatible .even (0, 0) := by rfl
      have hbOrigin : (0, 0) = b :=
        eq_of_tilingBase_eq_of_orientationCompatible t horiginCompat
          hcompat hbaseOrigin
      rw [← hbOrigin] at hbwindow
      have hlower : m - candidateLocalBroadWidth48 m ≤
          localTime s (creationTimeNat m k s) (0, 0) := by
        simp only [mem_shellZeroSourceTotalWindow] at hbwindow
        omega
      change m - candidateLocalBroadWidth48 m ≤
        localTime s (hlozCutoff44 m) (0, 0)
      exact hlower.trans (localTime_mono_time s (0, 0) hclock)

theorem eventually_simpleRandomWalk_cutoffOriginBroadLocalTimeEvent_le_exp :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (cutoffOriginBroadLocalTimeEvent m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
  have hdeadline := eventually_log_originDeadline_le_four_sqrt
  have hlogSq := eventually_log_sq_le_sqrt
  have hcutoff : ∀ᶠ m : ℕ in atTop, 1 ≤ levelCutoffTime upperTailDelta m :=
    (tendsto_levelCutoffTime upperTailDelta).eventually (eventually_ge_atTop 1)
  filter_upwards [hdeadline, hlogSq, hcutoff,
      eventually_candidateLocalBroadThetaScaleArithmetic,
      eventually_ge_atTop (20 : ℕ)] with
      m hdeadlineM hlogSqM hcutoffM scale hm
  rw [levelCutoffTime_upperTailDelta_eq_hlozCutoff44] at hdeadlineM hcutoffM
  let deadline := hlozCutoff44 m + 1
  let escape : ℝ := 1 / (100 * Real.log (deadline : ℝ))
  let returns := m - candidateLocalBroadWidth48 m - 1
  have hmpos : (0 : ℝ) < m := by positivity
  have hsqrt : 0 < Real.sqrt (m : ℝ) := by positivity
  have hdeadlineNat : 2 ≤ deadline := by dsimp only [deadline]; omega
  have hlogPos : 0 < Real.log (deadline : ℝ) :=
    Real.log_pos (by exact_mod_cast hdeadlineNat)
  have hescapePos : 0 < escape := by dsimp only [escape]; positivity
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
  have hwidthNat : 10 * candidateLocalBroadWidth48 m ≤ m := by
    have hwidthR := scale.width
    have : ((10 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤ (m : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
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
      _ ≤ (1 / 800 : ℝ) * Real.sqrt (m : ℝ) := by gcongr; norm_num
      _ ≤ _ := hproduct
  have hthreshold : 2 ≤ m - candidateLocalBroadWidth48 m := by
    dsimp only [returns] at hreturnsNat
    omega
  calc
    simpleRandomWalk (cutoffOriginBroadLocalTimeEvent m) ≤
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

theorem simpleRandomWalk_cutoffOriginBroadLocalTimeEvent_series_ne_top :
    ∑' m, simpleRandomWalk (cutoffOriginBroadLocalTimeEvent m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk
    cutoffOriginBroadLocalTimeEvent (by norm_num : (0 : ℝ) < 1 / 2000)
    eventually_simpleRandomWalk_cutoffOriginBroadLocalTimeEvent_le_exp

theorem simpleRandomWalk_zeroPrefixBroadStrongSourceEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (zeroPrefixBroadStrongSourceEvent t o m k
        (candidateLocalBroadWidth48 m) (m / 2)) ≠ ∞ := by
  apply measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk _ (by norm_num : (0 : ℝ) < 1 / 2000)
  filter_upwards
      [eventually_simpleRandomWalk_cutoffOriginBroadLocalTimeEvent_le_exp,
        eventually_ge_atTop (2 : ℕ)] with m horigin hm
  exact (measure_mono
    (zeroPrefixBroadStrongSourceEvent_subset_origin t o m k (by omega) hk)).trans
      horigin

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongZeroPrefixOrigin
