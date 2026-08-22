/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongZeroPrefixOrigin
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairBalancedSeries
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalGrowthWitness

/-!
# Zero-prefix positive-interface pairs are a fixed-origin tail

The external word of a positive-interface failure may have empty physical
length.  At a positive creation time this forces the even orientation and no
retained dominoes.  The upper-shell witness is therefore the origin.  Its
deficit is at most a constant multiple of the broad `m^(7/10)` width, so the
whole exceptional branch is summable by the fixed-point return tail.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairZeroPrefixOrigin

open ExternalProposition44 HLOZFixedPointLocalTimeTail HLOZGapEstimate
open HLOZAllSixBandProductClosure
open HLOZCandidateLocalBroadThetaProduct HLOZCandidateLocalLazyCap
open HLOZCandidateLocalBroadThetaStrongZeroPrefixOrigin
open HLOZCheckerOriginShiftPayment HLOZGapReturn HLOZLowGapProductEndgame
open HLOZFullBetaRegimeSplit HLOZGapRandomClockScreen
open HLOZPathEvents HLOZPositiveInterfacePairBalancedSeries
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfaceExternalPairCoordinateRecovery
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePhysicalGrowthWitness
open HLOZPositiveInterfaceSupportSelector
open HLOZProposition48Candidates HLOZSharpPositiveShellNumerics
open HLOZSharpWindowProductClosure HLOZUpperEstimates
open HLOZRawFullGapProductPromotion
open HLOZSourceCorrectFilteredTransitions HLOZSourceCorrectFullGapClosure
open LazyDecomposition NearFavoriteShells NearFavoriteThresholded
open SmallWindow
open ScreeningInstantiation TilingLazyDecomposition
open PathInsertion SpatialInsertionFiber TilingExternalPhaseSplit
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingPrefixedInsertedLocalTime
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A uniform loss which contains every displayed positive deficit shell. -/
def positiveInterfaceOriginLoss48 (m : ℕ) : ℕ :=
  4 * candidateLocalBroadWidth48 m

/-- Fixed-origin local time at the lower endpoint left after the uniform
positive-interface loss. -/
def cutoffOriginPositiveInterfaceLocalTimeEvent (m : ℕ) : Set WalkPath :=
  originLocalTimeEvent (hlozCutoff44 m)
    (m - positiveInterfaceOriginLoss48 m)

/-- The displayed positive shells fit inside four broad `m^(7/10)` widths. -/
theorem positiveInterface_shell_loss_le
    {m shell : ℕ} {beta : ℝ}
    (hm : 1 ≤ m)
    (hbetaLower : ScreeningInstantiation.kappaOne ≤ beta)
    (hbeta : beta ≤ (7 / 10 : ℝ))
    (hshell : shell ∈ Finset.range (shellCount48 m beta - 1)) :
    (shell + 2) * shellWidth48 m ≤ positiveInterfaceOriginLoss48 m := by
  have hshellCount : shell + 2 ≤ shellCount48 m beta := by
    have := Finset.mem_range.mp hshell
    omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbetaExp : beta - ScreeningInstantiation.kappaOne ≤
      7 / 10 - ScreeningInstantiation.kappaOne := by linarith
  have hcountPow : (m : ℝ) ^ (beta - ScreeningInstantiation.kappaOne) ≤
      (m : ℝ) ^ ((7 / 10 : ℝ) -
        ScreeningInstantiation.kappaOne) :=
    Real.rpow_le_rpow_of_exponent_le hmR hbetaExp
  have hcountOne : 1 ≤
      (m : ℝ) ^ (beta - ScreeningInstantiation.kappaOne) := by
    exact Real.one_le_rpow hmR (sub_nonneg.mpr hbetaLower)
  have hcountCeil : (shellCount48 m beta : ℝ) ≤
      2 * (m : ℝ) ^ ((7 / 10 : ℝ) -
        ScreeningInstantiation.kappaOne) := by
    unfold shellCount48
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg m)
        (beta - ScreeningInstantiation.kappaOne))
    have : (Nat.ceil ((m : ℝ) ^
        (beta - ScreeningInstantiation.kappaOne)) : ℝ) ≤
        2 * (m : ℝ) ^ (beta - ScreeningInstantiation.kappaOne) := by
      linarith
    exact this.trans (by gcongr)
  have hwidth : (shellWidth48 m : ℝ) ≤
      2 * (m : ℝ) ^ ScreeningInstantiation.kappaOne := by
    unfold shellWidth48
    have hpowOne : 1 ≤ (m : ℝ) ^ ScreeningInstantiation.kappaOne :=
      Real.one_le_rpow hmR (by norm_num [ScreeningInstantiation.kappaOne])
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg m)
        ScreeningInstantiation.kappaOne)
    linarith
  have hproduct : ((shellCount48 m beta * shellWidth48 m : ℕ) : ℝ) ≤
      4 * (m : ℝ) ^ (7 / 10 : ℝ) := by
    push_cast
    calc
      (shellCount48 m beta : ℝ) * (shellWidth48 m : ℝ) ≤
          (2 * (m : ℝ) ^ ((7 / 10 : ℝ) -
            ScreeningInstantiation.kappaOne)) *
            (2 * (m : ℝ) ^ ScreeningInstantiation.kappaOne) := by
        gcongr <;> positivity
      _ = 4 * (m : ℝ) ^ (((7 / 10 : ℝ) -
          ScreeningInstantiation.kappaOne) +
            ScreeningInstantiation.kappaOne) := by
        rw [Real.rpow_add (by positivity : (0 : ℝ) < m)]
        ring
      _ = 4 * (m : ℝ) ^ (7 / 10 : ℝ) := by ring
  have hbroad : (m : ℝ) ^ (7 / 10 : ℝ) ≤
      candidateLocalBroadWidth48 m := by
    exact Nat.le_ceil _
  have hnat : shellCount48 m beta * shellWidth48 m ≤
      4 * candidateLocalBroadWidth48 m := by
    exact_mod_cast hproduct.trans (mul_le_mul_of_nonneg_left hbroad (by norm_num))
  unfold positiveInterfaceOriginLoss48
  exact (Nat.mul_le_mul_right (shellWidth48 m) hshellCount).trans hnat

/-- A positive-interface growth failure with an empty external word forces
the upper-row witness to be the origin. -/
theorem zeroPrefix_bandPositiveInterfaceFailure_subset_origin
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {m : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hm : 1 < m)
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m))
    (hprofile : s ∈ positiveInterfaceCreationNoNextProfileEvent
      m band.oldRank)
    (hfailure : s ∈ orientedBandPositiveInterfaceFailureEvent t o m band)
    (hzero :
      let z := fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m band.oldRank s) s
      z.initial.1.length + 2 * z.retainedCount + z.tail.1.length = 0) :
    s ∈ cutoffOriginPositiveInterfaceLocalTimeEvent m := by
  classical
  have hmpos : 0 < m := by omega
  rw [positiveInterfaceCreationNoNextProfileEvent, if_pos hmpos] at hprofile
  rcases hprofile with ⟨n, hcreation, hnext⟩
  rcases Set.mem_iUnion.mp hfailure with ⟨shell, hfailure⟩
  rcases Set.mem_iUnion.mp hfailure with ⟨hshell, hfailure⟩
  have hvalid : s ∈ validStepWalk := hfailure.1.1.2
  have hclock : n ≤ levelCutoffTime upperTailDelta m := by
    have hclock' := hfailure.1.2
    change creationTimeNat m band.oldRank s ≤
      levelCutoffTime upperTailDelta m at hclock'
    rwa [creationTimeNat_eq_of_creation hcreation] at hclock'
  have hclockEq : pathTruncatedLevelTime m band.oldRank
      (levelCutoffTime upperTailDelta m) s = n :=
    HLOZTilingGapBandExtraction.pathTruncatedLevelTime_eq_of_creation_le_cutoff
      hcreation hclock
  have hn : 0 < n := by
    have hcreation' : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank n := by
      rw [show trajectory (stepsOfWalk s) = s from hvalid]
      exact hcreation
    exact HLOZThetaOneSourceShift.thresholdCreation_time_pos_of_two_le
      (stepsOfWalk s) (by omega) band.oldRank_pos hcreation'
  have hfavorite : thresholdSites s n m = favoriteSites s n :=
    HLOZTilingGapBandExtraction.thresholdSites_eq_favoriteSites_at_creation_of_terminal
      band.oldRank_pos hcreation le_rfl hnext
  have hgrowth : s ∈ thresholdedGrowthFailure
      (HLOZDominantPositiveInterfaceBandRecurrence.normalizedDominantBandOccupancy
        t o m (levelCutoffTime upperTailDelta m) band)
      (geometricShellThreshold
        (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
        shellGrowth48)
      shellGrowth48 shell := by
    simpa only [thresholdedInterfaceBad, compl_univ, empty_union] using
      hfailure.2
  have hpositive : 0 <
      HLOZDominantPositiveInterfaceBandRecurrence.normalizedDominantBandOccupancy
        t o m (levelCutoffTime upperTailDelta m) band s (shell + 1) := by
    simpa only [thresholdedGrowthFailure, Set.mem_ofPred_eq] using
      (show 0 < _ from lt_of_le_of_lt (Nat.zero_le _)
        (show _ < _ from hgrowth.1))
  unfold HLOZDominantPositiveInterfaceBandRecurrence.normalizedDominantBandOccupancy
    at hpositive
  rw [hclockEq] at hpositive
  rcases Finset.card_pos.mp hpositive with ⟨x, hx⟩
  rw [mem_shellCandidates] at hx
  rcases hx with ⟨hxSupport, hshellLabel⟩
  rw [HLOZDominantPositiveInterfaceSupportSelector.orientedDominantPositiveInterfacePhysicalSites,
    Finset.mem_image] at hxSupport
  rcases hxSupport with ⟨b, hbDominant, hbx⟩
  have hsupport :=
    HLOZDominantPositiveInterfaceSupportSelector.orientedDominantPositiveInterfaceSupportAt_subset
      t o m 1 s n hbDominant
  have hcodeZero :
      let z := fixedOrientedTypedExternalWordCode t o n s
      z.initial.1.length + 2 * z.retainedCount + z.tail.1.length = 0 := by
    simpa only [creationTimeNat_eq_of_creation hcreation] using hzero
  cases o with
  | shifted =>
      have hinitial :
          (fixedOrientedTypedExternalWordCode t .shifted n s).initial.1.length =
            1 := by
        simp [fixedOrientedTypedExternalWordCode, orientedInitialPrefix,
          incrementPrefixList, List.length_take]
        omega
      change
        (fixedOrientedTypedExternalWordCode t .shifted n s).initial.1.length +
          2 * (fixedOrientedTypedExternalWordCode t .shifted n s).retainedCount +
          (fixedOrientedTypedExternalWordCode t .shifted n s).tail.1.length = 0
        at hcodeZero
      rw [hinitial] at hcodeZero
      omega
  | even =>
      have hretained :
          (fixedOrientedTypedExternalWordCode t .even n s).retainedCount = 0 := by
        omega
      have hrepresented : b ∈ tilingExternalDominoBases t
          (fixedOrientedTypedExternalWordCode t .even n s).start
          (fixedOrientedTypedExternalWordCode t .even n s).retained := by
        unfold orientedPositiveInterfaceSupportAt at hsupport
        exact (mem_orientedPositiveInterfaceCodeSupport_iff.mp hsupport).1
      unfold tilingExternalDominoBases at hrepresented
      rcases Finset.mem_image.mp hrepresented with ⟨j, _hj, hjbase⟩
      have hjzero : j = 0 := by
        apply Fin.ext
        have hjlt : j.val < 1 := by simpa [hretained] using j.isLt
        omega
      subst j
      have hstart :
          (fixedOrientedTypedExternalWordCode t .even n s).start = (0, 0) := by
        rfl
      have hbase : tilingBase t (0, 0) = b := by
        rw [rawExternalBase_zero, hstart] at hjbase
        exact hjbase
      have horiginCompat : OrientationCompatible .even (0, 0) := by rfl
      have horiginEndpoint : (0, 0) =
          orientedDominoEndpoint t .even b :=
        eq_orientedDominoEndpoint_of_compatible_of_tilingBase_eq t .even
          horiginCompat hbase
      have hxOrigin : (0, 0) = x := horiginEndpoint.trans hbx
      have hwidth : 0 < shellWidth48 m := by
        unfold shellWidth48
        exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
      have hdeficitLt : m - localTime s n x <
          (shell + 2) * shellWidth48 m := by
        rw [← Nat.div_lt_iff_lt_mul hwidth]
        omega
      have hloss : (shell + 2) * shellWidth48 m ≤
          positiveInterfaceOriginLoss48 m :=
        positiveInterface_shell_loss_le (by omega)
          (sourceProductEndpointBand_betaLower hband)
          (sourceProductEndpointBand_betaUpperRange hband) hshell
      have hlower : m - positiveInterfaceOriginLoss48 m ≤
          localTime s n (0, 0) := by
        rw [hxOrigin]
        omega
      change m - positiveInterfaceOriginLoss48 m ≤
        localTime s (hlozCutoff44 m) (0, 0)
      rw [← levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
      exact hlower.trans (localTime_mono_time s (0, 0) hclock)

theorem eventually_simpleRandomWalk_cutoffOriginPositiveInterfaceLocalTimeEvent_le_exp :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (cutoffOriginPositiveInterfaceLocalTimeEvent m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
  have hdeadline := eventually_log_originDeadline_le_four_sqrt
  have hlogSq := eventually_log_sq_le_sqrt
  have hcutoff : ∀ᶠ m : ℕ in atTop, 1 ≤ levelCutoffTime upperTailDelta m :=
    (tendsto_levelCutoffTime upperTailDelta).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hdeadline, hlogSq, hcutoff,
      eventually_candidateLocalBroadThetaScaleArithmetic,
      eventually_ge_atTop (20 : ℕ)] with
      m hdeadlineM hlogSqM hcutoffM scale hm
  rw [levelCutoffTime_upperTailDelta_eq_hlozCutoff44] at hdeadlineM hcutoffM
  let deadline := hlozCutoff44 m + 1
  let escape : ℝ := 1 / (100 * Real.log (deadline : ℝ))
  let returns := m - positiveInterfaceOriginLoss48 m - 1
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
  have hwidthNat : 10 * candidateLocalBroadWidth48 m ≤ m := by
    have hwidthR := scale.width
    have : ((10 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤ (m : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hloss : positiveInterfaceOriginLoss48 m =
      4 * candidateLocalBroadWidth48 m := rfl
  have hreturnsNat : m ≤ 2 * returns := by
    dsimp only [returns]
    rw [hloss]
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
  have hthreshold : 2 ≤ m - positiveInterfaceOriginLoss48 m := by
    dsimp only [returns] at hreturnsNat
    omega
  calc
    simpleRandomWalk (cutoffOriginPositiveInterfaceLocalTimeEvent m) ≤
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

theorem simpleRandomWalk_cutoffOriginPositiveInterfaceLocalTimeEvent_series_ne_top :
    ∑' m, simpleRandomWalk
      (cutoffOriginPositiveInterfaceLocalTimeEvent m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk
    cutoffOriginPositiveInterfaceLocalTimeEvent
    (by norm_num : (0 : ℝ) < 1 / 2000)
    eventually_simpleRandomWalk_cutoffOriginPositiveInterfaceLocalTimeEvent_le_exp

/-- Zero-prefix failures in one endpoint band.  This deliberately contains
the whole physical failure, not just the unbalanced subevent. -/
def bandPositiveInterfaceZeroPrefixEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
    {s | ∃ o : Orientation,
      s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
        let z := fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s
        z.initial.1.length + 2 * z.retainedCount + z.tail.1.length = 0}

/-- Rankwise finite union of the zero-prefix interface failures. -/
def positiveInterfaceZeroPrefixPaymentUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfaceZeroPrefixEvent data t m)

theorem positiveInterfaceZeroPrefixPaymentUnionAtRank_subset_origin
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (hm : 1 < m)
    (hthreshold : 0 < data.externalThreshold m) :
    positiveInterfaceZeroPrefixPaymentUnionAtRank data t rank m ⊆
      cutoffOriginPositiveInterfaceLocalTimeEvent m := by
  intro s hs
  rcases hs with ⟨band, hbandRank, hsband⟩
  rcases hsband with ⟨hprofile, o, hfailure, hzero⟩
  have hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m) :=
    (Finset.mem_filter.mp hbandRank).1
  exact zeroPrefix_bandPositiveInterfaceFailure_subset_origin hm hband
    hprofile hfailure hzero

theorem eventually_simpleRandomWalk_positiveInterfaceZeroPrefixPaymentUnionAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (positiveInterfaceZeroPrefixPaymentUnionAtRank data t rank m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
  filter_upwards
      [data.threshold_pos,
       eventually_simpleRandomWalk_cutoffOriginPositiveInterfaceLocalTimeEvent_le_exp,
       eventually_ge_atTop (2 : ℕ)] with m hthreshold horigin hm
  exact (measure_mono
    (positiveInterfaceZeroPrefixPaymentUnionAtRank_subset_origin data t rank m
      (by omega) hthreshold)).trans horigin

theorem simpleRandomWalk_positiveInterfaceZeroPrefixPaymentUnionAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∑' m, simpleRandomWalk
      (positiveInterfaceZeroPrefixPaymentUnionAtRank data t rank m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1 / 2000)
    (eventually_simpleRandomWalk_positiveInterfaceZeroPrefixPaymentUnionAtRank_le_exp
      data t rank)

/-- The remaining exact-pair obstruction in one band: the reconstructed
source cap fails its cap-independent arithmetic certificate. -/
def bandPositiveInterfacePairArithmeticObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
    bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band ∩
      {s | ∃ o : Orientation,
        s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
          ∃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
            o m band.oldRank 1
              (shellWidth48 m) shell,
          ∃ cap : ℕ,
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
                (creationTimeNat m band.oldRank s) s ∧
              s ∈ positiveInterfaceExternalPairSourceCap eta cap
                (geometricShellThreshold
                  (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                  shellGrowth48)
                (levelCutoffTime upperTailDelta m) ∧
              ¬ PositiveInterfaceExternalPairArithmetic eta cap}

/-- Rankwise union of exact pair arithmetic obstructions. -/
def positiveInterfacePairArithmeticObstructionUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfacePairArithmeticObstructionEvent data t m)

/-- Failure of the exact adjacent-window comparison in one reconstructed
pair source cap. -/
def bandPositiveInterfacePairWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
    bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band ∩
      {s | ∃ o : Orientation,
        s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
          ∃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
            o m band.oldRank 1
              (shellWidth48 m) shell,
          ∃ cap : ℕ,
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
                (creationTimeNat m band.oldRank s) s ∧
              s ∈ positiveInterfaceExternalPairSourceCap eta cap
                (geometricShellThreshold
                  (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                  shellGrowth48)
                (levelCutoffTime upperTailDelta m) ∧
              ∃ b : PositiveInterfaceExternalPairCoordinate eta,
                ¬ windowMass
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1))
                    (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1)) (shell + 1)) ≤
                  positiveInterfaceRatioConstant * windowMass
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1))
                    (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1)) shell)}

/-- Failure of the exact prefix-boundary margin in one reconstructed pair
source cap. -/
def bandPositiveInterfacePairBoundaryObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
    bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band ∩
      {s | ∃ o : Orientation,
        s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
          ∃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
            o m band.oldRank 1
              (shellWidth48 m) shell,
          ∃ cap : ℕ,
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
                (creationTimeNat m band.oldRank s) s ∧
              s ∈ positiveInterfaceExternalPairSourceCap eta cap
                (geometricShellThreshold
                  (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                  shellGrowth48)
                (levelCutoffTime upperTailDelta m) ∧
              ∃ b : PositiveInterfaceExternalPairCoordinate eta,
                ¬ prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
                      eta.1.1.start eta.1.1.retained
                      (positiveInterfaceExternalPairTerminal eta) b.1 <
                    Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1) +
                      max 1 (shell * shellWidth48 m)}

/-- The structural form of the prefix-boundary obstruction: the physical
endpoint selected by the external orientation is not the dominant endpoint
of its fixed domino.  Unlike a large-deviation event this condition need not
be rare; it is the branch that must be normalized to the mate endpoint. -/
def bandPositiveInterfacePairNonDominantObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
    bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band ∩
      {s | ∃ o : Orientation,
        s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
          ∃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
            o m band.oldRank 1
              (shellWidth48 m) shell,
          ∃ cap : ℕ,
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
                (creationTimeNat m band.oldRank s) s ∧
              s ∈ positiveInterfaceExternalPairSourceCap eta cap
                (geometricShellThreshold
                  (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                  shellGrowth48)
                (levelCutoffTime upperTailDelta m) ∧
              ∃ b : PositiveInterfaceExternalPairCoordinate eta,
                ¬ prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1
                      eta.1.1.start eta.1.1.retained
                      (positiveInterfaceExternalPairTerminal eta)
                      (tilingPartner t
                        (orientedDominoEndpoint t o b.1.1)) ≤
                    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1
                      eta.1.1.start eta.1.1.retained
                      (positiveInterfaceExternalPairTerminal eta)
                      (orientedDominoEndpoint t o b.1.1)}

/-- A failed prefix-boundary margin is necessarily a genuinely
non-dominant oriented endpoint.  Dominance itself would identify the fixed
boundary with the retained coordinate count and make the margin strict. -/
theorem bandPositiveInterfacePairBoundaryObstruction_subset_nonDominant
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hm : 1 < m) :
    bandPositiveInterfacePairBoundaryObstructionEvent data t m band ⊆
      bandPositiveInterfacePairNonDominantObstructionEvent data t m band := by
  rintro s ⟨⟨hprofile, hunbalanced⟩,
    o, horientedFailure, shell, hshell, eta, cap, hcode, hcap, b, hboundary⟩
  refine ⟨⟨hprofile, hunbalanced⟩,
    o, horientedFailure, shell, hshell, eta, cap, hcode, hcap, b, ?_⟩
  intro hdominant
  exact hboundary
    (positiveInterfaceExternalPairBoundary_lt_of_orientedDominant eta hm
      band.oldRank_pos b hdominant)

/-- The shell width eventually supplies the cap-independent lower bound in
the pair arithmetic certificate. -/
theorem eventually_four_le_shellWidth48 :
    ∀ᶠ m : ℕ in atTop, 4 ≤ shellWidth48 m := by
  have htop : Tendsto (fun m : ℕ ↦ (m : ℝ) ^
      ScreeningInstantiation.kappaOne) atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num [ScreeningInstantiation.kappaOne] :
        0 < ScreeningInstantiation.kappaOne)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [htop.eventually (eventually_ge_atTop (4 : ℝ))] with m hm
  unfold shellWidth48
  exact_mod_cast (hm.trans
    (Nat.le_ceil ((m : ℝ) ^ ScreeningInstantiation.kappaOne)))

/-- Once the two scalar certificate fields are automatic, every exact pair
arithmetic obstruction exposes either a bad adjacent-window coordinate or a
bad prefix-boundary coordinate. -/
theorem bandPositiveInterfacePairArithmeticObstruction_subset_window_union_boundary
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hwidth : 4 ≤ shellWidth48 m) :
    bandPositiveInterfacePairArithmeticObstructionEvent data t m band ⊆
      bandPositiveInterfacePairWindowRatioObstructionEvent data t m band ∪
        bandPositiveInterfacePairBoundaryObstructionEvent data t m band := by
  classical
  rintro s ⟨⟨hprofile, hunbalanced⟩, hobstruction⟩
  rcases hobstruction with ⟨o, horientedFailure, shell, hshell, eta, cap,
    hcode, hcap, hnotArithmetic⟩
  by_cases hratio : ∀ b : PositiveInterfaceExternalPairCoordinate eta,
      windowMass
          (Fintype.card (TilingCoordinatesAt t eta.1.1.start
            eta.1.1.retained b.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card (TilingCoordinatesAt t eta.1.1.start
              eta.1.1.retained b.1)) (shell + 1)) ≤
        positiveInterfaceRatioConstant * windowMass
          (Fintype.card (TilingCoordinatesAt t eta.1.1.start
            eta.1.1.retained b.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card (TilingCoordinatesAt t eta.1.1.start
              eta.1.1.retained b.1)) shell)
  · by_cases hboundary : ∀ b : PositiveInterfaceExternalPairCoordinate eta,
        prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
              eta.1.1.start eta.1.1.retained
              (positiveInterfaceExternalPairTerminal eta) b.1 <
            Fintype.card (TilingCoordinatesAt t eta.1.1.start
                eta.1.1.retained b.1) +
              max 1 (shell * shellWidth48 m)
    · exact (hnotArithmetic
        { external_pos := by omega
          width_ge_four := hwidth
          window_ratio := hratio
          boundary_lt := hboundary }).elim
    · push_neg at hboundary
      rcases hboundary with ⟨b, hb⟩
      exact Or.inr
        ⟨⟨hprofile, hunbalanced⟩,
          o, horientedFailure, shell, hshell, eta, cap, hcode, hcap, b,
            not_lt_of_ge hb⟩
  · push_neg at hratio
    rcases hratio with ⟨b, hb⟩
    exact Or.inl
      ⟨⟨hprofile, hunbalanced⟩,
        o, horientedFailure, shell, hshell, eta, cap, hcode, hcap, b,
          not_le_of_gt hb⟩

theorem bandPositiveInterfaceProfiledUnbalanced_subset_zeroPrefix_union_arithmetic
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hm : 1 < m)
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m)) :
    positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
        bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band ⊆
      bandPositiveInterfaceZeroPrefixEvent data t m band ∪
        bandPositiveInterfacePairArithmeticObstructionEvent data t m band := by
  rintro s ⟨hprofile, hunbalanced⟩
  rcases exists_sourceCap_zeroPrefix_or_not_arithmetic_of_mem_bandUnbalanced
      hm hband hprofile hunbalanced with
    ⟨o, shell, hshell, eta, cap, horientedFailure, hcode, hcap,
      hzero | hnotArithmetic⟩
  · left
    refine ⟨hprofile, o, horientedFailure, ?_⟩
    change
      (fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s).initial.1.length +
          2 * (fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s).retainedCount +
          (fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s).tail.1.length = 0
    rw [← hcode]
    exact hzero
  · right
    exact ⟨⟨hprofile, hunbalanced⟩, o, horientedFailure, shell, hshell,
      eta, cap, hcode, hcap, hnotArithmetic⟩

theorem positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_subset_split
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (hm : 1 < m)
    (hthreshold : 0 < data.externalThreshold m) :
    positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
        data t rank m ⊆
      positiveInterfaceZeroPrefixPaymentUnionAtRank data t rank m ∪
        positiveInterfacePairArithmeticObstructionUnionAtRank data t rank m := by
  rintro s ⟨hprofile, band, hbandRank, hunbalanced⟩
  have hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m) :=
    (Finset.mem_filter.mp hbandRank).1
  have hrank : band.oldRank = rank := (Finset.mem_filter.mp hbandRank).2
  rw [← hrank] at hprofile
  have hbandThreshold : band.externalThreshold = data.externalThreshold m :=
    HLOZTilingEndpointBandExtraction.canonicalEndpointLowGapBand_externalThreshold
      (mem_sourceProductEndpointBands_iff.mp hband).1
  rcases bandPositiveInterfaceProfiledUnbalanced_subset_zeroPrefix_union_arithmetic
      hm hband ⟨hprofile, hunbalanced⟩ with hzero | harithmetic
  · exact Or.inl ⟨band, hbandRank, hzero⟩
  · exact Or.inr ⟨band, hbandRank, harithmetic⟩

end

end Erdos1165.HLOZPositiveInterfacePairZeroPrefixOrigin
