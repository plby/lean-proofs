/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement
import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift
import ErdosProblems.Erdos1165.HLOZCheckerPrefixedStoppedCandidateFamily

/-!
# Origin-safe checker Proposition 4.9 families

Deleting the first checker step removes the time-zero visit to the physical
origin.  The target source row must therefore retain the strict target
inequality which says that restoring this one visit stays below level `m`.

This file first records the exact clock transport on the target reaching
stage.  It also supplies the fixed-direction stopped-family transport used
after the origin-safe target family has been constructed.  Unlike the
all-direction wrapper, the fixed-direction transport has no junk history and
keeps its literal pulled-back previous event.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerOriginSafeProp49Family

open HLOZCheckerPrefixedCylinderTransport
open HLOZCheckerPrefixedStoppedCandidateFamily
open HLOZAllCreationCanonicalRefinement
open HLOZTypedStoppedCandidateObservability
open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZStoppedHistoryCandidateFuture
open HLOZMeshCandidatePolynomialNumerics
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Data.SourceThetaGoodRepresentative
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZSourceOrientedThetaProduct
open HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows
open HLOZThetaOneSourceShift
open HLOZTilingConditionalCandidateWindows
open LazyDecomposition
open NegativeBinomial NegativeBinomialLocalCLT ScreeningInstantiation
open SmallWindow
open FiniteDominoProductLaw
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingAwayNegativeBinomial
open VariableStoppedTracePartition
open PreStoppingFiber PreStoppingSpatialLaw StoppedInsertion
open TilingDistinguishedTraceInvariant TilingPrefixedFavoriteTraceSupport

noncomputable section

/-- The checker-origin refinement's three-point source window is available
eventually.  This is kept next to the final family so callers need not
reprove the elementary lower growth of the shell width. -/
theorem eventually_three_le_shellWidth48 :
    ∀ᶠ m : ℕ in atTop, 3 ≤ shellWidth48 m := by
  have htop : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ kappaOne) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappaOne] : 0 < kappaOne)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [htop.eventually (eventually_ge_atTop (3 : ℝ))] with m hm
  unfold shellWidth48
  exact_mod_cast (hm.trans (Nat.le_ceil ((m : ℝ) ^ kappaOne)))

/-- The target-path condition which exactly compensates for restoring the
discarded physical time-zero visit. -/
def targetOriginSafe (m k : ℕ) (e : Direction) : Set WalkPath :=
  {s | localTime s (creationTimeNat m k s) (0 - directionVector e) + 1 < m}

theorem measurableSet_targetOriginSafe (m k : ℕ) (e : Direction) :
    MeasurableSet (targetOriginSafe m k e) := by
  have hlocal (n : ℕ) : Measurable fun s : WalkPath ↦
      localTime s n (0 - directionVector e) := by
    change Measurable
      ((fun u : Fin (n + 1) → Point ↦
          localTimePrefix u (0 - directionVector e)) ∘
        (fun s ↦ pathPrefix s n))
    exact (measurable_of_countable _).comp (measurable_pathPrefix n)
  have heq : targetOriginSafe m k e = ⋃ n : ℕ,
      {s | creationTimeNat m k s = n} ∩
        {s | localTime s n (0 - directionVector e) + 1 < m} := by
    ext s
    simp only [targetOriginSafe, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨creationTimeNat m k s, rfl, hs⟩
    · rintro ⟨n, hclock, hs⟩
      simpa only [hclock] using hs
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_eq_fun (measurable_creationTimeNat m k)
    measurable_const).inter
      (measurableSet_lt ((hlocal n).add measurable_const) measurable_const)

/-- If the recentered path creates rank `k` at `n` while its shifted origin
is still safe after restoring one visit, then the physical path creates the
same rank exactly one step later. -/
theorem thresholdCreation_of_oneStepRecenter_of_originSafe
    (omega : StepPath) {m k n : ℕ} (hm : 1 < m) (hk : 0 < k)
    (hcreation : ThresholdCreation
      (oneStepRecenter (trajectory omega)) m k n)
    (horigin : localTime (oneStepRecenter (trajectory omega)) n
        (0 - trajectory omega 1) + 1 < m) :
    ThresholdCreation (trajectory omega) m k (n + 1) := by
  have horiginPhysical :
      localTime (trajectory omega) (n + 1) 0 < m := by
    rw [← localTime_oneStepRecenter_origin_add_one omega n]
    exact horigin
  refine ⟨?_, ?_⟩
  · rw [← thresholdCount_oneStepRecenter_eq omega n m (by omega)
      horiginPhysical]
    exact hcreation.1
  · intro q hq
    cases q with
    | zero =>
        rw [PreStoppingFiber.thresholdCount_trajectory_zero_time]
        simp [show ¬m ≤ 1 by omega, hk]
    | succ q =>
        have hqn : q < n := by omega
        have horiginQ : localTime (trajectory omega) (q + 1) 0 < m :=
          (localTime_mono_time (trajectory omega) 0 (by omega)).trans_lt
            horiginPhysical
        rw [← thresholdCount_oneStepRecenter_eq omega q m (by omega)
          horiginQ]
        exact hcreation.2 q hqn

/-- On a genuine target source atom, target origin-safety is precisely enough
to rule out the physical checker-origin exception.  Validity and target
reachability are stated explicitly: neither follows from the bare predicate
`targetOriginSafe` on arbitrary functions `ℕ → Point`. -/
theorem checkerPrefixedPreimage_targetOriginSafe_subset_exception_compl
    (d : Tilings.CheckerDirection) (e : Direction)
    {m k w : ℕ} (hm : 1 < m) (hk : 0 < k) :
    checkerPrefixedPreimage e
        (targetOriginSafe m k e ∩ thresholdReachStage m k) ∩
        validStepWalk ⊆
      (checkerOriginShiftExceptionEvent d m k w)ᶜ := by
  intro s hs
  rcases hs with ⟨⟨hfirst, hsafe, hreach⟩, hvalid⟩
  let omega := stepsOfWalk s
  have hsTrajectory : trajectory omega = s := hvalid
  have hfirstEq : trajectory omega 1 = directionVector e := by
    rw [hsTrajectory]
    exact hfirst
  have htargetReach : ReachesThreshold
      (oneStepRecenter (trajectory omega)) m k := by
    change ReachesThreshold (oneStepRecenter s) m k at hreach
    simpa only [hsTrajectory] using hreach
  have htargetCreation : ThresholdCreation
      (oneStepRecenter (trajectory omega)) m k
        (creationTimeNat m k (oneStepRecenter (trajectory omega))) := by
    have hfind := thresholdCreation_natFind htargetReach
    simpa only [creationTimeNat, htargetReach, dif_pos] using hfind
  have hsafe' : localTime (oneStepRecenter (trajectory omega))
        (creationTimeNat m k (oneStepRecenter (trajectory omega)))
        (0 - trajectory omega 1) + 1 < m := by
    change localTime (oneStepRecenter s)
        (creationTimeNat m k (oneStepRecenter s))
        (0 - directionVector e) + 1 < m at hsafe
    simpa only [hsTrajectory, hfirstEq] using hsafe
  have hphysicalCreation :=
    thresholdCreation_of_oneStepRecenter_of_originSafe omega hm
      hk htargetCreation hsafe'
  have hclock : creationTimeNat m k s =
      creationTimeNat m k (oneStepRecenter s) + 1 := by
    rw [← hsTrajectory]
    exact creationTimeNat_eq_of_creation hphysicalCreation
  have horigin : localTime s (creationTimeNat m k s) 0 < m := by
    rw [hclock, ← hsTrajectory,
      ← localTime_oneStepRecenter_origin_add_one omega
        (creationTimeNat m k (oneStepRecenter (trajectory omega)))]
    exact hsafe'
  simpa only [checkerOriginShiftExceptionEvent, Set.mem_compl_iff,
    Set.mem_ofPred_eq, not_le] using horigin

/-! ## The origin-safe one-coordinate window -/

/-- Retain only coordinate values for which restoring the deleted physical
origin visit still leaves the shifted origin strictly below level `m`. -/
noncomputable def originSafeWindow
    (m fixedOrigin : ℕ) (window : Finset ℕ) : Finset ℕ :=
  window.filter fun v ↦ fixedOrigin + v + 1 < m

@[simp] theorem mem_originSafeWindow
    {m fixedOrigin v : ℕ} {window : Finset ℕ} :
    v ∈ originSafeWindow m fixedOrigin window ↔
      v ∈ window ∧ fixedOrigin + v + 1 < m := by
  simp [originSafeWindow]

private theorem gapDeficitCutoff_pos {m : ℕ} (hm : 0 < m) (a : GapScale) :
    0 < gapDeficitCutoff m a := by
  rw [gapDeficitCutoff]
  exact Nat.ceil_pos.mpr (by positivity)

/-- If the shifted origin has strictly smaller fixed local time than the
dominant endpoint, its safety screen removes no value from a below-level
coordinate window. -/
theorem originSafeWindow_eq_self_of_lt
    {m fixedOrigin fixed : ℕ} {window : Finset ℕ}
    (hfixed : fixedOrigin < fixed)
    (hwindow : ∀ v ∈ window, v < m - fixed) :
    originSafeWindow m fixedOrigin window = window := by
  ext v
  simp only [mem_originSafeWindow]
  constructor
  · exact fun hv ↦ hv.1
  · intro hv
    refine ⟨hv, ?_⟩
    have hvm := hwindow v hv
    omega

/-- When the two fixed endpoint local times agree, origin safety deletes
exactly the top failure-count value from an interval ending at `m-fixed`. -/
theorem originSafeWindow_Ico_eq
    {m fixed lower : ℕ} (hfixed : fixed < m) :
    originSafeWindow m fixed (Finset.Ico lower (m - fixed)) =
      Finset.Ico lower (m - fixed - 1) := by
  ext v
  simp only [mem_originSafeWindow, Finset.mem_Ico]
  omega

/-- Removing the common unsafe top point from both the narrow and broad
failure windows does not worsen the Proposition 4.9 ratio.  The key integer
inequality is `(cutoff-1)/(width-2) ≤ cutoff/(width-1)`; hence this consumes
no additional row constant. -/
theorem originSafeFailureWindowMass_le_prop49Envelope
    {m i : ℕ} (a : GapScale)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ i)
    (htranslate : i ≤ m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroCenterRadius m) :
    windowMass i
        (originSafeWindow m i (prop49NarrowFailureWindow m a i)) ≤
      (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        windowMass i
          (originSafeWindow m i
            (shellZeroSourceFailureWindow m (shellWidth48 m) i)) := by
  let width := shellWidth48 m
  let cutoff := gapDeficitCutoff m a
  let broad := originSafeWindow m i
    (shellZeroSourceFailureWindow m width i)
  let narrow := originSafeWindow m i (prop49NarrowFailureWindow m a i)
  let D := literalShellZeroDeviationRadius m
  let W := shellZeroWindowSeparation width
  have hm : 0 < m := by
    have hwm := harithmetic.2.1
    omega
  have hiUpper : i < m := by
    have hwm := harithmetic.2.1
    omega
  have hcutPos : 0 < cutoff := by
    exact gapDeficitCutoff_pos hm a
  have hcutm : cutoff ≤ m := by
    exact hwindow.cut_le_width_pred.trans
      ((Nat.sub_le _ _).trans harithmetic.2.1)
  have hiNarrow : i ≤ m - cutoff := by
    apply Nat.le_sub_of_add_le
    have hmw : m - width + width = m :=
      Nat.sub_add_cancel harithmetic.2.1
    calc
      i + cutoff ≤ i + (width - 1) := by
        exact Nat.add_le_add_left hwindow.cut_le_width_pred i
      _ ≤ (m - width + 1) + (width - 1) :=
        Nat.add_le_add_right htranslate _
      _ = (m - width) + (1 + (width - 1)) := by
        simp only [Nat.add_assoc]
      _ = (m - width) + width := by omega
      _ = m := hmw
  have hbroadEq : broad = Finset.Ico (m - width + 1 - i) (m - i - 1) := by
    dsimp only [broad, width]
    rw [shellZeroSourceFailureWindow]
    exact originSafeWindow_Ico_eq hiUpper
  have hnarrowEq : narrow =
      Finset.Ico (m - cutoff - i) (m - i - 1) := by
    dsimp only [narrow, cutoff]
    rw [prop49NarrowFailureWindow]
    exact originSafeWindow_Ico_eq hiUpper
  have hbroadCard : broad.card = width - 2 := by
    rw [hbroadEq]
    simp only [Nat.card_Ico]
    have hwidthLe : width ≤ m := by
      simpa only [width] using harithmetic.2.1
    have hiw : i ≤ m - width + 1 := by
      simpa only [width] using htranslate
    have hsum : (m - width + 1 - i) + (width - 1) = m - i := by
      omega
    omega
  have hnarrowCard : narrow.card = cutoff - 1 := by
    rw [hnarrowEq]
    simp only [Nat.card_Ico]
    omega
  have hbroadNonempty : broad.Nonempty := by
    apply Finset.card_pos.mp
    rw [hbroadCard]
    omega
  obtain ⟨b, hb, hbmin⟩ :=
    Finset.exists_min_image broad (hlozMass i) hbroadNonempty
  have hlocal := harithmetic.2.2 i hthick
  have hbPos : 0 < hlozMass i b := hlozMass_pos hlocal.1 b
  have hD0 : 0 ≤ D := by
    dsimp only [D, literalShellZeroDeviationRadius,
      shellZeroDeviationRadius, shellZeroCenterRadius]
    exact add_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _) (geometricDeviation_nonneg m))
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact shellZeroWindowSeparation_nonneg _
  have hnarrowSubsetBroad : narrow ⊆ broad := by
    intro v hv
    simp only [narrow, broad, width, mem_originSafeWindow,
      mem_prop49NarrowFailureWindow,
      mem_shellZeroSourceFailureWindow] at hv ⊢
    have hcut : gapDeficitCutoff m a ≤ shellWidth48 m - 1 :=
      hwindow.cut_le_width_pred
    exact ⟨⟨by omega, hv.1.2⟩, hv.2⟩
  have hsmallPoint : ∀ v ∈ narrow,
      hlozMass i v ≤ adjacentLocalRatio i D W * hlozMass i b := by
    intro v hv
    have hvBroad := hnarrowSubsetBroad hv
    apply hlozMass_le_adjacentLocalRatio_mul hlocal.1 hD0 hW0
    · dsimp only [D]
      exact sourceFailure_deviation_le htranslate harithmetic.2.1 hcenter
        (mem_originSafeWindow.mp hvBroad).1
    · dsimp only [D]
      exact sourceFailure_deviation_le htranslate harithmetic.2.1 hcenter
        (mem_originSafeWindow.mp hb).1
    · dsimp only [W, width]
      exact sourceFailure_pair_deviation_sub_le htranslate harithmetic.2.1
        (mem_originSafeWindow.mp hvBroad).1
        (mem_originSafeWindow.mp hb).1
    · simpa only [D] using hlocal.2.1
  have hdenPos : (0 : ℝ) < (width - 2 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hwidth
  have hwidthPredPos : (0 : ℝ) < (width - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (show 1 < width by omega)
  have hcardRatio :
      (cutoff - 1 : ℕ) / (width - 2 : ℕ) ≤
        (cutoff : ℝ) / (width - 1 : ℕ) := by
    rw [div_le_div_iff₀ hdenPos hwidthPredPos]
    have hcutLe : cutoff ≤ width - 1 := by
      simpa only [cutoff, width] using hwindow.cut_le_width_pred
    have hcutOne : 1 ≤ cutoff := hcutPos
    have hwidthOne : 1 ≤ width := by omega
    have hwidthTwo : 2 ≤ width := by omega
    rw [Nat.cast_sub hcutOne, Nat.cast_sub hwidthOne,
      Nat.cast_sub hwidthTwo]
    norm_num
    have hcutLeR : (cutoff : ℝ) ≤ (width : ℝ) - 1 := by
      have hcast : (cutoff : ℝ) ≤ ((width - 1 : ℕ) : ℝ) := by
        exact_mod_cast hcutLe
      rw [Nat.cast_sub hwidthOne] at hcast
      norm_num at hcast ⊢
      exact hcast
    have hnonneg : 0 ≤ (width : ℝ) - 1 - cutoff := by linarith
    calc
      ((cutoff : ℝ) - 1) * ((width : ℝ) - 1) =
          (cutoff : ℝ) * ((width : ℝ) - 2) -
            ((width : ℝ) - 1 - cutoff) := by ring
      _ ≤ (cutoff : ℝ) * ((width : ℝ) - 2) :=
        sub_le_self _ hnonneg
  have hraw := windowMass_small_le_ratio_mul_large
    (i := i) (small := narrow) (large := broad)
    (b := hlozMass i b) (C := adjacentLocalRatio i D W)
    (g := ((cutoff - 1 : ℕ) : ℝ))
    (f := ((width - 2 : ℕ) : ℝ)) hbPos
    (adjacentLocalRatio_nonneg i D W) (Nat.cast_nonneg _) hdenPos
    (by rw [hnarrowCard]) (by rw [hbroadCard]) hsmallPoint
    (fun v hv ↦ hbmin v hv)
  have hratioLocal :
      adjacentLocalRatio i D W * ((cutoff - 1 : ℕ) : ℝ) /
          ((width - 2 : ℕ) : ℝ) ≤
        shellZeroLocalRatioConstant * (cutoff : ℝ) /
          ((width - 1 : ℕ) : ℝ) := by
    calc
      adjacentLocalRatio i D W * ((cutoff - 1 : ℕ) : ℝ) /
            ((width - 2 : ℕ) : ℝ) =
          adjacentLocalRatio i D W *
            (((cutoff - 1 : ℕ) : ℝ) / ((width - 2 : ℕ) : ℝ)) := by ring
      _ ≤ shellZeroLocalRatioConstant *
            (((cutoff - 1 : ℕ) : ℝ) / ((width - 2 : ℕ) : ℝ)) := by
        gcongr
        simpa only [D, W, width] using hlocal.2.2
      _ ≤ shellZeroLocalRatioConstant *
            ((cutoff : ℝ) / ((width - 1 : ℕ) : ℝ)) := by
        gcongr
        exact shellZeroLocalRatioConstant_pos.le
      _ = shellZeroLocalRatioConstant * (cutoff : ℝ) /
            ((width - 1 : ℕ) : ℝ) := by ring
  have hmassNonneg : 0 ≤ windowMass i broad := windowMass_nonneg _ _
  calc
    windowMass i
        (originSafeWindow m i (prop49NarrowFailureWindow m a i)) =
        windowMass i narrow := by rfl
    _ ≤ (adjacentLocalRatio i D W * ((cutoff - 1 : ℕ) : ℝ) /
          ((width - 2 : ℕ) : ℝ)) * windowMass i broad := hraw
    _ ≤ (shellZeroLocalRatioConstant * (cutoff : ℝ) /
          ((width - 1 : ℕ) : ℝ)) * windowMass i broad := by
      gcongr
    _ ≤ (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
          windowMass i broad := by
      gcongr
      simpa only [width, cutoff] using hwindow.coefficient_le
    _ = (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        windowMass i
          (originSafeWindow m i
            (shellZeroSourceFailureWindow m (shellWidth48 m) i)) := by
      rfl

/-- Origin-safe shifted-window ratio.  Strict fixed-endpoint dominance makes
the safety filter vacuous; equality invokes the common-top deletion theorem
above. -/
theorem originSafeShiftedEndpointWindow_prop49_mass_le
    {m fixedOrigin fixed upper : ℕ} (a : GapScale)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hfixed : fixedOrigin ≤ fixed)
    (hthick : m / 2 ≤ fixed)
    (htranslate : fixed ≤ m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (fixed : ℝ)| ≤
      shellZeroCenterRadius m)
    (hupper : m - fixed ≤ upper) :
    windowMass fixed
        (originSafeWindow m fixedOrigin
          (shiftedEndpointWindow fixed upper (prop49NarrowTotalWindow m a))) ≤
      (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        windowMass fixed
          (originSafeWindow m fixedOrigin
            (shiftedEndpointWindow fixed upper
              (shellZeroSourceTotalWindow m (shellWidth48 m)))) := by
  have hcutm : gapDeficitCutoff m a ≤ m := by
    exact hwindow.cut_le_width_pred.trans
      ((Nat.sub_le _ _).trans harithmetic.2.1)
  have hiNarrow : fixed ≤ m - gapDeficitCutoff m a := by
    apply Nat.le_sub_of_add_le
    have hmw : m - shellWidth48 m + shellWidth48 m = m :=
      Nat.sub_add_cancel harithmetic.2.1
    calc
      fixed + gapDeficitCutoff m a ≤
          fixed + (shellWidth48 m - 1) := by
        gcongr
        exact hwindow.cut_le_width_pred
      _ ≤ (m - shellWidth48 m + 1) +
          (shellWidth48 m - 1) := by
        gcongr
      _ = m := by omega
  rw [shiftedEndpointWindow_prop49NarrowTotalWindow hcutm hiNarrow hupper,
    shiftedEndpointWindow_shellZeroSourceTotalWindow htranslate
      harithmetic.2.1 hupper]
  rcases hfixed.lt_or_eq with hlt | rfl
  · rw [originSafeWindow_eq_self_of_lt hlt (by
          intro v hv
          exact (mem_prop49NarrowFailureWindow.mp hv).2),
        originSafeWindow_eq_self_of_lt hlt (by
          intro v hv
          exact (mem_shellZeroSourceFailureWindow.mp hv).2)]
    exact narrowFailureWindowMass_le_prop49Envelope a hwindow harithmetic
      hthick htranslate hcenter
  · exact originSafeFailureWindowMass_le_prop49Envelope a hwindow harithmetic
      hwidth hthick htranslate hcenter

/-! ## Origin-safe canonical source atoms -/

abbrev DominoTiling := Tilings.Tiling

/-- The represented domino containing the shifted image of the physical
origin. -/
def targetOriginBase (t : DominoTiling) (e : Direction) : Point :=
  tilingBase t (0 - directionVector e)

/-- On the checker-opposite histories used below, the origin domino is one
of the source coordinates and hence belongs to the away carrier. -/
def sourceOriginChosen
    {t : DominoTiling} {o : Orientation} {m k : ℕ} (cap : ℕ)
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (horigin : targetOriginBase t e ∈ eta.1.2) :
    TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap) :=
  sourceChosen cap eta (targetOriginBase t e) horigin

@[simp] theorem sourceOriginChosen_base
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (horigin : targetOriginBase t e ∈ eta.1.2) :
    (sourceOriginChosen cap eta e horigin).1.1 = targetOriginBase t e := rfl

/-- Fixed retained-prefix local time at the shifted physical origin. -/
def sourceOriginFixedLocalTime
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction) : ℕ :=
  prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
    eta.1.1.external.start eta.1.1.external.retained (sourceTerminal eta)
    (0 - directionVector e)

/-- Origin-safe accepted broad coordinate window. -/
noncomputable def originSafeAcceptedBaseWindow
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin b : spec.Away) : Finset ℕ :=
  if b = origin then
    originSafeWindow m fixedOrigin
      (spec.acceptedBaseWindow b)
  else spec.acceptedBaseWindow b

/-- Origin-safe accepted narrow coordinate window. -/
noncomputable def originSafeAcceptedScreenedWindow
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin b : spec.Away) : Finset ℕ :=
  if b = origin then
    originSafeWindow m fixedOrigin
      (spec.acceptedScreenedWindow b)
  else spec.acceptedScreenedWindow b

/-- Boolean broad screen used by the exact stopped-product factorization. -/
noncomputable def originSafeBaseAccepts
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide (spec.acceptedBaseProp ell ∧
    fixedOrigin + (ell origin : ℕ) + 1 < m)

/-- Boolean narrow screen used by the exact stopped-product factorization. -/
noncomputable def originSafeScreenedAccepts
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide (spec.acceptedScreenedProp ell ∧
    fixedOrigin + (ell origin : ℕ) + 1 < m)

theorem originSafeBaseAccepts_iff_windows
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away)
    (ell : TruncatedTotals spec.upper)
    (hcoverage : spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
      prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
        spec.terminal b.1) :
    originSafeBaseAccepts m fixedOrigin spec origin ell = true ↔
      ∀ b, (ell b : ℕ) ∈
        originSafeAcceptedBaseWindow m fixedOrigin spec origin b := by
  classical
  simp only [originSafeBaseAccepts, decide_eq_true_eq]
  rw [spec.acceptedBaseProp_iff_windows ell hcoverage]
  constructor
  · rintro ⟨hall, hsafe⟩ b
    by_cases hb : b = origin
    · subst b
      rw [originSafeAcceptedBaseWindow, if_pos rfl,
        mem_originSafeWindow]
      exact ⟨hall origin, hsafe⟩
    · rw [originSafeAcceptedBaseWindow, if_neg hb]
      exact hall b
  · intro hall
    refine ⟨fun b ↦ ?_, ?_⟩
    · have hb := hall b
      by_cases hbo : b = origin
      · rw [originSafeAcceptedBaseWindow, if_pos hbo,
          mem_originSafeWindow] at hb
        exact hb.1
      · rw [originSafeAcceptedBaseWindow, if_neg hbo] at hb
        exact hb
    · have hb := hall origin
      rw [originSafeAcceptedBaseWindow, if_pos rfl,
        mem_originSafeWindow] at hb
      exact hb.2

theorem originSafeScreenedAccepts_iff_windows
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away)
    (ell : TruncatedTotals spec.upper)
    (hcoverage : spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
      prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
        spec.terminal b.1) :
    originSafeScreenedAccepts m fixedOrigin spec origin ell = true ↔
      ∀ b, (ell b : ℕ) ∈
        originSafeAcceptedScreenedWindow m fixedOrigin spec origin b := by
  classical
  simp only [originSafeScreenedAccepts, decide_eq_true_eq]
  rw [spec.acceptedScreenedProp_iff_windows ell hcoverage]
  constructor
  · rintro ⟨hall, hsafe⟩ b
    by_cases hb : b = origin
    · subst b
      rw [originSafeAcceptedScreenedWindow, if_pos rfl,
        mem_originSafeWindow]
      exact ⟨hall origin, hsafe⟩
    · rw [originSafeAcceptedScreenedWindow, if_neg hb]
      exact hall b
  · intro hall
    refine ⟨fun b ↦ ?_, ?_⟩
    · have hb := hall b
      by_cases hbo : b = origin
      · rw [originSafeAcceptedScreenedWindow, if_pos hbo,
          mem_originSafeWindow] at hb
        exact hb.1
      · rw [originSafeAcceptedScreenedWindow, if_neg hbo] at hb
        exact hb
    · have hb := hall origin
      rw [originSafeAcceptedScreenedWindow, if_pos rfl,
        mem_originSafeWindow] at hb
      exact hb.2

theorem originSafeAcceptedScreenedWindow_eq_base
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin b : spec.Away) (hne : b ≠ spec.chosen) :
    originSafeAcceptedScreenedWindow m fixedOrigin spec origin b =
      originSafeAcceptedBaseWindow m fixedOrigin spec origin b := by
  classical
  by_cases hb : b = origin
  · rw [originSafeAcceptedScreenedWindow, if_pos hb,
      originSafeAcceptedBaseWindow, if_pos hb,
      spec.acceptedScreenedWindow_eq_base b hne]
  · rw [originSafeAcceptedScreenedWindow, if_neg hb,
      originSafeAcceptedBaseWindow, if_neg hb,
      spec.acceptedScreenedWindow_eq_base b hne]

theorem originSafeScreenedAccepts_subset_base
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away) {ell : TruncatedTotals spec.upper}
    (h : originSafeScreenedAccepts m fixedOrigin spec origin ell = true) :
    originSafeBaseAccepts m fixedOrigin spec origin ell = true := by
  simp only [originSafeScreenedAccepts, decide_eq_true_eq] at h
  simp only [originSafeBaseAccepts, decide_eq_true_eq]
  exact ⟨spec.acceptedScreenedProp_subset_base h.1, h.2⟩

theorem originSafeBaseAccepts_subset_acceptedBase
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away) {ell : TruncatedTotals spec.upper}
    (h : originSafeBaseAccepts m fixedOrigin spec origin ell = true) :
    spec.acceptedBaseAccepts ell = true := by
  simp only [originSafeBaseAccepts, decide_eq_true_eq] at h
  simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
    decide_eq_true_eq] using h.1

theorem originSafeScreenedAccepts_subset_acceptedBase
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away) {ell : TruncatedTotals spec.upper}
    (h : originSafeScreenedAccepts m fixedOrigin spec origin ell = true) :
    spec.acceptedBaseAccepts ell = true :=
  originSafeBaseAccepts_subset_acceptedBase m fixedOrigin spec origin
    (originSafeScreenedAccepts_subset_base m fixedOrigin spec origin h)

/-- Finite one-coordinate data after imposing the checker-origin safety
screen on one (not necessarily selected) away coordinate. -/
structure OriginSafeAcceptedRatioData
    (cap : ℕ) (C : ℝ) (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away) : Prop where
  coverage : spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
    prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
      spec.terminal b.1
  basePos : 0 < screenMass (spec.pointMass cap) spec.upper
    (fun ell ↦ ∀ b, (ell b : ℕ) ∈
      originSafeAcceptedBaseWindow m fixedOrigin spec origin b)
  screenedUpper : ∀ v ∈ originSafeAcceptedScreenedWindow
    m fixedOrigin spec origin spec.chosen, v < spec.upper spec.chosen
  baseUpper : ∀ v ∈ originSafeAcceptedBaseWindow
    m fixedOrigin spec origin spec.chosen, v < spec.upper spec.chosen
  screenedCap : ∀ v ∈ originSafeAcceptedScreenedWindow
    m fixedOrigin spec origin spec.chosen, v ≤ cap
  baseCap : ∀ v ∈ originSafeAcceptedBaseWindow
    m fixedOrigin spec origin spec.chosen, v ≤ cap
  coordinates : 0 < Fintype.card
    (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1)
  ratio : windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (originSafeAcceptedScreenedWindow
        m fixedOrigin spec origin spec.chosen) ≤
    C * windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (originSafeAcceptedBaseWindow m fixedOrigin spec origin spec.chosen)

/-- The exact conditional product estimate for the origin-safe screen. -/
theorem originSafeConditionalScreenMass_le
    {cap : ℕ} {C : ℝ} (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin : spec.Away)
    (data : OriginSafeAcceptedRatioData cap C m fixedOrigin spec origin) :
    conditionalScreenMass (spec.pointMass cap) spec.upper
      (fun ell ↦ originSafeBaseAccepts m fixedOrigin spec origin ell = true)
      (fun ell ↦
        originSafeScreenedAccepts m fixedOrigin spec origin ell = true) ≤ C := by
  classical
  have hbase : (fun ell ↦
      originSafeBaseAccepts m fixedOrigin spec origin ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈
        originSafeAcceptedBaseWindow m fixedOrigin spec origin b) := by
    funext ell
    apply propext
    exact originSafeBaseAccepts_iff_windows m fixedOrigin spec origin ell
      data.coverage
  have hscreened : (fun ell ↦
      originSafeScreenedAccepts m fixedOrigin spec origin ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈
        originSafeAcceptedScreenedWindow m fixedOrigin spec origin b) := by
    funext ell
    apply propext
    exact originSafeScreenedAccepts_iff_windows m fixedOrigin spec origin ell
      data.coverage
  simp only [hbase, hscreened]
  simpa only [PrefixedCanonicalDominantCandidateWindowSpec.pointMass,
    PrefixedCanonicalDominantCandidateWindowSpec.Away] using
    tilingConditionalScreenMass_le_of_one_coordinate_window_ratio
      (cap := cap) (C := C) spec.t spec.x spec.r spec.D spec.upper
      spec.chosen
      (originSafeAcceptedBaseWindow m fixedOrigin spec origin)
      (originSafeAcceptedScreenedWindow m fixedOrigin spec origin)
      data.basePos
      (fun b hb ↦ originSafeAcceptedScreenedWindow_eq_base
        m fixedOrigin spec origin b hb)
      data.screenedUpper data.baseUpper data.screenedCap data.baseCap
      data.coordinates data.ratio

/-- Every origin-safe broad coordinate still has positive normalized mass.
For strict endpoint dominance the extra screen is vacuous; in the equality
case the broad source interval loses one endpoint but retains `width-2`
positive lattice values. -/
theorem originSafeBaseCoordinateMass_pos
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (origin : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap))
    (fixedOrigin : ℕ)
    (hfixed : fixedOrigin ≤ prefixedTilingFixedBoundaryLocalTime
      ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta) origin.1.1) :
    let spec := sourceProp49Spec eta a candidate hcandidate low cap
    0 < ∑ v : Fin (spec.upper origin),
      if (v : ℕ) ∈ originSafeAcceptedBaseWindow
          m fixedOrigin spec origin origin then
        coordinateMass (spec.pointMass ((SourceFiber eta).coordinateCap cap))
          (spec.upper origin) origin v else 0 := by
  classical
  dsimp only
  let spec := sourceProp49Spec eta a candidate hcandidate low cap
  let i := Fintype.card (TilingCoordinatesAt t ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) origin.1)
  have hcompatible := good.away_orientationCompatible origin
  have hboundaryCard := good.fixedBoundary_eq_coordinateCard hm hk origin.1
    hcompatible
  have hboundaryCard' : prefixedTilingFixedBoundaryLocalTime
      ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta) origin.1.1 = i := by
    exact hboundaryCard
  have hext := good.away_fixedBoundary_external_window hm hk origin
  have hiWindow := hexternalArithmetic _ hext.1 hext.2
  rw [hboundaryCard'] at hiWindow
  have hi : 0 < i := by
    exact card_tilingCoordinatesAt_pos t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) origin.1
  have hmTotal : m ≤ (SourceFiber eta).totalCap :=
    m_le_sourceFiber_totalCap eta
  have hupperM : m ≤ spec.upper origin :=
    hmTotal.trans ((SourceFiber eta).totalCap_lt_upper cap origin).le
  have hcoordinateM : m ≤ (SourceFiber eta).coordinateCap cap :=
    hmTotal.trans ((SourceFiber eta).totalCap_le_coordinateCap cap)
  have hshiftUpper : m - i ≤ spec.upper origin := by omega
  have hwindowEq : spec.acceptedBaseWindow origin =
      shellZeroSourceFailureWindow m (shellWidth48 m) i := by
    calc
      spec.acceptedBaseWindow origin = shiftedEndpointWindow
          (prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
            ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
            (sourceTerminal eta) origin.1.1)
          (spec.upper origin)
          (shellZeroSourceTotalWindow m (shellWidth48 m)) := by
            exact good.acceptedBaseWindow_eq_shifted candidate hcandidate low
              (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) rfl rfl
              hm hk (prop49NarrowTotalWindow m a) origin
      _ = shiftedEndpointWindow i (spec.upper origin)
          (shellZeroSourceTotalWindow m (shellWidth48 m)) := by
            rw [hboundaryCard']
      _ = shellZeroSourceFailureWindow m (shellWidth48 m) i := by
            exact shiftedEndpointWindow_shellZeroSourceTotalWindow
              hiWindow.2.1 harithmetic.2.1 hshiftUpper
  have hfixed' : fixedOrigin ≤ i := by simpa only [hboundaryCard'] using hfixed
  let safeWindow := originSafeWindow m fixedOrigin
    (spec.acceptedBaseWindow origin)
  have hsafeEq : safeWindow = originSafeWindow m fixedOrigin
      (shellZeroSourceFailureWindow m (shellWidth48 m) i) := by
    dsimp only [safeWindow]
    rw [hwindowEq]
  have hsafeUpper : ∀ v ∈ safeWindow, v < spec.upper origin := by
    intro v hv
    rw [hsafeEq] at hv
    have hv' := (mem_originSafeWindow.mp hv).1
    have hv'' := (mem_shellZeroSourceFailureWindow.mp hv').2
    omega
  have hsafeCap : ∀ v ∈ safeWindow,
      v ≤ (SourceFiber eta).coordinateCap cap := by
    intro v hv
    rw [hsafeEq] at hv
    have hv' := (mem_originSafeWindow.mp hv).1
    have hv'' := (mem_shellZeroSourceFailureWindow.mp hv').2
    omega
  have hsafeNonempty : safeWindow.Nonempty := by
    rcases hfixed'.lt_or_eq with hlt | rfl
    · rw [hsafeEq, originSafeWindow_eq_self_of_lt hlt]
      · exact shellZeroSourceFailureWindow_nonempty hiWindow.2.1
          harithmetic.1 harithmetic.2.1
      · intro v hv
        exact (mem_shellZeroSourceFailureWindow.mp hv).2
    · rw [hsafeEq, shellZeroSourceFailureWindow,
        originSafeWindow_Ico_eq (by omega)]
      apply Finset.card_pos.mp
      simp only [Nat.card_Ico]
      have htranslate' : i ≤ m - shellWidth48 m + 1 := hiWindow.2.1
      have hsum : i + (m - shellWidth48 m + 1 - i) =
          m - shellWidth48 m + 1 := Nat.add_sub_of_le htranslate'
      have hmwidth : m - shellWidth48 m + shellWidth48 m = m :=
        Nat.sub_add_cancel harithmetic.2.1
      omega
  have hwindowPos : 0 < windowMass i safeWindow :=
    windowMass_pos hi hsafeNonempty
  have hdenPos : 0 < ∑ j : Fin (spec.upper origin),
      spec.pointMass ((SourceFiber eta).coordinateCap cap) origin j := by
    let v0 : Fin (spec.upper origin) :=
      ⟨0, (SourceFiber eta).upper_pos cap origin⟩
    have hv0 : 0 < spec.pointMass
        ((SourceFiber eta).coordinateCap cap) origin v0 := by
      change 0 < tilingAwayPointMass
        (cap := (SourceFiber eta).coordinateCap cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) origin 0
      exact tilingAwayExactTotalMass_zero_pos
        (cap := (SourceFiber eta).coordinateCap cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) origin
    exact hv0.trans_le (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (spec.upper origin) ↦
        spec.pointMass ((SourceFiber eta).coordinateCap cap) origin j)
      (fun j _ ↦ tilingAwayExactTotalMass_nonneg t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) origin j)
      (Finset.mem_univ v0))
  have heq := sum_tilingAway_coordinateMass_window t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).distinguished cap) spec.upper origin
    safeWindow hsafeUpper hsafeCap hi
  have hdenPos' : 0 < ∑ j : Fin (spec.upper origin),
      tilingAwayPointMass (cap := (SourceFiber eta).coordinateCap cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) origin j := by
    exact hdenPos
  change 0 < ∑ v : Fin (spec.upper origin),
    if (v : ℕ) ∈ originSafeAcceptedBaseWindow
        m fixedOrigin spec origin origin then
      coordinateMass
        (spec.pointMass ((SourceFiber eta).coordinateCap cap))
        (spec.upper origin) origin v else 0
  unfold originSafeAcceptedBaseWindow
  split
  · change 0 < ∑ v : Fin (spec.upper origin),
      if (v : ℕ) ∈ safeWindow then
        coordinateMass
          (tilingAwayPointMass t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap)
            ((SourceFiber eta).distinguished cap))
          spec.upper origin v else 0
    have hratio : 0 < windowMass i safeWindow /
        ∑ j : Fin (spec.upper origin),
          tilingAwayPointMass
            (cap := (SourceFiber eta).coordinateCap cap) t
            ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
            ((SourceFiber eta).distinguished cap) origin j :=
      div_pos hwindowPos hdenPos'
    exact heq.symm ▸ hratio
  · rename_i hne
    exact (hne rfl).elim

/-- The retained-prefix local time at the shifted physical origin is bounded
by the fixed dominant endpoint of its represented domino. -/
theorem sourceOriginFixedLocalTime_le
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (horigin : targetOriginBase t e ∈ eta.1.2) :
    sourceOriginFixedLocalTime eta e ≤
      prefixedTilingFixedBoundaryLocalTime
        ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (sourceTerminal eta)
        (sourceOriginChosen cap eta e horigin).1.1 := by
  change prefixedTilingFixedBoundaryLocalTime
      ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta)
      (0 - directionVector e) ≤
    prefixedTilingFixedBoundaryLocalTime
      ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta)
      (sourceOriginChosen cap eta e horigin).1.1
  have hdominant := away_fixedBoundary_partner_le_base eta
    (sourceOriginChosen cap eta e horigin)
  have hbase : (sourceOriginChosen cap eta e horigin).1.1 =
      tilingBase t (0 - directionVector e) := rfl
  rcases point_eq_tilingBase_or_partner_base t
      (0 - directionVector e) with hp | hp
  · rw [hp, hbase]
  · rw [hp, hbase]
    exact hdominant

/-- The source Proposition 4.9 ratio survives the extra checker-origin
screen.  If the original chosen coordinate is different, the chosen windows
are unchanged.  If it is the origin coordinate, the common-top deletion
estimate applies. -/
theorem sourceOriginSafe_chosen_ratio
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    let spec := sourceProp49Spec eta a candidate hcandidate low cap
    let origin := sourceOriginChosen cap eta e horigin
    windowMass
        (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
        (originSafeAcceptedScreenedWindow m
          (sourceOriginFixedLocalTime eta e) spec origin spec.chosen) ≤
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal *
        windowMass
          (Fintype.card
            (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
          (originSafeAcceptedBaseWindow m
            (sourceOriginFixedLocalTime eta e) spec origin spec.chosen) := by
  classical
  dsimp only
  let spec := sourceProp49Spec eta a candidate hcandidate low cap
  let origin := sourceOriginChosen cap eta e horigin
  change windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (originSafeAcceptedScreenedWindow m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen) ≤
    (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal *
      windowMass
        (Fintype.card
          (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
        (originSafeAcceptedBaseWindow m
          (sourceOriginFixedLocalTime eta e) spec origin spec.chosen)
  have hratio := (good.acceptedRatioData a candidate hcandidate low hm hk
    hwindow harithmetic hexternalArithmetic cap).ratio
  by_cases hchosen : spec.chosen = origin
  · have hnarrow : prop49NarrowTotalWindow m a ⊆
        shellZeroSourceTotalWindow m (shellWidth48 m) :=
      prop49NarrowTotalWindow_subset_source
        ((show 1 ≤ 2 by norm_num).trans harithmetic.1)
        harithmetic.2.1 hwindow.cut_le_width_pred
    have hdominant := sourceChosen_fixedBoundary_partner_le_base (cap := cap)
      eta candidate hcandidate
    have hS : spec.chosen.1.1 ∈ spec.S := by
      change (sourceChosen cap eta candidate hcandidate).1.1 ∈ eta.1.2
      simpa only [sourceChosen_base] using hcandidate
    have hext := good.away_fixedBoundary_external_window (cap := cap) hm hk
      spec.chosen
    have hbaseEq := spec.acceptedBaseWindow_chosen hdominant hS hext rfl
    have hscreenedEq := spec.acceptedScreenedWindow_chosen hdominant hS hext
      rfl hnarrow
    have hcompatible := good.away_orientationCompatible (cap := cap)
      spec.chosen
    have hboundaryCard := good.fixedBoundary_eq_coordinateCard hm hk
      spec.chosen.1 hcompatible
    have hboundaryCardFiber : prefixedTilingFixedBoundaryLocalTime
        ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (sourceTerminal eta)
        spec.chosen.1.1 =
        Fintype.card
          (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) := by
      change prefixedTilingFixedBoundaryLocalTime
          eta.1.1.external.initial.1 eta.1.1.external.start
          eta.1.1.external.retained (sourceTerminal eta) spec.chosen.1.1 =
        Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
          eta.1.1.external.retained spec.chosen.1)
      exact hboundaryCard
    have hboundaryCardSpec : prefixedTilingFixedBoundaryLocalTime
        spec.initial spec.x spec.r spec.terminal spec.chosen.1.1 =
        Fintype.card
          (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) := by
      change prefixedTilingFixedBoundaryLocalTime
          eta.1.1.external.initial.1 eta.1.1.external.start
          eta.1.1.external.retained (sourceTerminal eta) spec.chosen.1.1 =
        Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
          eta.1.1.external.retained spec.chosen.1)
      exact hboundaryCard
    have hiWindow := hexternalArithmetic _ hext.1 hext.2
    rw [hboundaryCardFiber] at hiWindow
    have hmTotal : m ≤ (SourceFiber eta).totalCap :=
      m_le_sourceFiber_totalCap eta
    have hupperM : m ≤ spec.upper spec.chosen :=
      hmTotal.trans ((SourceFiber eta).totalCap_lt_upper cap spec.chosen).le
    have hshiftUpper : m - Fintype.card
        (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) ≤
        spec.upper spec.chosen := by omega
    have hfixed : sourceOriginFixedLocalTime eta e ≤
        prefixedTilingFixedBoundaryLocalTime
          ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (sourceTerminal eta)
          spec.chosen.1.1 := by
      rw [hchosen]
      exact sourceOriginFixedLocalTime_le eta e horigin
    have hsafeScreened : originSafeAcceptedScreenedWindow m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen =
        originSafeWindow m (sourceOriginFixedLocalTime eta e)
          (spec.acceptedScreenedWindow spec.chosen) := by
      unfold originSafeAcceptedScreenedWindow
      split
      · rfl
      · rename_i hne
        exact (hne hchosen).elim
    have hsafeBase : originSafeAcceptedBaseWindow m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen =
        originSafeWindow m (sourceOriginFixedLocalTime eta e)
          (spec.acceptedBaseWindow spec.chosen) := by
      unfold originSafeAcceptedBaseWindow
      split
      · rfl
      · rename_i hne
        exact (hne hchosen).elim
    rw [hsafeScreened, hsafeBase, hscreenedEq, hbaseEq,
      hboundaryCardSpec]
    have hfixedCard : sourceOriginFixedLocalTime eta e ≤
        Fintype.card
          (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) :=
      hfixed.trans_eq hboundaryCardFiber
    have hsafeRatio := originSafeShiftedEndpointWindow_prop49_mass_le
      (fixedOrigin := sourceOriginFixedLocalTime eta e)
      (fixed := Fintype.card
        (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (upper := spec.upper spec.chosen) a hwindow harithmetic hwidth
      hfixedCard hiWindow.1 hiWindow.2.1 hiWindow.2.2 hshiftUpper
    simpa only [spec, sourceProp49Spec, sourceParameters,
      HLOZPrefixedAllCreationCanonicalRefinement.Parameters.toSpec,
      prop49CandidateRatioEnvelope_toReal
        prop49WindowRatioConstant_pos.le] using hsafeRatio
  · have hsafeScreened : originSafeAcceptedScreenedWindow m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen =
        spec.acceptedScreenedWindow spec.chosen := by
      unfold originSafeAcceptedScreenedWindow
      split
      · rename_i heq
        exact (hchosen heq).elim
      · rfl
    have hsafeBase : originSafeAcceptedBaseWindow m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen =
        spec.acceptedBaseWindow spec.chosen := by
      unfold originSafeAcceptedBaseWindow
      split
      · rename_i heq
        exact (hchosen heq).elim
      · rfl
    rw [hsafeScreened, hsafeBase]
    exact hratio

theorem originSafeAcceptedBaseWindow_subset
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin b : spec.Away) :
    originSafeAcceptedBaseWindow m fixedOrigin spec origin b ⊆
      spec.acceptedBaseWindow b := by
  intro v hv
  unfold originSafeAcceptedBaseWindow at hv
  split at hv
  · exact (mem_originSafeWindow.mp hv).1
  · exact hv

theorem originSafeAcceptedScreenedWindow_subset
    (m fixedOrigin : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (origin b : spec.Away) :
    originSafeAcceptedScreenedWindow m fixedOrigin spec origin b ⊆
      spec.acceptedScreenedWindow b := by
  intro v hv
  unfold originSafeAcceptedScreenedWindow at hv
  split at hv
  · exact (mem_originSafeWindow.mp hv).1
  · exact hv

/-- Fully checked origin-safe ratio data on a canonical source atom. -/
theorem sourceOriginSafeAcceptedRatioData
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    let spec := sourceProp49Spec eta a candidate hcandidate low cap
    let origin := sourceOriginChosen cap eta e horigin
    OriginSafeAcceptedRatioData ((SourceFiber eta).coordinateCap cap)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal
      m (sourceOriginFixedLocalTime eta e) spec origin := by
  classical
  dsimp only
  let spec := sourceProp49Spec eta a candidate hcandidate low cap
  let origin := sourceOriginChosen cap eta e horigin
  change OriginSafeAcceptedRatioData ((SourceFiber eta).coordinateCap cap)
    (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal
    m (sourceOriginFixedLocalTime eta e) spec origin
  have data := good.acceptedRatioData a candidate hcandidate low hm hk
    hwindow harithmetic hexternalArithmetic cap
  refine {
    coverage := data.coverage
    basePos := ?_
    screenedUpper := fun v hv ↦ data.screenedUpper v
      (originSafeAcceptedScreenedWindow_subset m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen hv)
    baseUpper := fun v hv ↦ data.baseUpper v
      (originSafeAcceptedBaseWindow_subset m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen hv)
    screenedCap := fun v hv ↦ data.screenedCap v
      (originSafeAcceptedScreenedWindow_subset m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen hv)
    baseCap := fun v hv ↦ data.baseCap v
      (originSafeAcceptedBaseWindow_subset m
        (sourceOriginFixedLocalTime eta e) spec origin spec.chosen hv)
    coordinates := data.coordinates
    ratio := sourceOriginSafe_chosen_ratio a candidate hcandidate low good e
      horigin hm hk hwindow harithmetic hwidth hexternalArithmetic }
  rw [screenMass_all_coordinate_windows_eq_prod]
  apply Finset.prod_pos
  intro b _hb
  by_cases hbo : b = origin
  · subst b
    exact originSafeBaseCoordinateMass_pos a candidate hcandidate low good hm
      hk harithmetic hwidth hexternalArithmetic origin
      (sourceOriginFixedLocalTime eta e)
      (sourceOriginFixedLocalTime_le eta e horigin)
  · have hwindowEq : originSafeAcceptedBaseWindow m
        (sourceOriginFixedLocalTime eta e) spec origin b =
        spec.acceptedBaseWindow b := by
      unfold originSafeAcceptedBaseWindow
      split
      · rename_i heq
        exact (hbo heq).elim
      · rfl
    rw [hwindowEq]
    exact good.acceptedBaseCoordinateMass_pos candidate hcandidate low hm hk
      harithmetic hexternalArithmetic (prop49NarrowTotalWindow m a) b

/-! ## Origin-safe stopped fibres -/

noncomputable def sourceOriginSafeBasePredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)) : Prop :=
  (SourceFiber eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
      ((SourceFiber eta).upper cap)
      (fun ell ↦ originSafeBaseAccepts m
        (sourceOriginFixedLocalTime eta e)
        (sourceProp49Spec eta a candidate hcandidate low cap)
        (sourceOriginChosen cap eta e horigin) ell = true)
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) q).2)

noncomputable def sourceOriginSafeScreenedPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)) : Prop :=
  (SourceFiber eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
      ((SourceFiber eta).upper cap)
      (fun ell ↦ originSafeScreenedAccepts m
        (sourceOriginFixedLocalTime eta e)
        (sourceProp49Spec eta a candidate hcandidate low cap)
        (sourceOriginChosen cap eta e horigin) ell = true)
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) q).2)

theorem sourceOriginSafeScreenedPredicate_subset_base
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (h : sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
      horigin cap q) :
    sourceOriginSafeBasePredicate eta a candidate hcandidate low e horigin
      cap q := by
  rcases h with ⟨hatom, ell, hell, htotal⟩
  exact ⟨hatom, ell,
    originSafeScreenedAccepts_subset_base m
      (sourceOriginFixedLocalTime eta e)
      (sourceProp49Spec eta a candidate hcandidate low cap)
      (sourceOriginChosen cap eta e horigin) hell,
    htotal⟩

theorem sourceOriginSafeBase_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)) :
    sourceOriginSafeBasePredicate eta a candidate hcandidate low e horigin
        cap q ∧
      PrefixedTilingStoppingAccepted ((SourceFiber eta).stoppingTime cap)
        ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
        ((SourceFiber eta).tail cap) ↔
      (SourceFiber eta).selected cap
          ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap)
            ((SourceFiber eta).distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
          ((SourceFiber eta).upper cap)
          (fun ell ↦ originSafeBaseAccepts m
            (sourceOriginFixedLocalTime eta e)
            (sourceProp49Spec eta a candidate hcandidate low cap)
            (sourceOriginChosen cap eta e horigin) ell = true)
          ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap)
            ((SourceFiber eta).distinguished cap) q).2) := by
  let cert := sourceRecoveryCertificate eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (prop49NarrowTotalWindow m a) hm hk (by
      simp only [mem_shellZeroSourceTotalWindow]
      omega)
  apply allCreationScreenedPredicate_factorization_of_reconstructed
      (SourceSupportData t o m k) eta cap
      (fun ell ↦ originSafeBaseAccepts m
        (sourceOriginFixedLocalTime eta e)
        (sourceProp49Spec eta a candidate hcandidate low cap)
        (sourceOriginChosen cap eta e horigin) ell = true)
      (q := q)
  intro q'
  dsimp only
  intro hselected hscreen
  apply cert.recover cap q' hselected
  rcases hscreen with ⟨ell, hell, htotal⟩
  exact ⟨ell,
    originSafeBaseAccepts_subset_acceptedBase m
      (sourceOriginFixedLocalTime eta e)
      (sourceProp49Spec eta a candidate hcandidate low cap)
      (sourceOriginChosen cap eta e horigin) hell,
    htotal⟩

theorem sourceOriginSafeScreened_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)) :
    sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
        horigin cap q ∧
      PrefixedTilingStoppingAccepted ((SourceFiber eta).stoppingTime cap)
        ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
        ((SourceFiber eta).tail cap) ↔
      (SourceFiber eta).selected cap
          ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap)
            ((SourceFiber eta).distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
          ((SourceFiber eta).upper cap)
          (fun ell ↦ originSafeScreenedAccepts m
            (sourceOriginFixedLocalTime eta e)
            (sourceProp49Spec eta a candidate hcandidate low cap)
            (sourceOriginChosen cap eta e horigin) ell = true)
          ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap)
            ((SourceFiber eta).distinguished cap) q).2) := by
  let cert := sourceRecoveryCertificate eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (prop49NarrowTotalWindow m a) hm hk (by
      simp only [mem_shellZeroSourceTotalWindow]
      omega)
  apply allCreationScreenedPredicate_factorization_of_reconstructed
      (SourceSupportData t o m k) eta cap
      (fun ell ↦ originSafeScreenedAccepts m
        (sourceOriginFixedLocalTime eta e)
        (sourceProp49Spec eta a candidate hcandidate low cap)
        (sourceOriginChosen cap eta e horigin) ell = true)
      (q := q)
  intro q'
  dsimp only
  intro hselected hscreen
  apply cert.recover cap q' hselected
  rcases hscreen with ⟨ell, hell, htotal⟩
  exact ⟨ell,
    originSafeScreenedAccepts_subset_acceptedBase m
      (sourceOriginFixedLocalTime eta e)
      (sourceProp49Spec eta a candidate hcandidate low cap)
      (sourceOriginChosen cap eta e horigin) hell,
    htotal⟩

def sourceOriginSafeBaseFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceOriginSafeBasePredicate eta a candidate hcandidate low e horigin
      cap))

def sourceOriginSafeScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
      horigin cap))

def sourceOriginSafeNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2) :
    Set WalkPath :=
  ⋃ cap, sourceOriginSafeScreenedFiber eta a candidate hcandidate low e
    horigin cap

theorem measurableSet_sourceOriginSafeScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ) :
    MeasurableSet (sourceOriginSafeScreenedFiber eta a candidate hcandidate
      low e horigin cap) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).isStoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
      horigin cap)

theorem measurableSet_sourceOriginSafeNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2) :
    MeasurableSet (sourceOriginSafeNear eta a candidate hcandidate low e
      horigin) :=
  MeasurableSet.iUnion fun cap ↦
    measurableSet_sourceOriginSafeScreenedFiber eta a candidate hcandidate
      low e horigin cap

private theorem sourceOriginCoordinateCap_mono
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) {cap cap' : ℕ}
    (hcap : cap ≤ cap') :
    (SourceFiber eta).coordinateCap cap ≤
      (SourceFiber eta).coordinateCap cap' := by
  change max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap ≤
    max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap'
  omega

private theorem sourceOriginSafeScreenedPredicate_cast
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap))
    (hscreen : sourceOriginSafeScreenedPredicate eta a candidate hcandidate
      low e horigin cap q) :
    sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
      horigin cap' (castAllCreationCappedCoordinates eta.1.1
        (sourceOriginCoordinateCap_mono eta hcap) q) := by
  classical
  rcases hscreen with ⟨hpred, ell, hell, htotal⟩
  refine ⟨?_, ell, ?_, ?_⟩
  · exact orientedAllCreationStoppedAtomPredicate_cast
      o m k (SourceSupportAt t o m) eta.1.2 eta.1.1
      (sourceOriginCoordinateCap_mono eta hcap) q hpred haccepted
  · exact hell
  · intro b
    simp only [OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.distinguished] at htotal b ⊢
    calc
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (fun j ↦ (castAllCreationCappedCoordinates eta.1.1
            (sourceOriginCoordinateCap_mono eta hcap) q j : ℕ)) b.1 :=
        tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 := by
        simp only [coe_castAllCreationCappedCoordinates]
      _ = tilingAwayTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained
            (supportComplementDistinguished t eta.1.1.external.start
              eta.1.1.external.retained eta.1.2) q).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _).symm
      _ = ell b := htotal b

theorem monotone_sourceOriginSafeScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2) :
    Monotone fun cap ↦ sourceOriginSafeScreenedFiber eta a candidate
      hcandidate low e horigin cap := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let q' := castAllCreationCappedCoordinates eta.1.1
    (sourceOriginCoordinateCap_mono eta hcap) q.1
  have haccepted' := prefixedStoppingAccepted_castAllCreation
    m k eta.1.1 (sourceOriginCoordinateCap_mono eta hcap) q.1 q.2.2
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact sourceOriginSafeScreenedPredicate_cast eta a candidate
      hcandidate low e horigin hcap q.1 q.2.2 q.2.1
  · rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((SourceFiber eta).isStoppingTime cap')
      ((SourceFiber eta).initial cap') t ((SourceFiber eta).start cap')
      ((SourceFiber eta).retained cap') (fun j ↦ (q' j : ℕ))
      ((SourceFiber eta).tail cap') haccepted']
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((SourceFiber eta).isStoppingTime cap)
      ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
      ((SourceFiber eta).tail cap) q.2.2] at hq
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail, q',
      coe_castAllCreationCappedCoordinates] using hq

/-- The extra coordinate screen is the literal path-space target-origin
safety condition on every accepted stopped cylinder. -/
theorem sourceOriginSafeBaseFiber_subset_targetOriginSafe
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ) :
    sourceOriginSafeBaseFiber eta a candidate hcandidate low e horigin cap ⊆
      targetOriginSafe m k e := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let v := prefixedTilingInsertionPrefixList
    ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
    ((SourceFiber eta).tail cap)
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
    ((SourceFiber eta).tail cap) (stepsOfWalk s) hq
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [v, sq] using hp'
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
      ((SourceFiber eta).coordinateCap cap) := by
    simpa only [v,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail] using
      (prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) q.1)
  have hcreationQ : ThresholdCreation sq m k v.length := by
    have hstop := q.2.2
    change truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at hstop
    exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) v.length _ hlt).mp hstop
  have hcreationS : ThresholdCreation s m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mpr hcreationQ
  have htime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hcreationS
  rcases q.2.1.2 with ⟨ell, hell, htotal⟩
  have hsafe : sourceOriginFixedLocalTime eta e +
      (ell (sourceOriginChosen cap eta e horigin) : ℕ) + 1 < m := by
    have hell' :
        (sourceProp49Spec eta a candidate hcandidate low cap).acceptedBaseProp
            ell ∧
          sourceOriginFixedLocalTime eta e +
            (ell (sourceOriginChosen cap eta e horigin) : ℕ) + 1 < m := by
      simpa only [originSafeBaseAccepts, decide_eq_true_eq] using hell
    exact hell'.2
  have hpath : finitePathList (pathPrefix sq v.length) =
      prefixedTilingPrefixPointPath ((SourceFiber eta).initial cap)
        ((SourceFiber eta).start cap)
        (tilingInsertGapVector t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ)))
        (sourceTerminal eta) := by
    rw [← sourceTerminal_eq_coordinates eta q.1]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q.1 j : ℕ))
      eta.1.1.external.tail rfl
  let origin := sourceOriginChosen cap eta e horigin
  have hlocalQ : localTime sq v.length (0 - directionVector e) =
      sourceOriginFixedLocalTime eta e +
        tilingDominoTotal t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
          origin.1 := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
        (sourceTerminal eta) origin.1 (0 - directionVector e)]
    · rfl
    · exact sourceOriginChosen_base eta e horigin |>.symm
  have htotalOrigin : tilingDominoTotal t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ)) origin.1 =
      ell origin := by
    rw [← tilingAwayTotal_split_eq_dominoTotal t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      ((SourceFiber eta).distinguished cap) q.1 origin]
    exact htotal origin
  change localTime s (creationTimeNat m k s)
      (0 - directionVector e) + 1 < m
  rw [htime, localTime_eq_of_pathPrefix_eq hp, hlocalQ, htotalOrigin]
  exact hsafe

theorem sourceOriginSafeBaseFiber_subset_previous
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ) :
    sourceOriginSafeBaseFiber eta a candidate hcandidate low e horigin cap ⊆
      targetOriginSafe m k e ∩ thresholdReachStage m k := by
  intro s hs
  refine ⟨sourceOriginSafeBaseFiber_subset_targetOriginSafe eta a candidate
    hcandidate low e horigin cap hs, ?_⟩
  rcases hs with ⟨hvalid, hevent⟩
  have hatom := (SourceFiber eta).atom_sound cap ⟨hvalid,
    prefixedTilingPreStoppingFiberEvent_mono
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).tail cap) (fun _q hq ↦ hq.1) hevent⟩
  exact hatom.1.2.1

/-- The complete origin-safe conditional refinement on one eligible source
atom.  Its past piece is the literal target-safe reaching stage intersected
with the exact stopped history atom. -/
noncomputable def sourceOriginSafeRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    OrientedAllCreationConditionalRefinementData (SourceFiber eta)
      (historyPiece t o m k (SourceSupportAt t o m)
        (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta))
      (historyPiece t o m k (SourceSupportAt t o m)
          (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) ∩
        sourceOriginSafeNear eta a candidate hcandidate low e horigin)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  basePredicate := sourceOriginSafeBasePredicate eta a candidate hcandidate
    low e horigin
  screenedPredicate := sourceOriginSafeScreenedPredicate eta a candidate
    hcandidate low e horigin
  base_subset_atom := fun _cap _q hq ↦ hq.1
  screened_subset_basePredicate := fun cap q hq ↦
    sourceOriginSafeScreenedPredicate_subset_base eta a candidate hcandidate
      low e horigin cap q hq
  baseAccepts := fun cap ell ↦ originSafeBaseAccepts m
    (sourceOriginFixedLocalTime eta e)
    (sourceProp49Spec eta a candidate hcandidate low cap)
    (sourceOriginChosen cap eta e horigin) ell
  screenedAccepts := fun cap ell ↦ originSafeScreenedAccepts m
    (sourceOriginFixedLocalTime eta e)
    (sourceProp49Spec eta a candidate hcandidate low cap)
    (sourceOriginChosen cap eta e horigin) ell
  screened_subset_base := fun cap ell hell ↦
    originSafeScreenedAccepts_subset_base m
      (sourceOriginFixedLocalTime eta e)
      (sourceProp49Spec eta a candidate hcandidate low cap)
      (sourceOriginChosen cap eta e horigin) hell
  base_factorization := fun cap q ↦ sourceOriginSafeBase_factorization eta
    a candidate hcandidate low e horigin hm hk cap q
  screened_factorization := fun cap q ↦
    sourceOriginSafeScreened_factorization eta a candidate hcandidate low e
      horigin hm hk cap q
  base_mass_pos := fun cap ↦ by
    let spec := sourceProp49Spec eta a candidate hcandidate low cap
    let origin := sourceOriginChosen cap eta e horigin
    have data := sourceOriginSafeAcceptedRatioData a candidate hcandidate low
      good e horigin hm hk hwindow harithmetic hwidth hexternalArithmetic
      (cap := cap)
    change 0 < screenMass
      (spec.pointMass ((SourceFiber eta).coordinateCap cap)) spec.upper
      (fun ell ↦ originSafeBaseAccepts m
        (sourceOriginFixedLocalTime eta e) spec origin ell = true)
    have heq : (fun ell ↦ originSafeBaseAccepts m
          (sourceOriginFixedLocalTime eta e) spec origin ell = true) =
        (fun ell ↦ ∀ b, (ell b : ℕ) ∈
          originSafeAcceptedBaseWindow m
            (sourceOriginFixedLocalTime eta e) spec origin b) := by
      funext ell
      apply propext
      exact originSafeBaseAccepts_iff_windows m
        (sourceOriginFixedLocalTime eta e) spec origin ell data.coverage
    simpa only [heq] using data.basePos
  base_subset_piece := by
    intro cap s hs
    have hsafe : s ∈ targetOriginSafe m k e ∩ thresholdReachStage m k :=
      sourceOriginSafeBaseFiber_subset_previous eta a candidate hcandidate
        low e horigin cap hs
    have hatom : s ∈ orientedAllCreationSupportTraceAtom t o m k
        (SourceSupportAt t o m) eta.1.1 eta.1.2 := by
      apply (SourceFiber eta).atom_sound cap
      exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
        ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).tail cap) (fun _q hq ↦ hq.1) hs.2⟩
    exact ⟨hsafe, hatom⟩
  monotone_screened := monotone_sourceOriginSafeScreenedFiber eta a candidate
    hcandidate low e horigin
  transition_covered := by
    intro s hs
    exact hs.2.2
  product_bound := fun cap ↦ by
    let spec := sourceProp49Spec eta a candidate hcandidate low cap
    let origin := sourceOriginChosen cap eta e horigin
    change conditionalScreenMass
      (spec.pointMass ((SourceFiber eta).coordinateCap cap)) spec.upper
      (fun ell ↦ originSafeBaseAccepts m
        (sourceOriginFixedLocalTime eta e) spec origin ell = true)
      (fun ell ↦ originSafeScreenedAccepts m
        (sourceOriginFixedLocalTime eta e) spec origin ell = true) ≤
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal
    exact originSafeConditionalScreenMass_le m
      (sourceOriginFixedLocalTime eta e) spec origin
      (sourceOriginSafeAcceptedRatioData a candidate hcandidate low good e
        horigin hm hk hwindow harithmetic hwidth hexternalArithmetic
        (cap := cap))

/-! ## The filtered target family -/

/-- Source eligibility strengthened by requiring the shifted physical-origin
domino to be one of the source coordinates. -/
structure OriginSafeSourceProp49EligibleHistory
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (e : Direction) (eta : SourceSupportedIndex t o m k) : Prop where
  source : SourceProp49EligibleHistory eta
  origin_mem : targetOriginBase t e ∈ eta.1.2

noncomputable def sourceOriginSafeCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (candidate : Point) : Set WalkPath := by
  classical
  exact if horigin : targetOriginBase t e ∈ eta.1.2 then
    if hcandidate : candidate ∈ eta.1.2 then
      sourceOriginSafeNear eta a candidate hcandidate low e horigin
    else ∅
  else ∅

theorem measurableSet_sourceOriginSafeCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (candidate : Point) :
    MeasurableSet (sourceOriginSafeCandidateNear eta a low e candidate) := by
  classical
  simp only [sourceOriginSafeCandidateNear]
  split
  · split
    · exact measurableSet_sourceOriginSafeNear eta a candidate _ low e _
    · exact MeasurableSet.empty
  · exact MeasurableSet.empty

/-- The target source family before restoring the fixed checker direction. -/
noncomputable def originSafeTargetCoordinateData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    FilteredOrientedAllCreationLowCoordinateData t o m k
      (initialBudget48 m)
      (targetOriginSafe m k e ∩ thresholdReachStage m k)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  supportAt := SourceSupportAt t o m
  supportData := SourceSupportData t o m k
  previous_measurable := (measurableSet_targetOriginSafe m k e).inter
    (measurableSet_thresholdReachStage m k)
  ratio_ne_top := prop49CandidateRatioEnvelope_ne_top _ _ _
  eligible := OriginSafeSourceProp49EligibleHistory e
  eligible_card := fun _eta heligible ↦ heligible.source.card_le
  near := fun eta candidate ↦
    sourceOriginSafeCandidateNear eta a low e candidate
  near_measurable := fun eta candidate ↦
    measurableSet_sourceOriginSafeCandidateNear eta a low e candidate
  refinement := by
    intro eta candidate heligible hcandidate
    have href := sourceOriginSafeRefinement eta a candidate hcandidate low e
      heligible.origin_mem heligible.source.good hm hk hwindow harithmetic
      hwidth hexternalArithmetic
    simpa only [sourceOriginSafeCandidateNear, heligible.origin_mem,
      hcandidate, dite_true] using href

/-- The stopped-history family on the recentered target row. -/
noncomputable def originSafeTargetFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point
      (targetOriginSafe m k e ∩ thresholdReachStage m k)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  (originSafeTargetCoordinateData (t := t) (o := o) a low e hm hk hwindow
    harithmetic hwidth hexternalArithmetic).family

/-- Exact candidate containment criterion on a good origin-safe target atom. -/
theorem originSafeTargetNext_subset_someCandidate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction) (next : Set WalkPath)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnext : ∀ s ∈ next,
      ∃ (eta : SourceSupportedIndex t o m k) (candidate : Point),
        s ∈ historyPiece t o m k (SourceSupportAt t o m)
          (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) ∧
        OriginSafeSourceProp49EligibleHistory e eta ∧
        candidate ∈ eta.1.2 ∧
        s ∈ sourceOriginSafeCandidateNear eta a low e candidate) :
    next ⊆ (originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic).someCandidate := by
  exact (originSafeTargetCoordinateData a low e hm hk hwindow harithmetic
    hwidth hexternalArithmetic).next_subset_someCandidate hnext

/-! ## Fixed-direction stopped-family transport -/

/-- Pull a stopped-candidate family through one fixed checker prefix.  The
common `1/4` cylinder factor cancels in every coordinate ratio. -/
noncomputable def checkerFixedPrefixFamily
    {History Candidate : Type*} [Countable History]
    {targetPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (e : Direction)
    (family : StoppedHistoryCandidateFamily History Candidate targetPrevious
      budget ratio)
    (near_measurable : ∀ h x, MeasurableSet (family.near h x)) :
    StoppedHistoryCandidateFamily History Candidate
      (checkerPrefixedPreimage e targetPrevious) budget ratio where
  piece := fun h ↦ checkerPrefixedPreimage e (family.piece h)
  candidates := family.candidates
  near := fun h x ↦ checkerPrefixedPreimage e (family.near h x)
  piece_pairwise := by
    intro h h' hne
    exact Set.disjoint_left.mpr fun _ hs hs' ↦
      Set.disjoint_left.mp (family.piece_pairwise hne) hs.2 hs'.2
  piece_measurable := fun h ↦
    measurableSet_checkerPrefixedPreimage (family.piece_measurable h) e
  piece_union := by
    ext s
    simp only [checkerPrefixedPreimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · rintro ⟨h, hfirst, hh⟩
      exact ⟨hfirst, (Set.ext_iff.mp family.piece_union _).mp
        (Set.mem_iUnion_of_mem h hh)⟩
    · rintro ⟨hfirst, hprevious⟩
      rcases Set.mem_iUnion.mp
          ((Set.ext_iff.mp family.piece_union _).mpr hprevious) with ⟨h, hh⟩
      exact ⟨h, hfirst, hh⟩
  candidate_card := family.candidate_card
  coordinate_ratio := by
    intro h x hx
    have hpieceNear : MeasurableSet
        (family.piece h ∩ family.near h x) :=
      (family.piece_measurable h).inter (near_measurable h x)
    have hset : checkerPrefixedPreimage e (family.piece h) ∩
          checkerPrefixedPreimage e (family.near h x) =
        checkerPrefixedPreimage e
          (family.piece h ∩ family.near h x) := by
      ext s
      simp only [checkerPrefixedPreimage, Set.mem_inter_iff,
        Set.mem_preimage]
      tauto
    rw [hset,
      simpleRandomWalk_checkerPrefixedPreimage e hpieceNear,
      simpleRandomWalk_checkerPrefixedPreimage e
        (family.piece_measurable h)]
    calc
      (1 / 4 : ℝ≥0∞) *
            simpleRandomWalk (family.piece h ∩ family.near h x) ≤
          (1 / 4 : ℝ≥0∞) *
            (ratio * simpleRandomWalk (family.piece h)) := by
        gcongr
        exact family.coordinate_ratio h x hx
      _ = ratio * ((1 / 4 : ℝ≥0∞) *
            simpleRandomWalk (family.piece h)) := by ac_rfl

namespace StoppedHistoryCandidateFamily

theorem someCandidate_checkerFixedPrefixFamily
    {History Candidate : Type*} [Countable History]
    {targetPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (e : Direction)
    (family : StoppedHistoryCandidateFamily History Candidate targetPrevious
      budget ratio)
    (near_measurable : ∀ h x, MeasurableSet (family.near h x)) :
    (checkerFixedPrefixFamily e family near_measurable).someCandidate =
      checkerPrefixedPreimage e family.someCandidate := by
  ext s
  unfold StoppedHistoryCandidateFamily.someCandidate
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨x, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨hx, hs⟩
    refine ⟨hs.1.1, ?_⟩
    exact Set.mem_iUnion_of_mem h <| Set.mem_iUnion_of_mem x <|
      Set.mem_iUnion_of_mem hx ⟨hs.1.2, hs.2.2⟩
  · intro hs
    rcases hs with ⟨hfirst, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨x, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨hx, hs⟩
    exact Set.mem_iUnion_of_mem h <| Set.mem_iUnion_of_mem x <|
      Set.mem_iUnion_of_mem hx ⟨⟨hfirst, hs.1⟩, hfirst, hs.2⟩

end StoppedHistoryCandidateFamily

theorem originSafeTargetFamily_near_measurable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h x, MeasurableSet
      ((originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).near h x) := by
  intro h x
  cases h with
  | none => exact MeasurableSet.empty
  | some eta =>
      exact measurableSet_sourceOriginSafeCandidateNear eta a low e x

/-- The final fixed-direction checker row.  Its previous event is the
literal first-step pullback of the origin-safe target reaching stage. -/
noncomputable def checkerOriginSafeFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point
      (checkerPrefixedPreimage e
        (targetOriginSafe m k e ∩ thresholdReachStage m k))
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  checkerFixedPrefixFamily e
    (originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic)
    (originSafeTargetFamily_near_measurable a low e hm hk hwindow harithmetic
      hwidth hexternalArithmetic)

/-- The final candidate union is exactly the first-step pullback of the
origin-safe target candidate union. -/
theorem checkerOriginSafeFamily_someCandidate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (checkerOriginSafeFamily (t := t) (o := o) a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic).someCandidate =
      checkerPrefixedPreimage e
        (originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
          harithmetic hwidth hexternalArithmetic).someCandidate := by
  exact StoppedHistoryCandidateFamily.someCandidate_checkerFixedPrefixFamily
    e _ (originSafeTargetFamily_near_measurable a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic)

/-- Pull back any target transition covered by the concrete good-origin
criterion into the final checker candidate union. -/
theorem checkerOriginSafeNext_subset_someCandidate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction) (next : Set WalkPath)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnext : ∀ s ∈ next,
      ∃ (eta : SourceSupportedIndex t o m k) (candidate : Point),
        s ∈ historyPiece t o m k (SourceSupportAt t o m)
          (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) ∧
        OriginSafeSourceProp49EligibleHistory e eta ∧
        candidate ∈ eta.1.2 ∧
        s ∈ sourceOriginSafeCandidateNear eta a low e candidate) :
    checkerPrefixedPreimage e next ⊆
      (checkerOriginSafeFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate := by
  rw [checkerOriginSafeFamily_someCandidate]
  intro s hs
  exact ⟨hs.1, originSafeTargetNext_subset_someCandidate a low e next hm hk
    hwindow harithmetic hwidth hexternalArithmetic hnext hs.2⟩

/-- Every valid path in the checker row's previous event is outside the
physical checker-origin exception. -/
theorem checkerOriginSafePrevious_inter_valid_subset_exception_compl
    (d : Tilings.CheckerDirection) (e : Direction)
    {m k w : ℕ} (hm : 1 < m) (hk : 0 < k) :
    checkerPrefixedPreimage e
        (targetOriginSafe m k e ∩ thresholdReachStage m k) ∩
        validStepWalk ⊆
      (checkerOriginShiftExceptionEvent d m k w)ᶜ :=
  checkerPrefixedPreimage_targetOriginSafe_subset_exception_compl d e hm hk

end

end Erdos1165.HLOZCheckerOriginSafeProp49Family
