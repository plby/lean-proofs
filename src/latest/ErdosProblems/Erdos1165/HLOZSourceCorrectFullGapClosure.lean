/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFilteredFullBetaProductBranch
import ErdosProblems.Erdos1165.HLOZCandidateLocalLazyCap
import ErdosProblems.Erdos1165.HLOZAllCreationCofinalConditionalSharpWindow
import ErdosProblems.Erdos1165.HLOZCofinalSharpWindowProductClosure
import ErdosProblems.Erdos1165.HLOZFilteredSourceCorrectBandProductClosure
import ErdosProblems.Erdos1165.HLOZLargeDeficitSpatialScreen
import ErdosProblems.Erdos1165.HLOZShellZeroExternalWindow
import ErdosProblems.Erdos1165.HLOZSharpPositiveShellNumerics
import ErdosProblems.Erdos1165.HLOZSourceCorrectFilteredTransitions
import ErdosProblems.Erdos1165.HLOZThetaSourceBalance
import ErdosProblems.Erdos1165.HLOZValidStoppedLazyClosure

/-!
# Literal eligible-source part of the full-beta gap closure

The shell-zero replacement is valid only on the literal
`D_eta ∩ {Theta_eta = ∅}` source.  This module therefore does not export the
old unconditional candidate theorem.  It constructs the per-band filtered
screen on the exact source event, proves its coefficient tail from literal
stopped-fibre and positive-shell data, and exposes the three rank-stage
preliminary events needed by the transition assembly.

The complementary Proposition 4.5 `Theta` screen is intentionally a
separate layer.  Until that concrete layer is imported, no raw
`HasGapDeficitReturnHarnack` theorem is stated here.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZSourceCorrectFullGapClosure

open HLOZAllSixBandProductClosure HLOZFilteredFullBetaProductBranch
open HLOZCandidateLocalLazyCap
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZCofinalSharpWindowProductClosure
open HLOZFilteredSourceCorrectBandProductClosure HLOZFullBetaRegimeSplit
open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open HLOZQuarterCutCentralTail
open HLOZShellZeroExternalWindow
open HLOZSharpPositiveShellNumerics HLOZSourceCorrectFilteredTransitions
open HLOZThetaSourceBalance
open HLOZTilingGapRandomClockScreen HLOZValidStoppedLazyClosure
open LazyDecomposition
open ScreeningInstantiation TilingShellZeroFactoredCapScreen
open NearFavoriteThresholded
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroLiteralScreen
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-! ## Literal per-band data -/

/-- Literal data for a band, before selecting a stage event.  Selecting a
preliminary event constructs the eligible set as its intersection with the
exact shell-zero source, so there is no `shellZero_good` or candidate-routing
field. -/
structure LiteralSourceBandProductData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixBandProductData t m cutoff band
  sourceOrientation : Orientation
  externalLow : ℕ
  externalHigh : ℕ
  baseFibers : ∀ (n : ℕ),
    ∀ eta : LiteralShellZeroSupportedTraceIndex t sourceOrientation m
      band.oldRank
      (m - shellWidth48 m) externalLow externalHigh
        (sourceCut48 m + 1 + n),
    LiteralShellZeroStoppedCoordinateSpec t sourceOrientation m band.oldRank
      (m - shellWidth48 m) externalLow externalHigh
      (sourceCut48 m + 1 + n) eta.1
  sharp : SharpPositiveShellBounds interfaces

/-- The exact eligible source selected by a preliminary rank stage. -/
def LiteralSourceBandProductData.eligible
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : LiteralSourceBandProductData t m cutoff band)
    (preliminary : Set WalkPath) : Set WalkPath :=
  orientedFilteredShellZeroSourceEvent preliminary t data.sourceOrientation m
    band.oldRank (shellWidth48 m) (m - shellWidth48 m) data.externalLow
      data.externalHigh (sourceCut48 m)

/-- Construct the filtered recurrence package on the exact eligible source.
The source inclusion used at shell zero is discharged by construction. -/
noncomputable def LiteralSourceBandProductData.filtered
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : LiteralSourceBandProductData t m cutoff band)
    (preliminary : Set WalkPath) :
    AllSixFilteredSourceCorrectBandProductData t m cutoff band
      (data.eligible preliminary) :=
  literalSourceFilteredBandProductData preliminary data.interfaces
    data.sourceOrientation (m - shellWidth48 m) data.externalLow
      data.externalHigh data.baseFibers

/-! ## Exact preliminary stages -/

/-- The lazy-good target left by the filtered full-beta endpoint extraction. -/
def endpointCandidatePreliminary (t : DominoTiling) (m cap : ℕ) :
    Set WalkPath :=
  tilingLazyGoodPart t
    (onTimeProductBetaLowGapExceptionalEvent t m ∩
      VariableStoppedTracePartition.validStepWalk) m cap

/-- Rank-one histories after the local low-gap and lazy-cap failures have
been routed away. -/
def firstCandidatePreliminary (cap : ℕ → ℕ) : BranchEvent :=
  fun t m a ↦ firstTransitionEvent t m a \
    (firstLowGapFailureEvent t m a ∪
      rankLazyCapFailureEvent t m (cap m) 1)

/-- Rank-two analogue of `firstCandidatePreliminary`. -/
def secondCandidatePreliminary (cap : ℕ → ℕ) : BranchEvent :=
  fun t m a ↦ secondTransitionEvent t m a \
    (secondLowGapFailureEvent t m a ∪
      rankLazyCapFailureEvent t m (cap m) 2)

/-- Rank-three analogue of `firstCandidatePreliminary`. -/
def thirdCandidatePreliminary (cap : ℕ → ℕ) : BranchEvent :=
  fun t m a ↦ thirdTransitionEvent t m a \
    (thirdLowGapFailureEvent t m a ∪
      rankLazyCapFailureEvent t m (cap m) 3)

/-- The rank-one preliminary stage already carries the exact structural
`D_eta` profile.  Only the `Theta` split remains before applying the
shell-zero source screen. -/
theorem firstCandidatePreliminary_subset_sourceProfileAtCreation
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 0 < m) :
    firstCandidatePreliminary cap t m a ⊆
      thresholdReachStage m 1 ∩
        {s | tilingDEtaAtCreation t m 1 (shellWidth48 m)
          (m - shellWidth48 m) s} :=
  sdiff_subset.trans
    (HLOZThetaSourceBalance.firstTransitionEvent_subset_sourceProfileAtCreation
      t m (shellWidth48 m) (m - shellWidth48 m) a hm rfl)

/-- Rank-two structural source profile. -/
theorem secondCandidatePreliminary_subset_sourceProfileAtCreation
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 0 < m) :
    secondCandidatePreliminary cap t m a ⊆
      thresholdReachStage m 2 ∩
        {s | tilingDEtaAtCreation t m 2 (shellWidth48 m)
          (m - shellWidth48 m) s} :=
  sdiff_subset.trans
    (HLOZThetaSourceBalance.secondTransitionEvent_subset_sourceProfileAtCreation
      t m (shellWidth48 m) (m - shellWidth48 m) a hm rfl)

/-- Rank-three structural source profile. -/
theorem thirdCandidatePreliminary_subset_sourceProfileAtCreation
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 0 < m) :
    thirdCandidatePreliminary cap t m a ⊆
      thresholdReachStage m 3 ∩
        {s | tilingDEtaAtCreation t m 3 (shellWidth48 m)
          (m - shellWidth48 m) s} :=
  sdiff_subset.trans
    (HLOZThetaSourceBalance.thirdTransitionEvent_subset_sourceProfileAtCreation
      t m (shellWidth48 m) (m - shellWidth48 m) a hm rfl)

theorem measurableSet_firstCandidatePreliminary
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (firstCandidatePreliminary cap t m a) :=
  (measurableSet_firstTransitionEvent t m a).diff
    ((measurableSet_firstLowGapFailureEvent t m a).union
      (measurableSet_rankLazyCapFailureEvent t m (cap m) 1))

theorem measurableSet_secondCandidatePreliminary
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (secondCandidatePreliminary cap t m a) :=
  (measurableSet_secondTransitionEvent t m a).diff
    ((measurableSet_secondLowGapFailureEvent t m a).union
      (measurableSet_rankLazyCapFailureEvent t m (cap m) 2))

theorem measurableSet_thirdCandidatePreliminary
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (thirdCandidatePreliminary cap t m a) :=
  (measurableSet_thirdTransitionEvent t m a).diff
    ((measurableSet_thirdLowGapFailureEvent t m a).union
      (measurableSet_rankLazyCapFailureEvent t m (cap m) 3))

/-! ## Full literal eligible-source package -/

/-- Data currently sufficient for the literal eligible-source half of the
full-beta product screen.  No event-probability estimate, coefficient tail,
arbitrary eligible predicate, or pathwise routing premise is stored. -/
structure FullBetaSourceCorrectProductData (t : DominoTiling) where
  cap : ℕ → ℕ
  externalThreshold : ℕ → ℕ
  lazy : AllSixValidStoppedLazyProductData t cap
  bands : ∀ m band,
    LiteralSourceBandProductData t m
      (levelCutoffTime upperTailDelta m) band
  threshold_pos : ∀ᶠ m : ℕ in atTop, 0 < externalThreshold m
  capacity : ∀ᶠ m : ℕ in atTop,
    cap m + externalThreshold m +
      Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤ m + 1
  band_law_start : ∀ᶠ m : ℕ in atTop,
    ∀ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
      (bands m band).interfaces.lawStart ≤ m
  /-- Legacy eligible-source packages may use a noncanonical retained-count
  window.  The final all-tiling package below fixes the canonical window and
  derives this arithmetic internally instead. -/
  external_window : ∀ᶠ m : ℕ in atTop,
    ∀ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
      ShellZeroExternalWindowArithmeticAt m
        (bands m band).externalLow (bands m band).externalHigh

/-! ## Constructible cofinal positive-shell data -/

/-- The creation-clock restriction on which the truncated clock is the
genuine creation time.  Positive-interface product screens are used only on
this event; its complement is paid by `lateLevelSet` in the raw recurrence. -/
def earlyCreationStage (m rank cutoff : ℕ) : Set WalkPath :=
  {s | creationTimeNat m rank s ≤ cutoff}

theorem measurableSet_earlyCreationStage (m rank cutoff : ℕ) :
    MeasurableSet (earlyCreationStage m rank cutoff) := by
  exact measurableSet_le (measurable_creationTimeNat m rank) measurable_const

/-- The sole band-dependent datum retained by the honest positive-interface
screen is a finite bound for each adjacent-shell total.  The active-window
product itself is constructed in `HLOZPositiveInterfaceScreenedEvent` on
the literal screened event; it is not stored here on the larger, generally
unbalanced physical growth event. -/
structure AllSixCofinalConditionalBandProductData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  totalBound : ℕ → ℕ

/- This intermediate all-six recurrence package fixes the common numerical
window `[shellZeroExternalLow48 m, shellZeroExternalHigh48 m)`.  Its positive
interfaces use the cofinal sharp-window law directly: the older all-cap
`AllSixBandProductData` asks for a false cap-zero tail certificate.

The shell-zero source comparison is no longer stored in this record.  The
transport layer constructs the delta-indexed `(external word, static support)`
stopped-coordinate specification directly for every exact source count.  In
particular there is no public full-favorite carrier or guessed replacement
rank. -/
/-- Cofinal all-tiling data for the carrier-independent raw recurrence.  The
Theta-empty shell-zero comparison is constructed internally by the transport
screen; the complementary Theta-bad payment remains a separate layer. -/
structure FullBetaSourceCorrectCofinalAllTilingProductData where
  externalThreshold : ℕ → ℕ
  interfaces : ∀ (t : DominoTiling) (m : ℕ) (band : RandomClockBand),
    AllSixCofinalConditionalBandProductData t m
      (levelCutoffTime upperTailDelta m) band
  threshold_pos : ∀ᶠ m : ℕ in atTop, 0 < externalThreshold m
  capacity : ∀ᶠ m : ℕ in atTop,
    sourceCandidateLazyCap48 m + externalThreshold m +
      Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤ m + 1

/-- Compatibility name for downstream source-transport modules.  It is an
abbreviation to the corrected cofinal package, not the legacy all-cap
record. -/
abbrev FullBetaSourceCorrectAllTilingProductData :=
  FullBetaSourceCorrectCofinalAllTilingProductData

/-- Finite-band eligible-source candidate event for an arbitrary sequence of
preliminary stages. -/
def eligibleSourceCandidateOverflow
    (t : DominoTiling) (data : FullBetaSourceCorrectProductData t)
    (preliminary : ℕ → Set WalkPath) (m : ℕ) : Set WalkPath :=
  tilingFilteredRandomClockCandidateOverflow t m
    (levelCutoffTime upperTailDelta m)
    (sourceProductEndpointBands m (data.cap m) (data.externalThreshold m))
    (fun band ↦ (data.bands m band).eligible (preliminary m))

/-- The source-supported candidate event restricted to the old-favorite rank
actually used by one transition factor. -/
def eligibleSourceCandidateOverflowAtRank
    (t : DominoTiling) (data : FullBetaSourceCorrectProductData t)
    (preliminary : ℕ → Set WalkPath) (rank m : ℕ) : Set WalkPath :=
  tilingFilteredRandomClockCandidateOverflow t m
    (levelCutoffTime upperTailDelta m)
    (sourceProductEndpointBandsAtRank m (data.cap m)
      (data.externalThreshold m) rank)
    (fun band ↦ (data.bands m band).eligible (preliminary m))

theorem eligibleSourceCandidateOverflowAtRank_subset
    (t : DominoTiling) (data : FullBetaSourceCorrectProductData t)
    (preliminary : ℕ → Set WalkPath) (rank m : ℕ) :
    eligibleSourceCandidateOverflowAtRank t data preliminary rank m ⊆
      eligibleSourceCandidateOverflow t data preliminary m := by
  intro s hs
  rcases hs with ⟨band, hband, hs⟩
  exact ⟨band, (Finset.mem_filter.mp hband).1, hs⟩

theorem measurableSet_eligibleSourceCandidateOverflow
    (t : DominoTiling) (data : FullBetaSourceCorrectProductData t)
    (preliminary : ℕ → Set WalkPath) (m : ℕ)
    (hpreliminary : MeasurableSet (preliminary m)) :
    MeasurableSet (eligibleSourceCandidateOverflow t data preliminary m) := by
  classical
  let bands := sourceProductEndpointBands m (data.cap m)
    (data.externalThreshold m)
  let bad : RandomClockBand → Set WalkPath := fun band ↦
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m
        (levelCutoffTime upperTailDelta m) s band).card} ∩
      (data.bands m band).eligible (preliminary m)
  change MeasurableSet (Screening.someCandidateBad bands bad)
  induction bands using Finset.induction_on with
  | empty => simp [Screening.someCandidateBad]
  | @insert band bands hband ih =>
      rw [show Screening.someCandidateBad (insert band bands) bad =
          bad band ∪ Screening.someCandidateBad bands bad by
        ext s
        simp [Screening.someCandidateBad]]
      apply MeasurableSet.union _ ih
      exact (measurableSet_tilingRandomClockBandCardOverflow t m
        (levelCutoffTime upperTailDelta m) band).inter
          (measurableSet_orientedFilteredShellZeroSourceEvent hpreliminary t
            (data.bands m band).sourceOrientation m band.oldRank
            (shellWidth48 m) (m - shellWidth48 m)
            (data.bands m band).externalLow
            (data.bands m band).externalHigh (sourceCut48 m))

theorem measurableSet_eligibleSourceCandidateOverflowAtRank
    (t : DominoTiling) (data : FullBetaSourceCorrectProductData t)
    (preliminary : ℕ → Set WalkPath) (rank m : ℕ)
    (hpreliminary : MeasurableSet (preliminary m)) :
    MeasurableSet
      (eligibleSourceCandidateOverflowAtRank t data preliminary rank m) := by
  classical
  let bands := sourceProductEndpointBandsAtRank m (data.cap m)
    (data.externalThreshold m) rank
  let bad : RandomClockBand → Set WalkPath := fun band ↦
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m
        (levelCutoffTime upperTailDelta m) s band).card} ∩
      (data.bands m band).eligible (preliminary m)
  change MeasurableSet (Screening.someCandidateBad bands bad)
  induction bands using Finset.induction_on with
  | empty => simp [Screening.someCandidateBad]
  | @insert band bands hband ih =>
      rw [show Screening.someCandidateBad (insert band bands) bad =
          bad band ∪ Screening.someCandidateBad bands bad by
        ext s
        simp [Screening.someCandidateBad]]
      apply MeasurableSet.union _ ih
      exact (measurableSet_tilingRandomClockBandCardOverflow t m
        (levelCutoffTime upperTailDelta m) band).inter
          (measurableSet_orientedFilteredShellZeroSourceEvent hpreliminary t
            (data.bands m band).sourceOrientation m band.oldRank
            (shellWidth48 m) (m - shellWidth48 m)
            (data.bands m band).externalLow
            (data.bands m band).externalHigh (sourceCut48 m))

/-- The eligible-source candidate has an internally derived
logarithmic-square envelope.  This theorem does not include the complementary
`Theta` event. -/
theorem eventually_simpleRandomWalk_eligibleSourceCandidateOverflow_le_exp
    (t : DominoTiling) (data : FullBetaSourceCorrectProductData t)
    (preliminary : ℕ → Set WalkPath) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (eligibleSourceCandidateOverflow t data preliminary m) ≤
        ENNReal.ofReal (Real.exp
          (-(2 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2)) := by
  have hcandidate :=
    eventually_simpleRandomWalk_tilingFilteredRandomClockCandidateOverflow_le_sum
      t (fun m ↦ levelCutoffTime upperTailDelta m)
      (fun m ↦ sourceProductEndpointBands m (data.cap m)
        (data.externalThreshold m))
      (fun m band ↦ (data.bands m band).eligible (preliminary m))
      (fun m band hband ↦ sourceProductEndpointBand_betaLower hband)
      (fun m band ↦ (data.bands m band).filtered (preliminary m))
      data.band_law_start data.external_window
  have hcoefficient :=
    eventually_sum_totalFilteredSourceCorrectBandOverflowCoefficient_le_exp
      t data.cap data.externalThreshold
      (fun m band ↦ (data.bands m band).eligible (preliminary m))
      (fun m band ↦ (data.bands m band).filtered (preliminary m))
      data.band_law_start (fun m band ↦ (data.bands m band).sharp)
  filter_upwards [hcandidate, hcoefficient] with m hcandidateM hcoefficientM
  exact hcandidateM.trans hcoefficientM

/-! ## Canonical eligible staged candidates -/

/-- Rank-one eligible candidate supplied to the filtered transition layer.
The concrete Proposition 4.5 layer must add the complementary `Theta` event
before this becomes a complete rank-one candidate filter. -/
def firstEligibleStagedCandidate
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t) :
    BranchEvent := fun t m a ↦
  eligibleSourceCandidateOverflowAtRank t (data t)
    (fun m ↦ firstCandidatePreliminary (data t).cap t m a) 1 m

/-- Rank-two eligible candidate. -/
def secondEligibleStagedCandidate
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t) :
    BranchEvent := fun t m a ↦
  eligibleSourceCandidateOverflowAtRank t (data t)
    (fun m ↦ secondCandidatePreliminary (data t).cap t m a) 2 m

/-- Rank-three eligible candidate. -/
def thirdEligibleStagedCandidate
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t) :
    BranchEvent := fun t m a ↦
  eligibleSourceCandidateOverflowAtRank t (data t)
    (fun m ↦ thirdCandidatePreliminary (data t).cap t m a) 3 m

theorem eventually_simpleRandomWalk_firstEligibleStagedCandidate_le_exp
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (a : GapTriple) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (firstEligibleStagedCandidate data t m a) ≤
        ENNReal.ofReal (Real.exp
          (-(2 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2)) :=
  by
    have hfull := eventually_simpleRandomWalk_eligibleSourceCandidateOverflow_le_exp
      t (data t) (fun m ↦ firstCandidatePreliminary (data t).cap t m a)
    filter_upwards [hfull] with m hfullM
    exact (measure_mono (eligibleSourceCandidateOverflowAtRank_subset t
      (data t) (fun m ↦ firstCandidatePreliminary (data t).cap t m a) 1 m)).trans
        hfullM

theorem eventually_simpleRandomWalk_secondEligibleStagedCandidate_le_exp
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (a : GapTriple) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (secondEligibleStagedCandidate data t m a) ≤
        ENNReal.ofReal (Real.exp
          (-(2 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2)) :=
  by
    have hfull := eventually_simpleRandomWalk_eligibleSourceCandidateOverflow_le_exp
      t (data t) (fun m ↦ secondCandidatePreliminary (data t).cap t m a)
    filter_upwards [hfull] with m hfullM
    exact (measure_mono (eligibleSourceCandidateOverflowAtRank_subset t
      (data t) (fun m ↦ secondCandidatePreliminary (data t).cap t m a) 2 m)).trans
        hfullM

theorem eventually_simpleRandomWalk_thirdEligibleStagedCandidate_le_exp
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (a : GapTriple) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (thirdEligibleStagedCandidate data t m a) ≤
        ENNReal.ofReal (Real.exp
          (-(2 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2)) :=
  by
    have hfull := eventually_simpleRandomWalk_eligibleSourceCandidateOverflow_le_exp
      t (data t) (fun m ↦ thirdCandidatePreliminary (data t).cap t m a)
    filter_upwards [hfull] with m hfullM
    exact (measure_mono (eligibleSourceCandidateOverflowAtRank_subset t
      (data t) (fun m ↦ thirdCandidatePreliminary (data t).cap t m a) 3 m)).trans
        hfullM

theorem measurableSet_firstEligibleStagedCandidate
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (firstEligibleStagedCandidate data t m a) :=
  measurableSet_eligibleSourceCandidateOverflowAtRank t (data t)
    (fun m ↦ firstCandidatePreliminary (data t).cap t m a) 1 m
    (measurableSet_firstCandidatePreliminary (data t).cap t m a)

theorem measurableSet_secondEligibleStagedCandidate
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (secondEligibleStagedCandidate data t m a) :=
  measurableSet_eligibleSourceCandidateOverflowAtRank t (data t)
    (fun m ↦ secondCandidatePreliminary (data t).cap t m a) 2 m
    (measurableSet_secondCandidatePreliminary (data t).cap t m a)

theorem measurableSet_thirdEligibleStagedCandidate
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (thirdEligibleStagedCandidate data t m a) :=
  measurableSet_eligibleSourceCandidateOverflowAtRank t (data t)
    (fun m ↦ thirdCandidatePreliminary (data t).cap t m a) 3 m
    (measurableSet_thirdCandidatePreliminary (data t).cap t m a)

theorem simpleRandomWalk_firstEligibleStagedCandidate_series_ne_top
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (a : GapTriple) :
    ∑' m, simpleRandomWalk (firstEligibleStagedCandidate data t m a) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (firstEligibleStagedCandidate data t · a)
    (by positivity [fullBetaSourceCorrectRate_pos])
    (eventually_simpleRandomWalk_firstEligibleStagedCandidate_le_exp data t a)

theorem simpleRandomWalk_secondEligibleStagedCandidate_series_ne_top
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (a : GapTriple) :
    ∑' m, simpleRandomWalk (secondEligibleStagedCandidate data t m a) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (secondEligibleStagedCandidate data t · a)
    (by positivity [fullBetaSourceCorrectRate_pos])
    (eventually_simpleRandomWalk_secondEligibleStagedCandidate_le_exp data t a)

theorem simpleRandomWalk_thirdEligibleStagedCandidate_series_ne_top
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t)
    (t : DominoTiling) (a : GapTriple) :
    ∑' m, simpleRandomWalk (thirdEligibleStagedCandidate data t m a) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (thirdEligibleStagedCandidate data t · a)
    (by positivity [fullBetaSourceCorrectRate_pos])
    (eventually_simpleRandomWalk_thirdEligibleStagedCandidate_le_exp data t a)

end

end Erdos1165.HLOZSourceCorrectFullGapClosure
