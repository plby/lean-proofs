/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerOriginShiftPayment
import ErdosProblems.Erdos1165.HLOZAllTilingSourceTransportScreen
import ErdosProblems.Erdos1165.HLOZNoLazyFullBetaProductBranch
import ErdosProblems.Erdos1165.HLOZNoLazyCandidateRankSplit
import ErdosProblems.Erdos1165.HLOZNoLazyFilteredPastObservability
import ErdosProblems.Erdos1165.HLOZPositiveInterfaceScreenedEvent
import ErdosProblems.Erdos1165.HLOZDominantPositiveInterfaceBandRecurrence
import ErdosProblems.Erdos1165.HLOZRawShellCreationBridge
import ErdosProblems.Erdos1165.HLOZSourceCorrectFullGapClosure

/-!
# Raw full-gap product promotion

This follow-up module contains the pieces used to promote the literal source
screen to the raw staged candidate events.  The eligible-source core remains
frozen in `HLOZSourceCorrectFullGapClosure`.

The first piece below is independent of source identification: the concrete
active-window part of every positive-shell interface failure is bounded by
the stopped product, while its exact unscreened balance/reconstruction
remainder is exposed separately.  The shell-zero canonical/opposite routing and its
`Theta`/checker-origin complements are added only through their literal
source theorems; no unconditional shell-zero claim is made here.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZRawFullGapProductPromotion

open HLOZAllSixBandProductClosure
open HLOZAllTilingSourceTransportScreen
open HLOZCandidateLocalLazyCap
open HLOZNoLazyFullBetaProductBranch
open HLOZNoLazyCandidateRankSplit
open HLOZCheckerOriginShiftPayment
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZDynamicThresholdedScreening HLOZFullBetaRegimeSplit
open HLOZNoLazyFilteredPastObservability
open HLOZDominantPositiveInterfaceBandRecurrence
open HLOZGapBetaNumerics HLOZGapRandomClockScreen HLOZProposition48Candidates
open HLOZGapPointReturn HLOZPathEvents HLOZSharpProductNumerics
open HLOZOrientedSourceCentralTail HLOZRawShellCreationBridge
open HLOZPositiveInterfaceScreenedEvent
open HLOZShellZeroRankUnionCentralTail
open HLOZShellZeroReplacementWindows
open HLOZSharpPositiveShellNumerics HLOZSourceCorrectFilteredTransitions
open HLOZSourceCorrectFullGapClosure HLOZThresholdedShellScreening
open HLOZThetaSourceBalance
open HLOZTilingGapBandExtraction
open HLOZTilingEndpointBandExtraction HLOZTilingGapRandomClockScreen
open HLOZSpatialAdapter HLOZUpperEstimates
open NearFavoriteShells NearFavoriteThresholded
open ScreeningInstantiation
open TilingOrientedShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-! ## The literal raw staged candidates -/

/-- Rank-one transition histories after paying only the local low-gap
failure.  No global or away-lazy event is removed: the sole candidate-local
cap used by extraction is recovered later from the oriented source window. -/
def firstRawCandidatePreliminary : BranchEvent :=
  fun t m a ↦ firstTransitionEvent t m a \
    firstLowGapFailureEvent t m a

/-- Rank-two raw preliminary stage. -/
def secondRawCandidatePreliminary : BranchEvent :=
  fun t m a ↦ secondTransitionEvent t m a \
    secondLowGapFailureEvent t m a

/-- Rank-three raw preliminary stage. -/
def thirdRawCandidatePreliminary : BranchEvent :=
  fun t m a ↦ thirdTransitionEvent t m a \
    thirdLowGapFailureEvent t m a

theorem measurableSet_firstRawCandidatePreliminary
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (firstRawCandidatePreliminary t m a) :=
  (measurableSet_firstTransitionEvent t m a).diff
    (measurableSet_firstLowGapFailureEvent t m a)

theorem measurableSet_secondRawCandidatePreliminary
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (secondRawCandidatePreliminary t m a) :=
  (measurableSet_secondTransitionEvent t m a).diff
    (measurableSet_secondLowGapFailureEvent t m a)

theorem measurableSet_thirdRawCandidatePreliminary
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (thirdRawCandidatePreliminary t m a) :=
  (measurableSet_thirdTransitionEvent t m a).diff
    (measurableSet_thirdLowGapFailureEvent t m a)

/-- Removing the low-gap filter preserves the exact rank-one structural
source profile supplied by the transition stage. -/
theorem firstRawCandidatePreliminary_subset_sourceProfileAtCreation
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 0 < m) :
    firstRawCandidatePreliminary t m a ⊆
      thresholdReachStage m 1 ∩
        {s | tilingDEtaAtCreation t m 1 (shellWidth48 m)
          (m - shellWidth48 m) s} :=
  sdiff_subset.trans
    (HLOZThetaSourceBalance.firstTransitionEvent_subset_sourceProfileAtCreation
      t m (shellWidth48 m) (m - shellWidth48 m) a hm rfl)

/-- Rank-two structural source profile for the raw preliminary. -/
theorem secondRawCandidatePreliminary_subset_sourceProfileAtCreation
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 0 < m) :
    secondRawCandidatePreliminary t m a ⊆
      thresholdReachStage m 2 ∩
        {s | tilingDEtaAtCreation t m 2 (shellWidth48 m)
          (m - shellWidth48 m) s} :=
  sdiff_subset.trans
    (HLOZThetaSourceBalance.secondTransitionEvent_subset_sourceProfileAtCreation
      t m (shellWidth48 m) (m - shellWidth48 m) a hm rfl)

/-- Rank-three structural source profile for the raw preliminary. -/
theorem thirdRawCandidatePreliminary_subset_sourceProfileAtCreation
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 0 < m) :
    thirdRawCandidatePreliminary t m a ⊆
      thresholdReachStage m 3 ∩
        {s | tilingDEtaAtCreation t m 3 (shellWidth48 m)
          (m - shellWidth48 m) s} :=
  sdiff_subset.trans
    (HLOZThetaSourceBalance.thirdTransitionEvent_subset_sourceProfileAtCreation
      t m (shellWidth48 m) (m - shellWidth48 m) a hm rfl)

/-- A rank-one raw preliminary supplies the exact creation profile needed to
identify a stopped first shell with its creation-time spatial source. -/
theorem firstRawCandidatePreliminary_creationProfile
    {t : DominoTiling} {m : ℕ} {a : GapTriple} {s : WalkPath}
    (hs : s ∈ firstRawCandidatePreliminary t m a) :
    ∃ n, ThresholdCreation s m 1 n ∧
      thresholdCount s n (m + 1) = 0 := by
  rcases hs with ⟨hstage, _⟩
  simp only [firstTransitionEvent, Set.mem_iUnion] at hstage
  rcases hstage with ⟨n₁, n₂, h₁, h₂, hnext, _⟩
  refine ⟨n₁, h₁, ?_⟩
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  change thresholdCount s n₁ (m + 1) ≤
    thresholdCount s n₂ (m + 1) at hmono
  omega

/-- Rank-two creation profile. -/
theorem secondRawCandidatePreliminary_creationProfile
    {t : DominoTiling} {m : ℕ} {a : GapTriple} {s : WalkPath}
    (hs : s ∈ secondRawCandidatePreliminary t m a) :
    ∃ n, ThresholdCreation s m 2 n ∧
      thresholdCount s n (m + 1) = 0 := by
  rcases hs with ⟨hstage, _⟩
  simp only [secondTransitionEvent, Set.mem_iUnion] at hstage
  rcases hstage with ⟨n₁, n₂, n₃, _h₁, h₂, h₃, hnext, _⟩
  refine ⟨n₂, h₂, ?_⟩
  have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  change thresholdCount s n₂ (m + 1) ≤
    thresholdCount s n₃ (m + 1) at hmono
  omega

/-- Rank-three creation profile. -/
theorem thirdRawCandidatePreliminary_creationProfile
    {t : DominoTiling} {m : ℕ} {a : GapTriple} {s : WalkPath}
    (hs : s ∈ thirdRawCandidatePreliminary t m a) :
    ∃ n, ThresholdCreation s m 3 n ∧
      thresholdCount s n (m + 1) = 0 := by
  rcases hs with ⟨hstage, _⟩
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hstage
  rcases hstage with ⟨n₁, n₂, n₃, n₄, _h₁, _h₂, h₃, h₄, hnext, _⟩
  refine ⟨n₃, h₃, ?_⟩
  have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  change thresholdCount s n₃ (m + 1) ≤
    thresholdCount s n₄ (m + 1) at hmono
  omega

/-- The rank-one candidate history removed from the first transition.

This is the actual raw random-clock overflow on the rank-one preliminary
stage.  Source, interface, `Theta`, and transport events occur only in its
internal probability decomposition; they are not substituted for the raw
history seen by the transition factor. -/
def firstRawStagedCandidate
    (data : FullBetaSourceCorrectAllTilingProductData) : BranchEvent :=
  fun t m a ↦
    firstRawCandidatePreliminary t m a ∩
      rankCandidateOverflowEvent t m (levelCutoffTime upperTailDelta m)
        (sourceCandidateLazyCap48 m) (data.externalThreshold m) 1

/-- Rank-two raw random-clock candidate history. -/
def secondRawStagedCandidate
    (data : FullBetaSourceCorrectAllTilingProductData) : BranchEvent :=
  fun t m a ↦
    secondRawCandidatePreliminary t m a ∩
      rankCandidateOverflowEvent t m (levelCutoffTime upperTailDelta m)
        (sourceCandidateLazyCap48 m) (data.externalThreshold m) 2

/-- Rank-three raw random-clock candidate history. -/
def thirdRawStagedCandidate
    (data : FullBetaSourceCorrectAllTilingProductData) : BranchEvent :=
  fun t m a ↦
    thirdRawCandidatePreliminary t m a ∩
      rankCandidateOverflowEvent t m (levelCutoffTime upperTailDelta m)
        (sourceCandidateLazyCap48 m) (data.externalThreshold m) 3

theorem measurableSet_firstRawStagedCandidate
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (firstRawStagedCandidate data t m a) :=
  (measurableSet_firstRawCandidatePreliminary t m a).inter
    (measurableSet_rankCandidateOverflowEvent t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) 1)

theorem measurableSet_secondRawStagedCandidate
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (secondRawStagedCandidate data t m a) :=
  (measurableSet_secondRawCandidatePreliminary t m a).inter
    (measurableSet_rankCandidateOverflowEvent t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) 2)

theorem measurableSet_thirdRawStagedCandidate
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (thirdRawStagedCandidate data t m a) :=
  (measurableSet_thirdRawCandidatePreliminary t m a).inter
    (measurableSet_rankCandidateOverflowEvent t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) 3)

/-! ## Fixed-creation observability of the raw overflow -/

theorem pathTruncatedLevelTime_eq_min_of_creation
    {s : WalkPath} {m rank n cutoff : ℕ}
    (hcreation : ThresholdCreation s m rank n) :
    pathTruncatedLevelTime m rank cutoff s = min n cutoff := by
  classical
  let hreach : ReachesThreshold s m rank := ⟨n, hcreation.1⟩
  have hfind : Nat.find hreach = n :=
    HLOZSpatialAdapter.thresholdCreation_time_unique
      (thresholdCreation_natFind hreach) hcreation
  unfold pathTruncatedLevelTime
  rw [dif_pos hreach, hfind]

/-- On paths with the same fixed rank-creation prefix, every raw band set
at that rank is identical.  The stopped clock is `min creation cutoff`, so
no assumption comparing the cutoff with the creation time is needed. -/
theorem tilingRandomClockBandSites_eq_of_pathPrefix_eq_of_creation
    {t : DominoTiling} {m rank n cutoff N : ℕ}
    {s s' : WalkPath} {band : RandomClockBand}
    (hrank : band.oldRank = rank)
    (hcreation : ThresholdCreation s m rank n)
    (hcreation' : ThresholdCreation s' m rank n)
    (hn : n ≤ N) (hp : pathPrefix s N = pathPrefix s' N) :
    tilingRandomClockBandSites t m cutoff s band =
      tilingRandomClockBandSites t m cutoff s' band := by
  have hclock : pathTruncatedLevelTime m band.oldRank cutoff s =
      min n cutoff := by
    rw [hrank]
    exact pathTruncatedLevelTime_eq_min_of_creation hcreation
  have hclock' : pathTruncatedLevelTime m band.oldRank cutoff s' =
      min n cutoff := by
    rw [hrank]
    exact pathTruncatedLevelTime_eq_min_of_creation hcreation'
  rw [tilingRandomClockBandSites_eq_prefix_of_clock hclock,
    tilingRandomClockBandSites_eq_prefix_of_clock hclock']
  rw [pathPrefix_eq_of_pathPrefix_eq_of_le hp
    ((Nat.min_le_left n cutoff).trans hn)]

/-- Candidate overflow in all bands with a fixed old rank is invariant on a
fixed creation prefix at that rank. -/
theorem rankCandidateOverflowEvent_iff_of_pathPrefix_eq_of_creation
    {t : DominoTiling} {m rank n cutoff cap externalThreshold N : ℕ}
    {s s' : WalkPath}
    (hcreation : ThresholdCreation s m rank n)
    (hcreation' : ThresholdCreation s' m rank n)
    (hn : n ≤ N) (hp : pathPrefix s N = pathPrefix s' N) :
    s ∈ rankCandidateOverflowEvent t m cutoff cap externalThreshold rank ↔
      s' ∈ rankCandidateOverflowEvent t m cutoff cap externalThreshold rank := by
  unfold rankCandidateOverflowEvent tilingRandomClockCandidateOverflow
    HLOZGapEstimate.candidateOverflow
  constructor
  · rintro ⟨band, hband, hoverflow⟩
    refine ⟨band, hband, ?_⟩
    have hrank : band.oldRank = rank := (Finset.mem_filter.mp hband).2
    rw [← tilingRandomClockBandSites_eq_of_pathPrefix_eq_of_creation
      hrank hcreation hcreation' hn hp]
    exact hoverflow
  · rintro ⟨band, hband, hoverflow⟩
    refine ⟨band, hband, ?_⟩
    have hrank : band.oldRank = rank := (Finset.mem_filter.mp hband).2
    rw [tilingRandomClockBandSites_eq_of_pathPrefix_eq_of_creation
      hrank hcreation hcreation' hn hp]
    exact hoverflow

/-- Rank-one overflow is observable on every fixed pair-creation atom. -/
theorem pairCreationAtom_inter_rankOneCandidateOverflow_observable
    (t : DominoTiling) (m cutoff cap externalThreshold : ℕ)
    (a : GapTriple) (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        rankCandidateOverflowEvent t m cutoff cap externalThreshold 1)) := by
  apply pairCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hn : z.1 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1).le
  exact rankCandidateOverflowEvent_iff_of_pathPrefix_eq_of_creation
    hs.1 hs'.1 hn hp

/-- Rank-one overflow is also observable on a fixed triple-creation atom. -/
theorem tripleCreationAtom_inter_rankOneCandidateOverflow_observable
    (t : DominoTiling) (m cutoff cap externalThreshold : ℕ)
    (a : GapTriple) (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        rankCandidateOverflowEvent t m cutoff cap externalThreshold 1)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have h12 : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1
  have h23 : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1
  exact rankCandidateOverflowEvent_iff_of_pathPrefix_eq_of_creation
    hs.1 hs'.1 (h12.trans h23).le hp

/-- Rank-two overflow is observable on every fixed triple-creation atom. -/
theorem tripleCreationAtom_inter_rankTwoCandidateOverflow_observable
    (t : DominoTiling) (m cutoff cap externalThreshold : ℕ)
    (a : GapTriple) (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        rankCandidateOverflowEvent t m cutoff cap externalThreshold 2)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hn : z.1.2 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1).le
  exact rankCandidateOverflowEvent_iff_of_pathPrefix_eq_of_creation
    hs.2.1 hs'.2.1 hn hp

private theorem isMeasurableAtStopping_diff_const
    (n : ℕ) {A B : Set StepPath}
    (hA : IsMeasurableAtStopping (fun _ : StepPath ↦ n) A)
    (hB : IsMeasurableAtStopping (fun _ : StepPath ↦ n) B) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n) (A \ B) := by
  rw [show A \ B = A ∩ Bᶜ by ext omega; simp]
  exact isMeasurableAtStopping_inter hA
    (isMeasurableAtStopping_compl (isFiniteStoppingTime_const n) hB)

private theorem pairCreationAtom_inter_firstLowGapFailure_observable
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstLowGapFailureEvent t m a)) := by
  apply pairCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz : z.1 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1).le
  exact (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hs).trans
    ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz le_rfl).trans
      (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hs').symm)

private theorem tripleCreationAtom_inter_firstLowGapFailure_observable
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstLowGapFailureEvent t m a)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz₁₂ : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1
  have hz₂₃ : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1
  exact (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hs).trans
    ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp
      (hz₁₂.trans hz₂₃).le hz₂₃.le).trans
        (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hs').symm)

private theorem tripleCreationAtom_inter_secondLowGapFailure_observable
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondLowGapFailureEvent t m a)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz : z.1.2 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1).le
  exact (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hs).trans
    ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz le_rfl).trans
      (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hs').symm)

/-- Exact first hpast seam required by the heterogeneous upper factor. -/
theorem pairCreationAtom_inter_firstRawStagedCandidate_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstRawStagedCandidate data t m a)) := by
  let structural := firstLowGapFailureEvent t m a
  let candidate := rankCandidateOverflowEvent t m
    (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
    (data.externalThreshold m) 1
  have heq : pairCreationAtom t m a z ∩
      firstRawStagedCandidate data t m a =
      (pairCreationAtom t m a z ∩ candidate) \
        (pairCreationAtom t m a z ∩ structural) := by
    ext s
    constructor
    · rintro ⟨hpair, ⟨hpreliminary, hcand⟩⟩
      exact ⟨⟨hpair, hcand⟩, fun hbad ↦ hpreliminary.2 hbad.2⟩
    · rintro ⟨⟨hpair, hcand⟩, hnotbad⟩
      have hstage : s ∈ firstTransitionEvent t m a :=
        Set.mem_iUnion.mpr ⟨z.1,
          Set.mem_iUnion.mpr ⟨z.2, hpair⟩⟩
      refine ⟨hpair, ⟨⟨hstage, ?_⟩, hcand⟩⟩
      exact fun hbad ↦ hnotbad ⟨hpair, hbad⟩
  rw [heq, preimage_sdiff]
  exact isMeasurableAtStopping_diff_const z.2
    (pairCreationAtom_inter_rankOneCandidateOverflow_observable t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) a z)
    (pairCreationAtom_inter_firstLowGapFailure_observable t m a z)

/-- Rank-one raw staged candidate on a fixed triple atom. -/
theorem tripleCreationAtom_inter_firstRawStagedCandidate_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstRawStagedCandidate data t m a)) := by
  let structural := firstLowGapFailureEvent t m a
  let candidate := rankCandidateOverflowEvent t m
    (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
    (data.externalThreshold m) 1
  have heq : tripleCreationAtom t m a z ∩
      firstRawStagedCandidate data t m a =
      (tripleCreationAtom t m a z ∩ candidate) \
        (tripleCreationAtom t m a z ∩ structural) := by
    ext s
    constructor
    · rintro ⟨htriple, ⟨hpreliminary, hcand⟩⟩
      exact ⟨⟨htriple, hcand⟩, fun hbad ↦ hpreliminary.2 hbad.2⟩
    · rintro ⟨⟨htriple, hcand⟩, hnotbad⟩
      have hpair := tripleCreationAtom_mem_pairConfiguration htriple
      have hstage : s ∈ firstTransitionEvent t m a :=
        Set.mem_iUnion.mpr ⟨z.1.1,
          Set.mem_iUnion.mpr ⟨z.1.2, hpair⟩⟩
      refine ⟨htriple, ⟨⟨hstage, ?_⟩, hcand⟩⟩
      exact fun hbad ↦ hnotbad ⟨htriple, hbad⟩
  rw [heq, preimage_sdiff]
  exact isMeasurableAtStopping_diff_const z.2
    (tripleCreationAtom_inter_rankOneCandidateOverflow_observable t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) a z)
    (tripleCreationAtom_inter_firstLowGapFailure_observable t m a z)

/-- Rank-two raw staged candidate on a fixed triple atom. -/
theorem tripleCreationAtom_inter_secondRawStagedCandidate_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondRawStagedCandidate data t m a)) := by
  let structural := secondLowGapFailureEvent t m a
  let candidate := rankCandidateOverflowEvent t m
    (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
    (data.externalThreshold m) 2
  have heq : tripleCreationAtom t m a z ∩
      secondRawStagedCandidate data t m a =
      (tripleCreationAtom t m a z ∩ candidate) \
        (tripleCreationAtom t m a z ∩ structural) := by
    ext s
    constructor
    · rintro ⟨htriple, ⟨hpreliminary, hcand⟩⟩
      exact ⟨⟨htriple, hcand⟩, fun hbad ↦ hpreliminary.2 hbad.2⟩
    · rintro ⟨⟨htriple, hcand⟩, hnotbad⟩
      have hstage : s ∈ secondTransitionEvent t m a :=
        Set.mem_iUnion.mpr ⟨z.1.1, Set.mem_iUnion.mpr ⟨z.1.2,
          Set.mem_iUnion.mpr ⟨z.2, htriple⟩⟩⟩
      refine ⟨htriple, ⟨⟨hstage, ?_⟩, hcand⟩⟩
      exact fun hbad ↦ hnotbad ⟨htriple, hbad⟩
  rw [heq, preimage_sdiff]
  exact isMeasurableAtStopping_diff_const z.2
    (tripleCreationAtom_inter_rankTwoCandidateOverflow_observable t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) a z)
    (tripleCreationAtom_inter_secondLowGapFailure_observable t m a z)
/-! ## The deterministic shell recurrence split -/

/-- The literal first-shell overflow in one random-clock band. -/
def bandInitialShellOverflowEvent
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  shellOverflow
      (normalizedDominantBandOccupancy t .even m
        (levelCutoffTime upperTailDelta m) band)
      (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48) 0 ∪
    shellOverflow
      (normalizedDominantBandOccupancy t .shifted m
        (levelCutoffTime upperTailDelta m) band)
      (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48) 0

/-- The four orientation-refined creation-source overflows furnished by the
exact raw-to-base pigeonhole.  This intermediate event is used only for a
deterministic subset proof; its members are subsequently routed to literal
source or restricted-Theta payments. -/
def orientedCreationSourceOverflowEvent
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  {s | orientedSourceCut48 m <
      (orientedCanonicalDominantNearBasesAtCreation t .even m
        band.oldRank (shellWidth48 m) s).card} ∪
    {s | orientedSourceCut48 m <
      (orientedCanonicalDominantNearBasesAtCreation t .shifted m
        band.oldRank (shellWidth48 m) s).card} ∪
    {s | orientedSourceCut48 m <
      (orientedOppositeDominantNearEndpointsAtCreation t .even m
        band.oldRank (shellWidth48 m) s).card} ∪
    {s | orientedSourceCut48 m <
      (orientedOppositeDominantNearEndpointsAtCreation t .shifted m
        band.oldRank (shellWidth48 m) s).card}

/-- Finite union of the four-way creation-source overflows over all endpoint
bands with the displayed old-favorite rank. -/
def orientedCreationSourceOverflowUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (orientedCreationSourceOverflowEvent t m)

/-- The arithmetic under which the concrete positive-interface active-window
screen is available.  Outside this range the screened event is empty and the
physical growth event is retained in the named remainder below. -/
def PositiveInterfaceScreenArithmeticAt
    (m : ℕ) (band : RandomClockBand) : Prop :=
  1 < m ∧
    HLOZSharpWindowProductClosure.SharpWindowArithmeticAt m ∧
      m / 2 ≤ band.externalThreshold

/-- The part of the positive-shell payment which is literally represented by
the frozen active-window stopped product.  The orientation is the actual band
orientation, rather than an independently selectable datum. -/
noncomputable def bandPositiveInterfaceScreenedEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  if h : PositiveInterfaceScreenArithmeticAt m band then
    ⋃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
      earlyCreationStage m band.oldRank
          (levelCutoffTime upperTailDelta m) ∩
        positiveInterfaceScreenedEvent t band.orientation m band.oldRank
          band.externalThreshold h.1 band.oldRank_pos
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shell ((data.interfaces t m band).totalBound shell)
  else ∅

/-- One selected endpoint-orientation of the normalized positive-shell
recurrence. -/
def orientedBandPositiveInterfaceFailureEvent
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  ⋃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
      ((thresholdReachStage m band.oldRank ∩ validStepWalk) ∩
          earlyCreationStage m band.oldRank
            (levelCutoffTime upperTailDelta m)) ∩
        thresholdedInterfaceBad (fun _ ↦ Set.univ)
          (normalizedDominantBandOccupancy t o m
            (levelCutoffTime upperTailDelta m) band)
          (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
            shellGrowth48)
          shellGrowth48 shell

/-- The globally valid early-creation positive-shell part of one band
recurrence, after the two-way dominant endpoint orientation split. -/
def bandPositiveInterfaceFailureEvent
    (_data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  ⋃ o : LazyDecomposition.Orientation,
    orientedBandPositiveInterfaceFailureEvent t o m band

/-- The exact early physical adjacent-shell growth which is not covered by
the honest active-window stopped product.  This is the remaining
positive-interface balance/reconstruction payment; no probability estimate
for it is asserted in this module. -/
def bandPositiveInterfaceBalanceRemainderEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  bandPositiveInterfaceFailureEvent data t m band \
    bandPositiveInterfaceScreenedEvent data t m band

theorem bandPositiveInterfaceFailureEvent_subset_screened_union_remainder
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) :
    bandPositiveInterfaceFailureEvent data t m band ⊆
      bandPositiveInterfaceScreenedEvent data t m band ∪
        bandPositiveInterfaceBalanceRemainderEvent data t m band := by
  intro s hs
  by_cases hscreen : s ∈ bandPositiveInterfaceScreenedEvent data t m band
  · exact Or.inl hscreen
  · exact Or.inr ⟨hs, hscreen⟩

theorem bandPositiveInterfaceFailureEvent_subset_earlyCreationStage
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) :
    bandPositiveInterfaceFailureEvent data t m band ⊆
      earlyCreationStage m band.oldRank
        (levelCutoffTime upperTailDelta m) := by
  rintro s hs
  rcases Set.mem_iUnion.mp hs with ⟨_o, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨shell, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨_hshell, hs⟩
  exact hs.1.2

/-- A raw band-cardinality overflow is routed pathwise either to its first
shell or to a positive-shell interface failure.  This is the recurrence
split only; no source identification is used here. -/
theorem bandCardOverflow_subset_initialShell_or_positiveInterface
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) {s : WalkPath}
    {n : ℕ}
    (hm : 1 < m)
    (hbudget : geometricCandidateBudget48 m band.beta ≤
      candidateBudget48 m band.beta)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hclock : n ≤ levelCutoffTime upperTailDelta m)
    (hvalid : s ∈ validStepWalk)
    (hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 *
          geometricShellThreshold (normalizedPositiveInitialBudget48 m)
            shellGrowth48 j ≤
        geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48 (j + 1))
    (hs : candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m
        (levelCutoffTime upperTailDelta m) s band).card) :
    s ∈ bandInitialShellOverflowEvent t m band ∪
      bandPositiveInterfaceFailureEvent data t m band := by
  have hn : 0 < n := by
    have hcreation' : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank n := by
      rw [show trajectory (stepsOfWalk s) = s from hvalid]
      exact hcreation
    exact HLOZThetaOneSourceShift.thresholdCreation_time_pos_of_two_le
      (stepsOfWalk s) hm band.oldRank_pos hcreation'
  have hclockEq : pathTruncatedLevelTime m band.oldRank
      (levelCutoffTime upperTailDelta m) s = n :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff hcreation hclock
  have hfavorite : thresholdSites s n m = favoriteSites s n :=
    thresholdSites_eq_favoriteSites_at_creation_of_terminal
      band.oldRank_pos hcreation le_rfl hnext
  have hstage : s ∈ thresholdReachStage m band.oldRank ∩ validStepWalk :=
    ⟨⟨n, hcreation.1⟩, hvalid⟩
  have hearly : s ∈ earlyCreationStage m band.oldRank
      (levelCutoffTime upperTailDelta m) := by
    rw [earlyCreationStage, Set.mem_ofPred_eq,
      creationTimeNat_eq_of_creation hcreation]
    exact hclock
  rcases raw_band_overflow_implies_normalized_totalOverflow hvalid hn
      hclockEq hfavorite hbudget hs with htotal | htotal
  · have hsplit := totalOverflow_subset_thresholdedGlobalBad
        (fun _ ↦ Set.univ)
        (normalizedDominantBandOccupancy t .even m
          (levelCutoffTime upperTailDelta m) band)
        (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48)
        shellGrowth48 (shellCount48 m band.beta) hstep htotal
    rcases hsplit with hfirst | hpositive
    · exact Or.inl (Or.inl hfirst)
    · apply Or.inr
      rw [mem_someThresholdedInterfaceBad_iff] at hpositive
      rcases hpositive with ⟨shell, hshell, hbad⟩
      exact Set.mem_iUnion.mpr ⟨LazyDecomposition.Orientation.even,
        Set.mem_iUnion.mpr ⟨shell,
        Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hshell,
          ⟨⟨hstage, hearly⟩, hbad⟩⟩⟩⟩
  · have hsplit := totalOverflow_subset_thresholdedGlobalBad
        (fun _ ↦ Set.univ)
        (normalizedDominantBandOccupancy t .shifted m
          (levelCutoffTime upperTailDelta m) band)
        (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48)
        shellGrowth48 (shellCount48 m band.beta) hstep htotal
    rcases hsplit with hfirst | hpositive
    · exact Or.inl (Or.inr hfirst)
    · apply Or.inr
      rw [mem_someThresholdedInterfaceBad_iff] at hpositive
      rcases hpositive with ⟨shell, hshell, hbad⟩
      exact Set.mem_iUnion.mpr ⟨LazyDecomposition.Orientation.shifted,
        Set.mem_iUnion.mpr ⟨shell,
        Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hshell,
          ⟨⟨hstage, hearly⟩, hbad⟩⟩⟩⟩

/-- Finite union of the literal first-shell overflows over all endpoint
bands with the displayed old-favorite rank.  Keeping this separate from
the four source payments makes the recurrence/source boundary explicit. -/
def initialShellOverflowUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandInitialShellOverflowEvent t m)

/-- The literal cofinal sharp-window contribution of all positive adjacent
shells in one band. -/
noncomputable def cofinalPositiveShellRealCost
    (m : ℕ) (band : RandomClockBand) : ℝ :=
  ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
    sharpInterfaceCost
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) shell

lemma cofinalPositiveShellRealCost_nonneg
    (m : ℕ) (band : RandomClockBand) :
    0 ≤ cofinalPositiveShellRealCost m band := by
  unfold cofinalPositiveShellRealCost
  exact Finset.sum_nonneg fun shell _ ↦ sharpInterfaceCost_nonneg _ shell

/-- The honest screened part is controlled directly by the concrete cofinal
sharp-window product.  The physical remainder is deliberately absent from
this estimate. -/
theorem simpleRandomWalk_bandPositiveInterfaceScreenedEvent_le
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) :
    simpleRandomWalk (bandPositiveInterfaceScreenedEvent data t m band) ≤
      ENNReal.ofReal (cofinalPositiveShellRealCost m band) := by
  rw [bandPositiveInterfaceScreenedEvent]
  split
  next h =>
    let threshold := geometricShellThreshold
      (initialBudget48 m) shellGrowth48
    rw [← ENNReal.ofReal_toReal
      (measure_ne_top simpleRandomWalk
        (⋃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
          earlyCreationStage m band.oldRank
              (levelCutoffTime upperTailDelta m) ∩
            positiveInterfaceScreenedEvent t band.orientation m band.oldRank
              band.externalThreshold h.1 band.oldRank_pos
              threshold shell ((data.interfaces t m band).totalBound shell)))]
    apply ENNReal.ofReal_mono
    calc
      simpleRandomWalk.real
          (⋃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
            earlyCreationStage m band.oldRank
                (levelCutoffTime upperTailDelta m) ∩
              positiveInterfaceScreenedEvent t band.orientation m band.oldRank
                band.externalThreshold h.1 band.oldRank_pos
                threshold shell
                  ((data.interfaces t m band).totalBound shell)) ≤
          ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
            simpleRandomWalk.real
              (earlyCreationStage m band.oldRank
                  (levelCutoffTime upperTailDelta m) ∩
                positiveInterfaceScreenedEvent t band.orientation m
                  band.oldRank band.externalThreshold h.1 band.oldRank_pos
                  threshold shell
                    ((data.interfaces t m band).totalBound shell)) := by
        apply measureReal_biUnion_finset_le
      _ ≤ ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
          sharpInterfaceCost threshold shell := by
        apply Finset.sum_le_sum
        intro shell _hshell
        calc
          simpleRandomWalk.real
              (earlyCreationStage m band.oldRank
                  (levelCutoffTime upperTailDelta m) ∩
                positiveInterfaceScreenedEvent t band.orientation m
                  band.oldRank band.externalThreshold h.1 band.oldRank_pos
                  threshold shell
                    ((data.interfaces t m band).totalBound shell)) ≤
            simpleRandomWalk.real
              (positiveInterfaceScreenedEvent t band.orientation m
                band.oldRank band.externalThreshold h.1 band.oldRank_pos
                threshold shell
                  ((data.interfaces t m band).totalBound shell)) :=
              measureReal_mono inter_subset_right
          _ ≤ sharpInterfaceCost threshold shell :=
            (positiveInterfaceScreenedProductData t band.orientation m
              band.oldRank band.externalThreshold h.1 band.oldRank_pos
              h.2.1 h.2.2 threshold shell
                ((data.interfaces t m band).totalBound shell)).simpleRandomWalk_real_next_le
      _ = cofinalPositiveShellRealCost m band := rfl
  next _ => simp

/-- One source-low band has at most `m` positive shells, each with the
literal sharp-window cost. -/
theorem cofinalPositiveShellRealCost_le_level_mul_exp
    {m : ℕ} (hm : 1 ≤ m) {band : RandomClockBand}
    (hbeta : band.beta ≤ (7 / 10 : ℝ)) :
    cofinalPositiveShellRealCost m band ≤
      (m : ℝ) * Real.exp
        (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
  unfold cofinalPositiveShellRealCost
  calc
    (∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        sharpInterfaceCost
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shell) ≤
      ∑ _shell ∈ Finset.range (shellCount48 m band.beta - 1),
        Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro shell _
      exact sharpInterfaceCost_geometric_le_exp_log_sq m shell
    _ = ((shellCount48 m band.beta - 1 : ℕ) : ℝ) *
        Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by simp
    _ ≤ (m : ℝ) * Real.exp
        (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
      gcongr
      exact_mod_cast (Nat.sub_le _ _).trans
        (shellCount48_le_level_of_beta_le_sevenTenths hm hbeta)

/-- Finite union of the honestly screened positive-shell payments over the
endpoint bands whose old favorite has the displayed rank.  The historical
name is retained for downstream rank-payment APIs; the unscreened physical
remainder is the separate event below. -/
def positiveInterfaceFailureUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfaceScreenedEvent data t m)

/-- The exact rankwise early-growth remainder not represented by the
active-window product screen.  No measure estimate is attached to this
event in the recurrence module. -/
def positiveInterfaceBalanceRemainderUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfaceBalanceRemainderEvent data t m)

/-- The raw rankwise candidate overflow is contained in its first shell, the
screened positive-interface payment, or the exact unscreened remainder.  The
only numerical inputs are the common large-level logarithmic inequality and
the literal lower endpoint bound on every source-product band. -/
theorem rankCandidateOverflowEvent_subset_initialShell_or_positiveInterface
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) {s : WalkPath} {n : ℕ}
    (hm : 1 ≤ m) (hlog : 1 ≤ Real.log (m : ℝ) ^ 2)
    (hcreation : ThresholdCreation s m rank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hvalid : s ∈ validStepWalk)
    (hclock : s ∈ earlyCreationStage m rank
      (levelCutoffTime upperTailDelta m))
    (hs : s ∈ rankCandidateOverflowEvent t m
      (levelCutoffTime upperTailDelta m) (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank) :
    s ∈ initialShellOverflowUnionAtRank data t rank m ∪
      (positiveInterfaceFailureUnionAtRank data t rank m ∪
        positiveInterfaceBalanceRemainderUnionAtRank data t rank m) := by
  rcases hs with ⟨band, hband, hoverflow⟩
  have hsource : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) := (Finset.mem_filter.mp hband).1
  have hbudget : geometricCandidateBudget48 m band.beta ≤
      candidateBudget48 m band.beta :=
    geometricCandidateBudget48_le_candidateBudget48 hm
      (sourceProductEndpointBand_betaLower hsource) hlog
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 *
          geometricShellThreshold (normalizedPositiveInitialBudget48 m)
            shellGrowth48 j ≤
        geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48 (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (normalizedPositiveInitialBudget48 m)
      shellGrowth48 j).le
  have hmstrict : 1 < m := by
    by_contra hnot
    have hmone : m = 1 := by omega
    subst m
    norm_num at hlog
  have hcreationBand : ThresholdCreation s m band.oldRank n := by
    simpa only [(Finset.mem_filter.mp hband).2] using hcreation
  have hclockNat : n ≤ levelCutoffTime upperTailDelta m := by
    rw [earlyCreationStage, Set.mem_ofPred_eq,
      creationTimeNat_eq_of_creation hcreation] at hclock
    exact hclock
  rcases bandCardOverflow_subset_initialShell_or_positiveInterface
      data t m band hmstrict hbudget hcreationBand hnext hclockNat hvalid
        hstep hoverflow with hfirst | hpositive
  · exact Or.inl ⟨band, hband, hfirst⟩
  · rcases bandPositiveInterfaceFailureEvent_subset_screened_union_remainder
        data t m band hpositive with hscreened | hremainder
    · exact Or.inr (Or.inl ⟨band, hband, hscreened⟩)
    · exact Or.inr (Or.inr ⟨band, hband, hremainder⟩)

theorem eventually_simpleRandomWalk_positiveInterfaceFailureUnionAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (positiveInterfaceFailureUnionAtRank data t rank m) ≤
        ENNReal.ofReal (Real.exp
          (-(sharpProductRate / 8) * Real.log (m : ℝ) ^ 2)) := by
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag)
    (show 0 < sharpProductRate / 8 by
      positivity [sharpProductRate_pos])
  filter_upwards [eventually_level_mul_exp_sharp_le, habsorb,
      eventually_ge_atTop (1 : ℕ)] with
      m hlevel habsorbM hm
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2))
  have heach : ∀ band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m),
      simpleRandomWalk (bandPositiveInterfaceScreenedEvent data t m band) ≤
        q := by
    intro band hband
    have hraw := simpleRandomWalk_bandPositiveInterfaceScreenedEvent_le
      data t m band
    refine hraw.trans ?_
    apply ENNReal.ofReal_mono
    refine (cofinalPositiveShellRealCost_le_level_mul_exp hm
      (sourceProductEndpointBand_betaUpperRange hband)).trans ?_
    refine hlevel.trans ?_
    apply Real.exp_le_exp.mpr
    have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
    have hr := sharpProductRate_pos
    nlinarith
  calc
    simpleRandomWalk (positiveInterfaceFailureUnionAtRank data t rank m) ≤
        ∑ band ∈ sourceProductEndpointBandsAtRank m
            (sourceCandidateLazyCap48 m)
            (data.externalThreshold m) rank,
          simpleRandomWalk (bandPositiveInterfaceScreenedEvent data t m band) :=
      Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
    _ ≤ ∑ band ∈ sourceProductEndpointBandsAtRank m
            (sourceCandidateLazyCap48 m)
            (data.externalThreshold m) rank,
          q := by
      apply Finset.sum_le_sum
      intro band hband
      exact heach band (Finset.mem_filter.mp hband).1
    _ ≤ ∑ band ∈ sourceProductEndpointBands m (sourceCandidateLazyCap48 m)
            (data.externalThreshold m),
          q := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ((sourceProductEndpointBands m (sourceCandidateLazyCap48 m)
          (data.externalThreshold m)).card : ℝ≥0∞) * q := by simp
    _ ≤ (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast sourceProductEndpointBands_card_le m
        (sourceCandidateLazyCap48 m) (data.externalThreshold m)
    _ ≤ _ := by
      simpa only [q, show 2 * (sharpProductRate / 8) =
        sharpProductRate / 4 by ring] using habsorbM

theorem simpleRandomWalk_positiveInterfaceFailureUnionAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (positiveInterfaceFailureUnionAtRank data t rank m) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (positiveInterfaceFailureUnionAtRank data t rank)
    (div_pos sharpProductRate_pos (by norm_num))
    (eventually_simpleRandomWalk_positiveInterfaceFailureUnionAtRank_le_exp
      data t rank)

/-! ## The four oriented source payments -/

/-- The canonical and transported opposite source screens for all endpoint
orientations at one old-favorite rank.  This is a payment event only: the
raw staged candidate remains the literal random-clock overflow above. -/
def allTilingSourcePaymentAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  let canonical :=
    canonicalSourceUnionAtRank data t .even rank m ∪
      canonicalSourceUnionAtRank data t .shifted rank m
  let opposite := match t with
    | .checker d =>
        shiftedCheckerSourceUnionAtRank data d .even rank m ∪
          shiftedCheckerSourceUnionAtRank data d .shifted rank m
    | .evenColumns | .oddColumns =>
        reflectedColumnSourceUnionAtRank data t .even rank m ∪
          reflectedColumnSourceUnionAtRank data t .shifted rank m
  canonical ∪ opposite

theorem measurableSet_allTilingSourcePaymentAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) :
    MeasurableSet (allTilingSourcePaymentAtRank data t rank m) := by
  cases t with
  | checker d =>
      exact ((measurableSet_canonicalSourceUnionAtRank data (.checker d)
          .even rank m).union
        (measurableSet_canonicalSourceUnionAtRank data (.checker d)
          .shifted rank m)).union
        ((measurableSet_shiftedCheckerSourceUnionAtRank data d .even rank m).union
          (measurableSet_shiftedCheckerSourceUnionAtRank data d .shifted rank m))
  | evenColumns =>
      exact ((measurableSet_canonicalSourceUnionAtRank data .evenColumns
          .even rank m).union
        (measurableSet_canonicalSourceUnionAtRank data .evenColumns
          .shifted rank m)).union
        ((measurableSet_reflectedColumnSourceUnionAtRank data .evenColumns
          .even rank m).union
          (measurableSet_reflectedColumnSourceUnionAtRank data .evenColumns
            .shifted rank m))
  | oddColumns =>
      exact ((measurableSet_canonicalSourceUnionAtRank data .oddColumns
          .even rank m).union
        (measurableSet_canonicalSourceUnionAtRank data .oddColumns
          .shifted rank m)).union
        ((measurableSet_reflectedColumnSourceUnionAtRank data .oddColumns
          .even rank m).union
          (measurableSet_reflectedColumnSourceUnionAtRank data .oddColumns
            .shifted rank m))

private theorem eventually_measure_union_four_le_exp
    {first second third fourth : ℕ → Set WalkPath} {c : ℝ} (hc : 0 < c)
    (hfirst : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (first m) ≤ ENNReal.ofReal
        (Real.exp (-c * Real.log (m : ℝ) ^ 2)))
    (hsecond : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (second m) ≤ ENNReal.ofReal
        (Real.exp (-c * Real.log (m : ℝ) ^ 2)))
    (hthird : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (third m) ≤ ENNReal.ofReal
        (Real.exp (-c * Real.log (m : ℝ) ^ 2)))
    (hfourth : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (fourth m) ≤ ENNReal.ofReal
        (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk ((first m ∪ second m) ∪ (third m ∪ fourth m)) ≤
        ENNReal.ofReal (Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2)) := by
  have hcHalf : 0 < c / 2 := div_pos hc (by norm_num)
  have hdouble : 2 * (c / 2) = c := by ring
  have habsorbRaw :=
    eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg 4 hcHalf
  have habsorb : ∀ᶠ m : ℕ in atTop,
      ((4 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-c * Real.log (m : ℝ) ^ 2)) ≤
        ENNReal.ofReal
          (Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2)) := by
    simpa only [hdouble] using habsorbRaw
  filter_upwards [hfirst, hsecond, hthird, hfourth, habsorb] with
      m hfirstM hsecondM hthirdM hfourthM habsorbM
  calc
    simpleRandomWalk ((first m ∪ second m) ∪ (third m ∪ fourth m)) ≤
        simpleRandomWalk (first m) + simpleRandomWalk (second m) +
          (simpleRandomWalk (third m) + simpleRandomWalk (fourth m)) :=
      (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ ((4 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
      calc
        simpleRandomWalk (first m) + simpleRandomWalk (second m) +
            (simpleRandomWalk (third m) + simpleRandomWalk (fourth m)) ≤
          ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) +
            ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) +
            (ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) +
              ENNReal.ofReal
                (Real.exp (-c * Real.log (m : ℝ) ^ 2))) := by gcongr
        _ = ((4 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
            (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by ring
    _ ≤ _ := by simpa using habsorbM

theorem eventually_simpleRandomWalk_allTilingSourcePaymentAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (allTilingSourcePaymentAtRank data t rank m) ≤
        ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 4) *
            Real.log (m : ℝ) ^ 2)) := by
  have hc : 0 < orientedRankUnionCentralTailRate
      shellZeroLocalRatioConstant / 2 :=
    div_pos (orientedRankUnionCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le) (by norm_num)
  have hrate :
      (orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) / 2 =
        orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 4 := by
    ring
  cases t with
  | checker d =>
      have hfirst :=
        eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
          data (.checker d) .even rank
      have hsecond :=
        eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
          data (.checker d) .shifted rank
      have hthird :=
        eventually_simpleRandomWalk_shiftedCheckerSourceUnionAtRank_le_exp
          data d .even rank
      have hfourth :=
        eventually_simpleRandomWalk_shiftedCheckerSourceUnionAtRank_le_exp
          data d .shifted rank
      simpa only [allTilingSourcePaymentAtRank, hrate] using
        eventually_measure_union_four_le_exp hc hfirst hsecond hthird hfourth
  | evenColumns =>
      have hfirst :=
        eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
          data .evenColumns .even rank
      have hsecond :=
        eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
          data .evenColumns .shifted rank
      have hthird :=
        eventually_simpleRandomWalk_reflectedColumnSourceUnionAtRank_le_exp
          data .evenColumns .even rank
      have hfourth :=
        eventually_simpleRandomWalk_reflectedColumnSourceUnionAtRank_le_exp
          data .evenColumns .shifted rank
      simpa only [allTilingSourcePaymentAtRank, hrate] using
        eventually_measure_union_four_le_exp hc hfirst hsecond hthird hfourth
  | oddColumns =>
      have hfirst :=
        eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
          data .oddColumns .even rank
      have hsecond :=
        eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
          data .oddColumns .shifted rank
      have hthird :=
        eventually_simpleRandomWalk_reflectedColumnSourceUnionAtRank_le_exp
          data .oddColumns .even rank
      have hfourth :=
        eventually_simpleRandomWalk_reflectedColumnSourceUnionAtRank_le_exp
          data .oddColumns .shifted rank
      simpa only [allTilingSourcePaymentAtRank, hrate] using
        eventually_measure_union_four_le_exp hc hfirst hsecond hthird hfourth

theorem simpleRandomWalk_allTilingSourcePaymentAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∑' m, simpleRandomWalk (allTilingSourcePaymentAtRank data t rank m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk
    (allTilingSourcePaymentAtRank data t rank)
    (div_pos (orientedRankUnionCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le) (by norm_num))
    (eventually_simpleRandomWalk_allTilingSourcePaymentAtRank_le_exp
      data t rank)

/-- The sole checker-shift obstruction, totalized to the empty event for the
two column tilings. -/
def allTilingCheckerOriginShiftPaidEvent
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  match t with
  | .checker _ => checkerOriginShiftPaidEvent rank m
  | .evenColumns => ∅
  | .oddColumns => ∅

theorem simpleRandomWalk_allTilingCheckerOriginShiftPaidEvent_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (allTilingCheckerOriginShiftPaidEvent t rank m) ≠ ∞ := by
  cases t with
  | checker d =>
      exact simpleRandomWalk_checkerOriginShiftPaidEvent_series_ne_top
        hProp13 rank hrank
  | evenColumns => simp [allTilingCheckerOriginShiftPaidEvent]
  | oddColumns => simp [allTilingCheckerOriginShiftPaidEvent]

/-! ## The common late stopped-clock payment -/

/-- A creation beyond the ceiling cutoff is one of the existing late-level
events.  This is independent of the tiling and is used before identifying a
random-clock first shell with its genuine creation-time source. -/
theorem creation_after_levelCutoff_mem_lateLevelSet
    {s : WalkPath} {m rank N : ℕ} (hrank : 0 < rank)
    (hcreation : ThresholdCreation s m rank N)
    (hnext : thresholdCount s N (m + 1) = 0)
    (hlate : levelCutoffTime upperTailDelta m < N) :
    s ∈ lateLevelSet upperTailDelta m rank := by
  have hcount : thresholdCount s N m = rank :=
    thresholdCount_eq_of_creation hrank hcreation
  have hfavorite : levelFavorite s m rank :=
    (levelFavorite_iff_thresholdCounts s m rank hrank).2
      ⟨N, hcount, hnext⟩
  refine ⟨?_, hfavorite⟩
  rw [thresholdTime_eq_creationTime hcreation]
  have hfloorCeil : ⌊levelCutoff upperTailDelta m⌋₊ ≤
      ⌈levelCutoff upperTailDelta m⌉₊ := Nat.floor_le_ceil _
  unfold levelCutoffTime at hlate
  exact_mod_cast hfloorCeil.trans_lt hlate

/-- Once the rank creation profile is fixed, a raw first-shell overflow is
either late or belongs to one of the four honest oriented spatial sources.
No source/Theta probability estimate is used in this deterministic step. -/
theorem bandInitialShellOverflow_mem_late_or_orientedCreationSource
    {t : DominoTiling} {m n : ℕ} {band : RandomClockBand} {s : WalkPath}
    (hm : 1 < m) (hcreation : ThresholdCreation s m band.oldRank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hvalid : s ∈ validStepWalk)
    (hoverflow : s ∈ bandInitialShellOverflowEvent t m band) :
    s ∈ lateLevelSet upperTailDelta m band.oldRank ∪
      orientedCreationSourceOverflowEvent t m band := by
  by_cases hclock : n ≤ levelCutoffTime upperTailDelta m
  · apply Or.inr
    have htruncated : pathTruncatedLevelTime m band.oldRank
        (levelCutoffTime upperTailDelta m) s = n := by
      rw [pathTruncatedLevelTime_eq_min_of_creation hcreation,
        Nat.min_eq_left hclock]
    rcases hoverflow with heven | hshifted
    · rcases
        normalizedSourceCut48_lt_creationSource_of_shellZeroOverflow
          (t := t) (o := .even) (band := band) (s := s) hm
          hcreation htruncated hnext hvalid heven with
          hcanonical | hopposite
      · exact Or.inl (Or.inl (Or.inl hcanonical))
      · exact Or.inl (Or.inr hopposite)
    · rcases
        normalizedSourceCut48_lt_creationSource_of_shellZeroOverflow
          (t := t) (o := .shifted) (band := band) (s := s) hm
          hcreation htruncated hnext hvalid hshifted with
          hcanonical | hopposite
      · exact Or.inl (Or.inl (Or.inr hcanonical))
      · exact Or.inr hopposite
  · apply Or.inl
    exact creation_after_levelCutoff_mem_lateLevelSet band.oldRank_pos
      hcreation hnext (Nat.lt_of_not_ge hclock)

/-- Orientation-neutral composition of the shell recurrence with creation
identification.  The profile hypothesis is purely deterministic and is
discharged below by each literal transition stage. -/
theorem preliminary_inter_rankCandidateOverflow_subset_rankPayments
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (preliminary : Set WalkPath)
    (hm : 1 ≤ m) (hlog : 1 ≤ Real.log (m : ℝ) ^ 2)
    (hprofile : ∀ s ∈ preliminary,
      ∃ n, ThresholdCreation s m rank n ∧
        thresholdCount s n (m + 1) = 0) :
    preliminary ∩
        rankCandidateOverflowEvent t m (levelCutoffTime upperTailDelta m)
          (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank ⊆
      validStepWalkᶜ ∪
        (positiveInterfaceFailureUnionAtRank data t rank m ∪
          (positiveInterfaceBalanceRemainderUnionAtRank data t rank m ∪
            (lateLevelSet upperTailDelta m rank ∪
              (preliminary ∩
                orientedCreationSourceOverflowUnionAtRank data t rank m)))) := by
  intro s hs
  have hmstrict : 1 < m := by
    by_contra hnot
    have hmone : m = 1 := by omega
    subst m
    norm_num at hlog
  by_cases hvalid : s ∈ validStepWalk
  · apply Or.inr
    rcases hprofile s hs.1 with ⟨n, hcreation, hnext⟩
    have hreach : s ∈ thresholdReachStage m rank :=
      ⟨n, hcreation.1⟩
    have hrank : 0 < rank := by
      rcases hs.2 with ⟨band, hband, _hoverflow⟩
      simpa only [(Finset.mem_filter.mp hband).2] using band.oldRank_pos
    by_cases hclock : s ∈ earlyCreationStage m rank
        (levelCutoffTime upperTailDelta m)
    · rcases rankCandidateOverflowEvent_subset_initialShell_or_positiveInterface
          data t rank m hm hlog hcreation hnext hvalid hclock hs.2 with
        hfirst | hpositive
      · rcases hfirst with ⟨band, hband, hoverflow⟩
        have hrank : band.oldRank = rank := (Finset.mem_filter.mp hband).2
        have hcreationBand : ThresholdCreation s m band.oldRank n := by
          rw [hrank]
          exact hcreation
        rcases bandInitialShellOverflow_mem_late_or_orientedCreationSource
            (t := t) (m := m) (band := band) (s := s) hmstrict
            hcreationBand hnext hvalid hoverflow with hlate | hsource
        · exact Or.inr (Or.inr (Or.inl
            (by simpa only [hrank] using hlate)))
        · exact Or.inr (Or.inr (Or.inr
            ⟨hs.1, band, hband, hsource⟩))
      · rcases hpositive with hscreened | hremainder
        · exact Or.inl hscreened
        · exact Or.inr (Or.inl hremainder)
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      apply creation_after_levelCutoff_mem_lateLevelSet hrank hcreation hnext
      simp only [earlyCreationStage, Set.mem_ofPred_eq,
        creationTimeNat_eq_of_creation hcreation] at hclock
      omega
  · exact Or.inl hvalid

/-- Rank-one raw candidate routed to positive interfaces, late creation, or
one of the four oriented creation sources. -/
theorem firstRawStagedCandidate_subset_rankPayments
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hlog : 1 ≤ Real.log (m : ℝ) ^ 2) :
    firstRawStagedCandidate data t m a ⊆
      validStepWalkᶜ ∪
        (positiveInterfaceFailureUnionAtRank data t 1 m ∪
          (positiveInterfaceBalanceRemainderUnionAtRank data t 1 m ∪
            (lateLevelSet upperTailDelta m 1 ∪
              (firstRawCandidatePreliminary t m a ∩
                orientedCreationSourceOverflowUnionAtRank data t 1 m)))) := by
  exact preliminary_inter_rankCandidateOverflow_subset_rankPayments
    data t 1 m (firstRawCandidatePreliminary t m a) hm hlog
      (fun s hs ↦ firstRawCandidatePreliminary_creationProfile hs)

/-- Rank-two raw payment route. -/
theorem secondRawStagedCandidate_subset_rankPayments
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hlog : 1 ≤ Real.log (m : ℝ) ^ 2) :
    secondRawStagedCandidate data t m a ⊆
      validStepWalkᶜ ∪
        (positiveInterfaceFailureUnionAtRank data t 2 m ∪
          (positiveInterfaceBalanceRemainderUnionAtRank data t 2 m ∪
            (lateLevelSet upperTailDelta m 2 ∪
              (secondRawCandidatePreliminary t m a ∩
                orientedCreationSourceOverflowUnionAtRank data t 2 m)))) := by
  exact preliminary_inter_rankCandidateOverflow_subset_rankPayments
    data t 2 m (secondRawCandidatePreliminary t m a) hm hlog
      (fun s hs ↦ secondRawCandidatePreliminary_creationProfile hs)

/-- Rank-three raw payment route. -/
theorem thirdRawStagedCandidate_subset_rankPayments
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hlog : 1 ≤ Real.log (m : ℝ) ^ 2) :
    thirdRawStagedCandidate data t m a ⊆
      validStepWalkᶜ ∪
        (positiveInterfaceFailureUnionAtRank data t 3 m ∪
          (positiveInterfaceBalanceRemainderUnionAtRank data t 3 m ∪
            (lateLevelSet upperTailDelta m 3 ∪
              (thirdRawCandidatePreliminary t m a ∩
                orientedCreationSourceOverflowUnionAtRank data t 3 m)))) := by
  exact preliminary_inter_rankCandidateOverflow_subset_rankPayments
    data t 3 m (thirdRawCandidatePreliminary t m a) hm hlog
      (fun s hs ↦ thirdRawCandidatePreliminary_creationProfile hs)

/-! ## The finite arithmetic prefix -/

/-- The explicit harmless prefix on which the recurrence arithmetic has not
yet reached its canonical large-level range.  Keeping it as an event makes
the final raw rank majorant unconditional in `m`, without storing a cutoff
or an eventual numerical hypothesis in the public data package. -/
def rawRankArithmeticFailureEvent (m : ℕ) : Set WalkPath :=
  if 1 ≤ m ∧ 1 ≤ Real.log (m : ℝ) ^ 2 then ∅ else Set.univ

theorem measurableSet_rawRankArithmeticFailureEvent (m : ℕ) :
    MeasurableSet (rawRankArithmeticFailureEvent m) := by
  unfold rawRankArithmeticFailureEvent
  split <;> simp

theorem eventually_rawRankArithmeticFailureEvent_eq_empty :
    ∀ᶠ m : ℕ in atTop, rawRankArithmeticFailureEvent m = ∅ := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog.eventually (eventually_ge_atTop (1 : ℝ))] with m hm hlogM
  rw [rawRankArithmeticFailureEvent, if_pos]
  exact ⟨hm, by nlinarith⟩

theorem simpleRandomWalk_rawRankArithmeticFailureEvent_series_ne_top :
    ∑' m, simpleRandomWalk (rawRankArithmeticFailureEvent m) ≠ ∞ := by
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk
    rawRankArithmeticFailureEvent (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_rawRankArithmeticFailureEvent_eq_empty] with m hm
  rw [hm]
  simp

theorem simpleRandomWalk_lateRankCutoff_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk (lateLevelSet upperTailDelta m rank) ≠ ∞ :=
  simpleRandomWalk_lateLevelAtRank_series_ne_top hProp13 rank hrank

/-! ## The unconditional recurrence-only rank payment -/

/-- The internally summable part of the raw shell recurrence: arithmetic
prefix, invalid walks, screened positive interfaces, and late creation.  The
unscreened interface remainder and literal oriented source/Theta terms are
both kept outside this event. -/
def rawRankRecurrencePaymentEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  rawRankArithmeticFailureEvent m ∪
    (validStepWalkᶜ ∪
      (positiveInterfaceFailureUnionAtRank data t rank m ∪
        lateLevelSet upperTailDelta m rank))

/-- The raw recurrence is unconditional in the level once the explicit
finite arithmetic prefix is included.  The two terms left outside the
summable recurrence payment are the exact unscreened positive-interface
remainder and the preliminary-stage oriented creation source. -/
theorem preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (preliminary : Set WalkPath)
    (hprofile : ∀ s ∈ preliminary,
      ∃ n, ThresholdCreation s m rank n ∧
        thresholdCount s n (m + 1) = 0) :
    preliminary ∩
        rankCandidateOverflowEvent t m (levelCutoffTime upperTailDelta m)
          (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank ⊆
      rawRankRecurrencePaymentEvent data t rank m ∪
        (positiveInterfaceBalanceRemainderUnionAtRank data t rank m ∪
          (preliminary ∩
            orientedCreationSourceOverflowUnionAtRank data t rank m)) := by
  intro s hs
  by_cases harithmetic :
      1 ≤ m ∧ 1 ≤ Real.log (m : ℝ) ^ 2
  · have hroute :=
      preliminary_inter_rankCandidateOverflow_subset_rankPayments
        data t rank m preliminary harithmetic.1 harithmetic.2 hprofile hs
    rcases hroute with hinvalid | hrest
    · exact Or.inl (Or.inr (Or.inl hinvalid))
    · rcases hrest with hpositive | hrest
      · exact Or.inl (Or.inr (Or.inr (Or.inl hpositive)))
      · rcases hrest with hremainder | hrest
        · exact Or.inr (Or.inl hremainder)
        · rcases hrest with hlate | hsource
          · exact Or.inl (Or.inr (Or.inr (Or.inr hlate)))
          · exact Or.inr (Or.inr hsource)
  · apply Or.inl
    apply Or.inl
    simp only [rawRankArithmeticFailureEvent, if_neg harithmetic,
      Set.mem_univ]

private theorem measure_union_series_ne_top
    {first second : ℕ → Set WalkPath}
    (hfirst : ∑' m, simpleRandomWalk (first m) ≠ ∞)
    (hsecond : ∑' m, simpleRandomWalk (second m) ≠ ∞) :
    ∑' m, simpleRandomWalk (first m ∪ second m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (first m) + simpleRandomWalk (second m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩
  exact ne_top_of_le_ne_top hmajor
    (ENNReal.tsum_le_tsum fun m ↦ measure_union_le _ _)

theorem simpleRandomWalk_validStepWalk_compl_series_ne_top :
    ∑' _m : ℕ, simpleRandomWalk validStepWalkᶜ ≠ ∞ := by
  simp only [HLOZLazyOverflowClosure.simpleRandomWalk_validStepWalk_compl]
  simp

/-- The recurrence-only rank payment is summable without any source-fiber,
Theta, or candidate-event probability premise. -/
theorem simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (rawRankRecurrencePaymentEvent data t rank m) ≠ ∞ := by
  exact measure_union_series_ne_top
    simpleRandomWalk_rawRankArithmeticFailureEvent_series_ne_top
    (measure_union_series_ne_top
      simpleRandomWalk_validStepWalk_compl_series_ne_top
      (measure_union_series_ne_top
        (simpleRandomWalk_positiveInterfaceFailureUnionAtRank_series_ne_top
          data t rank)
        (simpleRandomWalk_lateRankCutoff_series_ne_top
          hProp13 rank hrank)))

/-! ## Direct candidate-local product overflow routing -/

/-- The exact overflow term produced by the no-lazy candidate-local product
screen. -/
def candidateLocalProductOverflowEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
      (data.externalThreshold m) ∩
    tilingRandomClockCandidateOverflow t m
      (levelCutoffTime upperTailDelta m)
      (sourceProductEndpointBands m (sourceCandidateLazyCap48 m)
        (data.externalThreshold m))

/-- Definitional bridge to the carrier-free rank-split event. -/
theorem candidateLocalProductOverflowEvent_eq_rankSplit
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalProductOverflowEvent data t m =
      (HLOZNoLazyCandidateRankSplit.candidateLocalProductOverflowEvent
        t m (levelCutoffTime upperTailDelta m)
          (sourceCandidateLazyCap48 m) (data.externalThreshold m)) := rfl

/-- The only rankwise source term left after the recurrence split, now
restricted to the actual candidate-local product event. -/
def candidateLocalOrientedSourceEventAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
      (data.externalThreshold m) ∩
    orientedCreationSourceOverflowUnionAtRank data t rank m

/-- Rankwise candidate-local portion of the exact positive-interface
reconstruction remainder. -/
def candidateLocalPositiveInterfaceBalanceRemainderAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
      (data.externalThreshold m) ∩
    positiveInterfaceBalanceRemainderUnionAtRank data t rank m

/-- Three-rank recurrence payment for the direct product screen. -/
def candidateLocalProductRecurrencePaymentEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  rawRankRecurrencePaymentEvent data t 1 m ∪
    (rawRankRecurrencePaymentEvent data t 2 m ∪
      rawRankRecurrencePaymentEvent data t 3 m)

/-- Three-rank literal oriented-source remainder.  The corrected
static-source/Theta transport layer will majorize this event without changing
the candidate-local product screen. -/
def candidateLocalProductOrientedSourceEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  candidateLocalOrientedSourceEventAtRank data t 1 m ∪
    (candidateLocalOrientedSourceEventAtRank data t 2 m ∪
      candidateLocalOrientedSourceEventAtRank data t 3 m)

/-- The exact three-rank positive-interface balance/reconstruction
remainder.  This event is intentionally outside the internally summable
recurrence payment. -/
def candidateLocalProductPositiveInterfaceBalanceRemainderEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  candidateLocalPositiveInterfaceBalanceRemainderAtRank data t 1 m ∪
    (candidateLocalPositiveInterfaceBalanceRemainderAtRank data t 2 m ∪
      candidateLocalPositiveInterfaceBalanceRemainderAtRank data t 3 m)

/-- Carrier-independent direct product routing.  The finite endpoint list is
split into the three old-favorite ranks; each rank uses the terminal
candidate-local creation profile proved without a lazy filter. -/
theorem candidateLocalProductOverflowEvent_subset_recurrence_or_source
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalProductOverflowEvent data t m ⊆
      candidateLocalProductRecurrencePaymentEvent data t m ∪
        (candidateLocalProductPositiveInterfaceBalanceRemainderEvent data t m ∪
          candidateLocalProductOrientedSourceEvent data t m) := by
  intro s hs
  by_cases harithmetic : 1 ≤ m ∧ 1 ≤ Real.log (m : ℝ) ^ 2
  · have hm : 0 < m := lt_of_lt_of_le (by omega) harithmetic.1
    have hranks :=
      tilingRandomClockCandidateOverflow_sourceProduct_subset_rank_union
        t m (levelCutoffTime upperTailDelta m)
        (sourceCandidateLazyCap48 m) (data.externalThreshold m) hs.2
    rcases hranks with hrank | hrank | hrank
    · have hroute :=
        preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
          data t 1 m
          (onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
            (data.externalThreshold m))
          (fun u hu ↦ by
            rcases onTimeCandidateLocalProductBeta_rankOne_creationSourceData
              hm hu with ⟨n, hcreation, hnext, _hD⟩
            exact ⟨n, hcreation, hnext⟩)
          ⟨hs.1, hrank⟩
      rcases hroute with hrecurrence | hremainderOrSource
      · exact Or.inl (Or.inl hrecurrence)
      · rcases hremainderOrSource with hremainder | hsource
        · exact Or.inr (Or.inl (Or.inl ⟨hs.1, hremainder⟩))
        · exact Or.inr (Or.inr (Or.inl hsource))
    · have hroute :=
        preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
          data t 2 m
          (onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
            (data.externalThreshold m))
          (fun u hu ↦ by
            rcases onTimeCandidateLocalProductBeta_rankTwo_creationSourceData
              hm hu with ⟨n, hcreation, hnext, _hD⟩
            exact ⟨n, hcreation, hnext⟩)
          ⟨hs.1, hrank⟩
      rcases hroute with hrecurrence | hremainderOrSource
      · exact Or.inl (Or.inr (Or.inl hrecurrence))
      · rcases hremainderOrSource with hremainder | hsource
        · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hs.1, hremainder⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hsource)))
    · have hroute :=
        preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
          data t 3 m
          (onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
            (data.externalThreshold m))
          (fun u hu ↦ by
            rcases onTimeCandidateLocalProductBeta_rankThree_creationSourceData
              hm hu with ⟨n, hcreation, hnext, _hD⟩
            exact ⟨n, hcreation, hnext⟩)
          ⟨hs.1, hrank⟩
      rcases hroute with hrecurrence | hremainderOrSource
      · exact Or.inl (Or.inr (Or.inr hrecurrence))
      · rcases hremainderOrSource with hremainder | hsource
        · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hs.1, hremainder⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hsource)))
  · apply Or.inl
    apply Or.inl
    apply Or.inl
    simp only [rawRankArithmeticFailureEvent, if_neg harithmetic,
      Set.mem_univ]

/-- The recurrence half of the direct candidate-local product overflow is
summable without any shell-zero or Theta input. -/
theorem
    simpleRandomWalk_candidateLocalProductRecurrencePaymentEvent_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalProductRecurrencePaymentEvent data t m) ≠ ∞ := by
  exact measure_union_series_ne_top
    (simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
      hProp13 data t 1 (by omega))
    (measure_union_series_ne_top
      (simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
        hProp13 data t 2 (by omega))
      (simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
        hProp13 data t 3 (by omega)))

/-- The exact candidate-local overflow is summable once the two honest
remainders are summable: the unscreened positive-interface balance term and
the oriented source term.  The screened interface, late, and finite-prefix
terms are discharged internally. -/
theorem
    simpleRandomWalk_candidateLocalProductOverflowEvent_series_ne_top_of_balance_and_source
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (hbalance : ∑' m, simpleRandomWalk
      (candidateLocalProductPositiveInterfaceBalanceRemainderEvent data t m) ≠ ∞)
    (hsource : ∑' m, simpleRandomWalk
      (candidateLocalProductOrientedSourceEvent data t m) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (candidateLocalProductOverflowEvent data t m) ≠ ∞ := by
  have hmajor := measure_union_series_ne_top
    (simpleRandomWalk_candidateLocalProductRecurrencePaymentEvent_series_ne_top
      hProp13 data t) (measure_union_series_ne_top hbalance hsource)
  exact ne_top_of_le_ne_top hmajor <|
    ENNReal.tsum_le_tsum fun m ↦ measure_mono
      (candidateLocalProductOverflowEvent_subset_recurrence_or_source
        data t m)

end

end Erdos1165.HLOZRawFullGapProductPromotion
