/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCanonicalDominantCandidateWindows
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateConditionalProduct

/-!
# The conditional stopped-history family for the canonical dominant source

This is the low Proposition 4.9 family whose histories and candidates use
the normalized canonical dominant band set throughout.  It does not adapt
back to the raw endpoint set.  The conditional coordinate certificate fixes
the broad `D_eta / Theta / exact-S` history and adds the selected narrow
window.  The future escape certificate remains a separate final input.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCanonicalDominantStoppedCandidateFamily

open HLOZDominantStoppedCandidatePartition HLOZGapRandomClockScreen
open HLOZPathEvents HLOZProposition48Candidates
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open HLOZTilingGapRandomClockScreen HLOZTraceCappedProductScreening
open HLOZTypedStoppedCandidateConditionalProduct
open HLOZTypedStoppedCandidateFamily TilingConditionalCappedMarginalization
open TilingTypedFavoriteTrace VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Narrow stopped window attached to a canonical dominant history. -/
def canonicalDominantStoppedCandidateNear
    {t : DominoTiling} {budget : ℕ} (m cutoff : ℕ)
    (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ) :
    DominantStoppedCandidateHistory t budget → Point → Set WalkPath
  | none, _ => ∅
  | some (z, _), x => stoppedCandidateWindowEvent m cutoff band window z x

theorem measurableSet_canonicalDominantStoppedCandidateNear
    {t : DominoTiling} {budget : ℕ} (m cutoff : ℕ)
    (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (h : DominantStoppedCandidateHistory t budget) (x : Point) :
    MeasurableSet
      (canonicalDominantStoppedCandidateNear m cutoff band window h x) := by
  cases h with
  | none => exact MeasurableSet.empty
  | some h =>
      exact measurableSet_stoppedCandidateWindowEvent
        m cutoff band window h.1 x

/-- Exact conditional canonical-dominant stopped-history family. -/
noncomputable def conditionalCanonicalDominantStoppedHistoryCandidateFamily
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : DominantStoppedCandidateHistory t budget) (x : Point),
      x ∈ dominantStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ dominantStoppedCandidatePiece .canonical
            t m k cutoff budget stage previous band h)
          (dominantStoppedCandidatePiece .canonical
              t m k cutoff budget stage previous band h ∩
            canonicalDominantStoppedCandidateNear
              m cutoff band window h x)
          ratio) :
    StoppedHistoryCandidateFamily
      (DominantStoppedCandidateHistory t budget) Point previous budget ratio where
  piece := dominantStoppedCandidatePiece .canonical
    t m k cutoff budget stage previous band
  candidates := dominantStoppedCandidates
  near := canonicalDominantStoppedCandidateNear m cutoff band window
  piece_pairwise := pairwise_disjoint_dominantStoppedCandidatePiece
    .canonical t m k cutoff budget hstage previous band
  piece_measurable := measurableSet_dominantStoppedCandidatePiece
    .canonical t m k cutoff budget hstageMeasurable hpreviousMeasurable band
  piece_union := iUnion_dominantStoppedCandidatePiece
    .canonical t m k cutoff budget hstage band
  candidate_card := dominantStoppedCandidates_card_le
  coordinate_ratio := by
    intro h x hx
    exact coordinate_ratio_of_tilingConditionalFactoredStoppedCoordinateData
      (measurableSet_dominantStoppedCandidatePiece .canonical
        t m k cutoff budget hstageMeasurable hpreviousMeasurable band h)
      (measurableSet_canonicalDominantStoppedCandidateNear
        m cutoff band window h x)
      hratio (coordinateData h x hx)

/-- Membership in the selected source, its narrow window, and the explicit
source budget place every filtered target in the concrete some-candidate
event. -/
theorem next_subset_conditionalCanonicalDominantStoppedHistorySomeCandidate
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnextPrevious : next ⊆ previous)
    (hnextBudget : ∀ s ∈ next,
      (tilingCanonicalDominantRandomClockBandSites
        t m cutoff s band).card ≤ budget)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : DominantStoppedCandidateHistory t budget) (x : Point),
      x ∈ dominantStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ dominantStoppedCandidatePiece .canonical
            t m k cutoff budget stage previous band h)
          (dominantStoppedCandidatePiece .canonical
              t m k cutoff budget stage previous band h ∩
            canonicalDominantStoppedCandidateNear
              m cutoff band window h x)
          ratio)
    (hsmallWindow : ∀ s ∈ next,
      ∃ (z : TypedFavoriteTilingTraceCode t) (x : Point),
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        x ∈ tilingCanonicalDominantRandomClockBandSites
          t m cutoff s band ∧
        s ∈ stoppedCandidateWindowEvent m cutoff band window z x) :
    next ⊆
      (conditionalCanonicalDominantStoppedHistoryCandidateFamily
        t m k cutoff budget stage previous band window ratio
          hstageMeasurable hpreviousMeasurable hstage hratio
            coordinateData).someCandidate := by
  classical
  intro s hs
  rcases hsmallWindow s hs with ⟨z, x, hz, hx, hwindow⟩
  have hprev := hnextPrevious hs
  let S : Finset Point :=
    tilingCanonicalDominantRandomClockBandSites t m cutoff s band
  let h : DominantStoppedCandidateHistory t budget := some (z, S)
  refine Set.mem_iUnion.mpr ⟨h, Set.mem_iUnion.mpr ⟨x, ?_⟩⟩
  refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
  · change x ∈ dominantStoppedCandidates h
    simpa only [h, dominantStoppedCandidates, S,
      if_pos (hnextBudget s hs)] using hx
  · exact ⟨⟨⟨hprev, hz⟩, rfl⟩, hwindow⟩

/-- A raw candidate-card bound is sufficient for the canonical source
budget, while histories still record only the canonical normalized set. -/
theorem next_subset_conditionalCanonicalDominantSomeCandidate_of_rawBudget
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnextPrevious : next ⊆ previous)
    (hnextRawBudget : ∀ s ∈ next,
      (tilingRandomClockBandSites t m cutoff s band).card ≤ budget)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : DominantStoppedCandidateHistory t budget) (x : Point),
      x ∈ dominantStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ dominantStoppedCandidatePiece .canonical
            t m k cutoff budget stage previous band h)
          (dominantStoppedCandidatePiece .canonical
              t m k cutoff budget stage previous band h ∩
            canonicalDominantStoppedCandidateNear
              m cutoff band window h x)
          ratio)
    (hsmallWindow : ∀ s ∈ next,
      ∃ (z : TypedFavoriteTilingTraceCode t) (x : Point),
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        x ∈ tilingCanonicalDominantRandomClockBandSites
          t m cutoff s band ∧
        s ∈ stoppedCandidateWindowEvent m cutoff band window z x) :
    next ⊆
      (conditionalCanonicalDominantStoppedHistoryCandidateFamily
        t m k cutoff budget stage previous band window ratio
          hstageMeasurable hpreviousMeasurable hstage hratio
            coordinateData).someCandidate :=
  next_subset_conditionalCanonicalDominantStoppedHistorySomeCandidate
    t m k cutoff budget stage previous next band window ratio
      hstageMeasurable hpreviousMeasurable hstage hnextPrevious
      (fun s hs ↦ dominantSourceRandomClockBandSites_card_le_of_raw
        .canonical t m cutoff budget s band (hnextRawBudget s hs))
      hratio coordinateData hsmallWindow

/-! ## Public low factor with future escape kept separate -/

noncomputable def conditionalCanonicalDominantSourceCorrectTransitionFactorLowAtomwise
    {Index : Type} {State : Type*} [Countable Index] [Countable State]
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (candidateRatio escapeCost q : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : candidateRatio ≠ ∞)
    (coordinateData : ∀
      (h : DominantStoppedCandidateHistory t budget) (x : Point),
      x ∈ dominantStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ dominantStoppedCandidatePiece .canonical
            t m k cutoff budget stage previous band h)
          (dominantStoppedCandidatePiece .canonical
              t m k cutoff budget stage previous band h ∩
            canonicalDominantStoppedCandidateNear
              m cutoff band window h x)
          candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      (conditionalCanonicalDominantStoppedHistoryCandidateFamily
        t m k cutoff budget stage previous band window candidateRatio
          hstageMeasurable hpreviousMeasurable hstage hratio
            coordinateData).someCandidate
      next escapeCost)
    (cost_le : (budget : ℝ≥0∞) * candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (DominantStoppedCandidateHistory t budget) Point State previous next q := by
  let family := conditionalCanonicalDominantStoppedHistoryCandidateFamily
    t m k cutoff budget stage previous band window candidateRatio
      hstageMeasurable hpreviousMeasurable hstage hratio coordinateData
  exact .lowAtomwise budget candidateRatio escapeCost
    { candidate := family, escape := escape } cost_le

/-- Deterministic stopped-past data for one canonical low rank.  It contains
no target transition probability or future escape field. -/
structure CanonicalDominantTypedLowConditionalCoordinateData
    (t : DominoTiling) (m k budget : ℕ) (previous : Set WalkPath)
    (candidateRatio : ℝ≥0∞) where
  cutoff : ℕ
  stage : Set WalkPath
  band : RandomClockBand
  window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ
  stage_measurable : MeasurableSet stage
  previous_measurable : MeasurableSet previous
  stage_subset : stage ⊆ thresholdReachStage m k
  candidateRatio_ne_top : candidateRatio ≠ ∞
  coordinateData : ∀
    (h : DominantStoppedCandidateHistory t budget) (x : Point),
    x ∈ dominantStoppedCandidates h →
      TilingConditionalFactoredStoppedCoordinateData
        (fun _ : Unit ↦ dominantStoppedCandidatePiece .canonical
          t m k cutoff budget stage previous band h)
        (dominantStoppedCandidatePiece .canonical
            t m k cutoff budget stage previous band h ∩
          canonicalDominantStoppedCandidateNear
            m cutoff band window h x)
        candidateRatio

namespace CanonicalDominantTypedLowConditionalCoordinateData

noncomputable def family
    {t : DominoTiling} {m k budget : ℕ} {previous : Set WalkPath}
    {candidateRatio : ℝ≥0∞}
    (data : CanonicalDominantTypedLowConditionalCoordinateData
      t m k budget previous candidateRatio) :
    StoppedHistoryCandidateFamily
      (DominantStoppedCandidateHistory t budget) Point previous budget
        candidateRatio :=
  conditionalCanonicalDominantStoppedHistoryCandidateFamily
    t m k data.cutoff budget data.stage previous data.band data.window
      candidateRatio data.stage_measurable data.previous_measurable
        data.stage_subset data.candidateRatio_ne_top data.coordinateData

noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {t : DominoTiling} {m k budget : ℕ} {previous next : Set WalkPath}
    {candidateRatio escapeCost q : ℝ≥0∞}
    (data : CanonicalDominantTypedLowConditionalCoordinateData
      t m k budget previous candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : (budget : ℝ≥0∞) * candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (DominantStoppedCandidateHistory t budget) Point State previous next q :=
  conditionalCanonicalDominantSourceCorrectTransitionFactorLowAtomwise
    t m k data.cutoff budget data.stage previous next data.band data.window
      candidateRatio escapeCost q data.stage_measurable
        data.previous_measurable data.stage_subset data.candidateRatio_ne_top
          data.coordinateData escape cost_le

end CanonicalDominantTypedLowConditionalCoordinateData

end

end Erdos1165.HLOZCanonicalDominantStoppedCandidateFamily
