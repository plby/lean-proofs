/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZMixedSpatialTransitionFactors
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateConditionalProduct
import ErdosProblems.Erdos1165.HLOZTilingConditionalCandidateWindows

/-!
# Rankwise low factors from the conditional candidate product

This module is the conditional-denominator counterpart of
`CandidateBudgetTypedLowTransitionData`.  The stopped-history coordinate
package contains the broad `I₁ / D_eta / Theta / exact-S` denominator and
its selected narrow numerator.  The atomwise future escape certificate is
not a field of that deterministic package: it is supplied only to the final
constructor.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZConditionalMixedSpatialTransitionFactors

open HLOZHeterogeneousFilteredTransitionFactors
open HLOZMixedSpatialTransitionFactors
open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open HLOZTypedStoppedCandidateConditionalProduct HLOZTypedStoppedCandidateFamily
open HLOZTilingGapRandomClockScreen
open TilingConditionalCappedMarginalization TilingTypedFavoriteTrace
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- All stopped-past data for one low rank, through the checked conditional
coordinate product.  No future event or transition inequality occurs in
this structure. -/
structure CandidateBudgetTypedLowConditionalCoordinateData
    (t : DominoTiling) (m k : ℕ) (previous : Set WalkPath)
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
    (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
    (x : Point), x ∈ typedStoppedCandidates h →
      TilingConditionalFactoredStoppedCoordinateData
        (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
          (candidateBudget48 m band.beta) stage previous band h)
        (typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h ∩
          typedStoppedCandidateNear m cutoff band window h x)
        candidateRatio

namespace CandidateBudgetTypedLowConditionalCoordinateData

/-- The literal stopped-history candidate family constructed from the
conditional coordinate package. -/
noncomputable def family
    {t : DominoTiling} {m k : ℕ} {previous : Set WalkPath}
    {candidateRatio : ℝ≥0∞}
    (data : CandidateBudgetTypedLowConditionalCoordinateData
      t m k previous candidateRatio) :
    StoppedHistoryCandidateFamily
      (TypedStoppedCandidateHistory t (candidateBudget48 m data.band.beta))
      Point previous (candidateBudget48 m data.band.beta) candidateRatio :=
  conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
    t m k data.cutoff data.stage previous data.band data.window candidateRatio
      data.stage_measurable data.previous_measurable data.stage_subset
        data.candidateRatio_ne_top data.coordinateData

/-- Add only the independent atomwise strong-Markov future certificate and
the deterministic numerical cost comparison.  This is the requested
rankwise low factor; no past-to-next probability inequality is assumed. -/
noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {t : DominoTiling} {m k : ℕ} {previous next : Set WalkPath}
    {candidateRatio escapeCost q : ℝ≥0∞}
    (data : CandidateBudgetTypedLowConditionalCoordinateData
      t m k previous candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : (candidateBudget48 m data.band.beta : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q := by
  exact .of
    (conditionalCandidateBudgetTypedSourceCorrectTransitionFactorLowAtomwise
      (Index := Index) (State := State)
      t m k data.cutoff data.stage previous next data.band data.window
      candidateRatio escapeCost q data.stage_measurable
      data.previous_measurable data.stage_subset data.candidateRatio_ne_top
      data.coordinateData escape cost_le)

end CandidateBudgetTypedLowConditionalCoordinateData

/-- Rank-one deterministic low data start from the full previous path
space; the invalid-support and overflow atoms remain in the typed history
partition. -/
abbrev FirstCandidateBudgetTypedLowConditionalCoordinateData
    (t : DominoTiling) (m : ℕ) (candidateRatio : ℝ≥0∞) :=
  CandidateBudgetTypedLowConditionalCoordinateData
    t m 1 Set.univ candidateRatio

/-- Rank-two deterministic low data use the already filtered first stage as
their previous event. -/
abbrev SecondCandidateBudgetTypedLowConditionalCoordinateData
    (t : DominoTiling) (m : ℕ) (previous : Set WalkPath)
    (candidateRatio : ℝ≥0∞) :=
  CandidateBudgetTypedLowConditionalCoordinateData
    t m 2 previous candidateRatio

/-- Rank-three deterministic low data use the already filtered second stage
as their previous event. -/
abbrev ThirdCandidateBudgetTypedLowConditionalCoordinateData
    (t : DominoTiling) (m : ℕ) (previous : Set WalkPath)
    (candidateRatio : ℝ≥0∞) :=
  CandidateBudgetTypedLowConditionalCoordinateData
    t m 3 previous candidateRatio

end

end Erdos1165.HLOZConditionalMixedSpatialTransitionFactors
