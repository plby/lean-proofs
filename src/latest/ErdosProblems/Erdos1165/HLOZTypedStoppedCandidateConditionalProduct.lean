/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateFamily
import ErdosProblems.Erdos1165.TilingConditionalCappedMarginalization

/-!
# Conditional product data for typed stopped candidates

This module replaces the unconditional denominator in the original typed
candidate constructor by the literal broad-history denominator supplied by
`TilingConditionalFactoredStoppedCoordinateData`.  It exposes ordinary and
atomwise `SourceCorrectTransitionFactor.low` constructors.  Their only
quantitative past input is the checked finite conditional coordinate ratio;
no transition-probability inequality is assumed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTypedStoppedCandidateConditionalProduct

open CappedCoordinateMassCertificate
open HLOZStoppedHistoryCandidateFuture HLOZSourceCorrectFutureTransition
open HLOZTraceCappedProductScreening
open HLOZGapRandomClockScreen HLOZPathEvents HLOZTilingGapRandomClockScreen
open HLOZTypedStoppedCandidateFamily HLOZProposition48Candidates
open TilingConditionalCappedMarginalization
open TilingTypedFavoriteTrace
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## One-history conditional coordinate ratio -/

/-- A coordinate-mass specification with an arbitrary cap schedule and
arbitrary measurable stopped fibers already supplies the candidate ratio.
This is the primitive used by endpoint-oriented fibers: their physical
initial prefix contributes to `commonFactor`, and their logical cap index
need not equal the actual coordinate cutoff. -/
theorem coordinate_ratio_of_coordinateMassSpec
    {piece near : Set WalkPath} {ratio : ℝ≥0∞}
    (hpiece : MeasurableSet piece) (hnear : MeasurableSet near)
    (hratio : ratio ≠ ∞)
    (data : CoordinateMassSpec
      (fun _ : Unit ↦ piece) (piece ∩ near) ratio) :
    simpleRandomWalk (piece ∩ near) ≤ ratio * simpleRandomWalk piece := by
  let screen : @TraceCappedProductScreening Unit inferInstance
      piece (piece ∩ near) ratio :=
    { piece := fun _ ↦ piece
      measurable_piece := fun _ ↦ hpiece
      disjoint_piece := by
        intro a b hab
        cases a
        cases b
        exact (hab rfl).elim
      union_piece := by
        apply Set.Subset.antisymm
        · exact Set.iUnion_subset fun _ ↦ Subset.rfl
        · intro s hs
          exact Set.mem_iUnion_of_mem () hs
      next_subset_stage := inter_subset_left
      certificate := cappedProductScreenCertificateOfCoordinateMassSpec data }
  exact @transition_measure_le_of_traceCappedProductScreening Unit
    inferInstance piece (piece ∩ near) (hpiece.inter hnear) ratio hratio screen

/-- A literal conditional stopped-coordinate product law on one history
atom implies the required candidate-coordinate ratio. -/
theorem coordinate_ratio_of_tilingConditionalFactoredStoppedCoordinateData
    {piece near : Set WalkPath} {ratio : ℝ≥0∞}
    (hpiece : MeasurableSet piece) (hnear : MeasurableSet near)
    (hratio : ratio ≠ ∞)
    (data : TilingConditionalFactoredStoppedCoordinateData
      (fun _ : Unit ↦ piece) (piece ∩ near) ratio) :
    simpleRandomWalk (piece ∩ near) ≤ ratio * simpleRandomWalk piece := by
  exact coordinate_ratio_of_coordinateMassSpec hpiece hnear hratio
    (coordinateMassSpecOfTilingConditionalFactoredData data)

/-! ## The conditional typed stopped-history family -/

/-- Typed candidate family whose coordinate ratio is obtained from the
nontrivial broad-history denominator. -/
noncomputable def conditionalTypedStoppedHistoryCandidateFamily
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t budget) (x : Point),
      x ∈ typedStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece
            t m k cutoff budget stage previous band h)
          (typedStoppedCandidatePiece
              t m k cutoff budget stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio) :
    StoppedHistoryCandidateFamily
      (TypedStoppedCandidateHistory t budget) Point previous budget ratio where
  piece := typedStoppedCandidatePiece
    t m k cutoff budget stage previous band
  candidates := typedStoppedCandidates
  near := typedStoppedCandidateNear m cutoff band window
  piece_pairwise := pairwise_disjoint_typedStoppedCandidatePiece
    t m k cutoff budget hstage previous band
  piece_measurable := measurableSet_typedStoppedCandidatePiece
    t m k cutoff budget hstageMeasurable hpreviousMeasurable band
  piece_union := iUnion_typedStoppedCandidatePiece
    t m k cutoff budget hstage band
  candidate_card := typedStoppedCandidates_card_le
  coordinate_ratio := by
    intro h x hx
    exact coordinate_ratio_of_tilingConditionalFactoredStoppedCoordinateData
      (measurableSet_typedStoppedCandidatePiece
        t m k cutoff budget hstageMeasurable hpreviousMeasurable band h)
      (measurableSet_typedStoppedCandidateNear m cutoff band window h x)
      hratio (coordinateData h x hx)

/-- Source-compatible specialization to the actual Proposition 4.8
candidate budget. -/
noncomputable def conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio) :
    StoppedHistoryCandidateFamily
      (TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      Point previous (candidateBudget48 m band.beta) ratio :=
  conditionalTypedStoppedHistoryCandidateFamily t m k cutoff
    (candidateBudget48 m band.beta) stage previous band window ratio
    hstageMeasurable hpreviousMeasurable hstage hratio coordinateData

/-- The target-local no-overflow and narrow-window witnesses place the
filtered target inside the concrete conditional family's `someCandidate`
event.  Overflow histories remain in the exact preceding-event partition. -/
theorem next_subset_conditionalCandidateBudgetTypedStoppedHistorySomeCandidate
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnextPrevious : next ⊆ previous)
    (hnextNoOverflow : next ⊆
      {s : WalkPath | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card}ᶜ)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio)
    (hsmallWindow : ∀ s ∈ next,
      ∃ (z : TypedFavoriteTilingTraceCode t) (x : Point),
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        x ∈ tilingRandomClockBandSites t m cutoff s band ∧
        s ∈ stoppedCandidateWindowEvent m cutoff band window z x) :
    next ⊆
      (conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
        t m k cutoff stage previous band window ratio hstageMeasurable
        hpreviousMeasurable hstage hratio coordinateData).someCandidate := by
  classical
  intro s hs
  rcases hsmallWindow s hs with ⟨z, x, hz, hx, hwindow⟩
  have hprev := hnextPrevious hs
  have hbudget := tilingRandomClockBandSites_card_le_candidateBudget48
    t m cutoff band (hnextNoOverflow hs)
  let S : Finset Point := tilingRandomClockBandSites t m cutoff s band
  let h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta) :=
    some (z, S)
  refine Set.mem_iUnion.mpr ⟨h, Set.mem_iUnion.mpr ⟨x, ?_⟩⟩
  refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
  · change x ∈ typedStoppedCandidates h
    simpa only [h, typedStoppedCandidates, S, if_pos hbudget] using hx
  · exact ⟨⟨⟨hprev, hz⟩, rfl⟩, hwindow⟩

/-! ## Public low-scale constructors -/

/-- Direct ordinary strong-Markov constructor from the conditional stopped
coordinate family. -/
noncomputable def conditionalCandidateBudgetTypedSourceCorrectTransitionFactorLow
    {State : Type*} [Countable State]
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (candidateRatio escapeCost q : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : candidateRatio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          candidateRatio)
    (escape : BoundaryEscapeFutureFactorCertificate State
      (conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
        t m k cutoff stage previous band window candidateRatio
        hstageMeasurable hpreviousMeasurable hstage hratio
        coordinateData).someCandidate
      next escapeCost)
    (cost_le : (candidateBudget48 m band.beta : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      Point State previous next q := by
  let family := conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
    t m k cutoff stage previous band window candidateRatio hstageMeasurable
      hpreviousMeasurable hstage hratio coordinateData
  exact .low (candidateBudget48 m band.beta) candidateRatio escapeCost
    { candidate := family, escape := escape }
    (by
      exact MeasurableSet.iUnion fun h ↦
        MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun _hx ↦
          (measurableSet_typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) hstageMeasurable
            hpreviousMeasurable band h).inter
          (measurableSet_typedStoppedCandidateNear
            m cutoff band window h x))
    cost_le

/-- Atomwise strong-Markov constructor consumed by the source-correct upper
assembly.  The future escape certificate remains separate from the checked
conditional stopped-history coordinate law. -/
noncomputable def conditionalCandidateBudgetTypedSourceCorrectTransitionFactorLowAtomwise
    {Index : Type} {State : Type*} [Countable Index] [Countable State]
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (candidateRatio escapeCost q : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : candidateRatio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      (conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
        t m k cutoff stage previous band window candidateRatio
        hstageMeasurable hpreviousMeasurable hstage hratio
        coordinateData).someCandidate
      next escapeCost)
    (cost_le : (candidateBudget48 m band.beta : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      Point State previous next q := by
  let family := conditionalCandidateBudgetTypedStoppedHistoryCandidateFamily
    t m k cutoff stage previous band window candidateRatio hstageMeasurable
      hpreviousMeasurable hstage hratio coordinateData
  exact .lowAtomwise (candidateBudget48 m band.beta) candidateRatio escapeCost
    { candidate := family, escape := escape } cost_le

end

end Erdos1165.HLOZTypedStoppedCandidateConditionalProduct
