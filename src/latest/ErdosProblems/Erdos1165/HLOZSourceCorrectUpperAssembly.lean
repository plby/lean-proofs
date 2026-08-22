/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSourceCorrectFilteredTransitions
import ErdosProblems.Erdos1165.HLOZSourceCorrectFullGapClosure
import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture
import ErdosProblems.Erdos1165.Proposition13DirectTransferAssembly

/-!
# Unconditional source-correct HLOZ upper assembly

This is the public upper endpoint after replacing prefix-only transition
screens by the filtered future factors used in HLOZ (4.36)--(4.37).  Its
inputs are the direct Proposition 1.3 scale construction, the literal
valid-support lazy and source-correct shell product data for the full
`7 / 10` beta split, and stopped-history/strong-Markov certificates for the
three filtered future transitions.

All event-probability estimates are conclusions.  In particular the theorem
does not assume an exceptional-event series, a transition inequality, or a
`HasGapDeficitReturnHarnack` value.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZSourceCorrectUpperAssembly

open HLOZFilteredTransitionAssembly HLOZFullBetaRegimeSplit
open HLOZPathEvents HLOZSourceCorrectBandProductClosure
open HLOZSourceCorrectFilteredTransitions HLOZSourceCorrectFullGapClosure
open HLOZStoppedHistoryCandidateFuture HLOZValidStoppedLazyClosure
open Proposition13DirectTransferAssembly ScreeningInstantiation

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-- The source cutoff in Proposition 4.8. -/
def sourceCorrectCutoff (m : ℕ) : ℕ :=
  levelCutoffTime upperTailDelta m

/-- Opaque projection of the lazy cap, used to keep dependent transition
types small at the public endpoint. -/
def sourceCorrectCap {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c)
    (t : DominoTiling) : ℕ → ℕ :=
  (data t).cap

/-- Opaque projection of the source candidate threshold. -/
def sourceCorrectExternalThreshold {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c)
    (t : DominoTiling) : ℕ → ℕ :=
  (data t).externalThreshold

/-- Rank-one history filter selected by the literal full-beta data. -/
def sourceCorrectFirstBadHistory {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c) :
    BranchEvent := fun t m a ↦
  firstFactorBadHistory sourceCorrectCutoff (sourceCorrectCap data t)
    (sourceCorrectExternalThreshold data t) t m a

/-- Rank-two history filter selected by the literal full-beta data. -/
def sourceCorrectSecondBadHistory {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c) :
    BranchEvent := fun t m a ↦
  secondFactorBadHistory sourceCorrectCutoff (sourceCorrectCap data t)
    (sourceCorrectExternalThreshold data t) t m a

/-- Rank-three history filter selected by the literal full-beta data. -/
def sourceCorrectThirdBadHistory {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c) :
    BranchEvent := fun t m a ↦
  thirdFactorBadHistory sourceCorrectCutoff (sourceCorrectCap data t)
    (sourceCorrectExternalThreshold data t) t m a

/-- The branch-constant paid family.  Only valid-lazy and source endpoint
candidate overflows occur here; rank-local gap failures do not. -/
def sourceCorrectPaidAuxiliary {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c) :
    BranchEvent := fun t m _ ↦
  sourceCorrectAuxiliaryBadHistoryEvent t m (sourceCorrectCutoff m)
    (sourceCorrectCap data t m) (sourceCorrectExternalThreshold data t m)

/-! ## Summability derived from the literal product data -/

/-- The global valid-lazy/candidate auxiliary event is summable. -/
theorem simpleRandomWalk_sourceCorrectAuxiliaryBadHistoryEvent_series_ne_top
    {c : ℝ} (hc : 0 < c) (t : DominoTiling)
    (data : FullBetaSourceCorrectProductData t c) :
    ∑' m, simpleRandomWalk
      (sourceCorrectAuxiliaryBadHistoryEvent t m (sourceCorrectCutoff m)
        (data.cap m) (data.externalThreshold m)) ≠ ∞ := by
  have hlazyCost :=
    eventually_allSixValidStoppedLazyOverflowCost_le_exp data.lazy (2 * c)
  have hlazyBound : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (sourceCorrectLazyBadHistoryEvent t m (data.cap m)) ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    filter_upwards [hlazyCost, eventually_ge_atTop data.lazy.lawStart,
        eventually_gt_atTop (0 : ℕ)] with m hcost hstart hm
    exact (simpleRandomWalk_tilingLazyOverflowExceptionalEvent_le
      data.lazy hstart hm).trans hcost
  have hlazySeries : ∑' m, simpleRandomWalk
      (sourceCorrectLazyBadHistoryEvent t m (data.cap m)) ≠ ∞ :=
    HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
      simpleRandomWalk _ (by linarith : 0 < 2 * c) hlazyBound
  have hcandidates :=
    eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_sourceCorrectData
      t sourceCorrectCutoff
      (fun m ↦ sourceProductEndpointBands m (data.cap m)
        (data.externalThreshold m))
      (fun m band hband ↦ sourceProductEndpointBand_betaLower hband)
      data.bands data.band_law_start
  have hcandidateBound : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (sourceCorrectCandidateBadHistoryEvent t m (sourceCorrectCutoff m)
            (data.cap m) (data.externalThreshold m)) ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    filter_upwards [hcandidates, data.coefficient_tail] with m hcandidate htail
    exact hcandidate.trans htail
  have hcandidateSeries : ∑' m, simpleRandomWalk
      (sourceCorrectCandidateBadHistoryEvent t m (sourceCorrectCutoff m)
        (data.cap m) (data.externalThreshold m)) ≠ ∞ :=
    HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
      simpleRandomWalk _ (by linarith : 0 < 2 * c) hcandidateBound
  have hmajor : ∑' m,
      (simpleRandomWalk
          (sourceCorrectLazyBadHistoryEvent t m (data.cap m)) +
        simpleRandomWalk
          (sourceCorrectCandidateBadHistoryEvent t m (sourceCorrectCutoff m)
            (data.cap m) (data.externalThreshold m))) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hlazySeries, hcandidateSeries⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  exact measure_union_le _ _

/-- Repeating the same paid auxiliary event over the finite gap mesh does
not change summability. -/
theorem simpleRandomWalk_paidTransitionBadHistoryEvent_series_ne_top
    {c : ℝ} (hc : 0 < c)
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (paidTransitionBadHistoryEvent (sourceCorrectPaidAuxiliary data) t m) ≠
        ∞ := by
  have haux :=
    simpleRandomWalk_sourceCorrectAuxiliaryBadHistoryEvent_series_ne_top
      hc t (data t)
  apply ne_top_of_le_ne_top haux
  apply ENNReal.tsum_le_tsum
  intro m
  apply measure_mono
  intro s hs
  change s ∈ UpperAssembly.meshBranchUnion properGapMesh
    (sourceCorrectPaidAuxiliary data t m) at hs
  rw [UpperAssembly.mem_meshBranchUnion] at hs
  rcases hs with ⟨a, _ha, hs⟩
  exact hs

/-! ## Terminal routing -/

/-- On a terminal branch, every rejected history has already entered the
low-gap exceptional event or the globally paid valid-lazy/candidate event. -/
theorem sourceCorrect_terminalFilteredBadHistoryRouting
    {c : ℝ}
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c) :
    TerminalFilteredBadHistoryRouting
      (sourceCorrectFirstBadHistory data)
      (sourceCorrectSecondBadHistory data)
      (sourceCorrectThirdBadHistory data)
      (sourceCorrectPaidAuxiliary data) := by
  intro t m a _ha s hs
  have hcover :=
    thirdTransitionEvent_subset_exceptional_union_auxiliary_union_filtered
      sourceCorrectCutoff (sourceCorrectCap data t)
      (sourceCorrectExternalThreshold data t) t m a hs.1.1
  rcases hcover with (he | haux) | hfiltered
  · exact Or.inl he
  · exact Or.inr haux
  · exfalso
    exact hfiltered.2 hs.2

/-! ## Public upper endpoint -/

/-- Upper composition from literal source-correct data and already assembled
filtered branch certificate packages.

The `factors` argument consists only of stopped-history coordinate families,
future escape-before-return containments, and their numerical costs.  The
three transition probability inequalities, both exceptional series, and the
gap-Harnack interface are all derived in this theorem. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_filteredFactorPackages
    (K : ℝ≥0) {c : ℝ} (hc : 0 < c)
    (hdirect : HasDirectAnnularScaleData)
    (data : ∀ t : DominoTiling, FullBetaSourceCorrectProductData t c)
    {History Candidate State : Type*}
    [hHistory : Countable History] [hState : Countable State]
    (factors : ∀ t m a,
      FilteredBranchTransitionFactorPackage History Candidate State
        sourceCorrectCutoff (sourceCorrectCap data t)
        (sourceCorrectExternalThreshold data t) K t m a) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk :=
    hasPlanarMaximumLowerDeviation_of_directData hdirect
  have hgap : HLOZUpperEstimates.HasGapDeficitReturnHarnack c :=
    hasGapDeficitReturnHarnack_of_fullBetaSourceCorrectData hc data
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_sourceCorrect_filtered_estimates
      K (sourceCorrectFirstBadHistory data)
      (sourceCorrectSecondBadHistory data)
      (sourceCorrectThirdBadHistory data)
      (sourceCorrectPaidAuxiliary data)
      (sourceCorrect_terminalFilteredBadHistoryRouting data)
  · intro t m a ha
    change simpleRandomWalk
        (filteredFirstTransitionEvent sourceCorrectCutoff
          (sourceCorrectCap data t)
          (sourceCorrectExternalThreshold data t) t m a) ≤
      UpperCanonical.hlozTransitionCost K m
    let package := factors t m a
    have h := package.measure_estimates
    exact h.1
  · intro t m a ha
    change simpleRandomWalk
        (filteredSecondTransitionEvent sourceCorrectCutoff
          (sourceCorrectCap data t)
          (sourceCorrectExternalThreshold data t) t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk
          (filteredFirstTransitionEvent sourceCorrectCutoff
            (sourceCorrectCap data t)
            (sourceCorrectExternalThreshold data t) t m a)
    let package := factors t m a
    have h := package.measure_estimates
    exact h.2.1
  · intro t m a ha
    change simpleRandomWalk
        (filteredThirdTransitionEvent sourceCorrectCutoff
          (sourceCorrectCap data t)
          (sourceCorrectExternalThreshold data t) t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk
          (filteredSecondTransitionEvent sourceCorrectCutoff
            (sourceCorrectCap data t)
            (sourceCorrectExternalThreshold data t) t m a)
    let package := factors t m a
    have h := package.measure_estimates
    exact h.2.2
  · intro t
    exact HLOZUpperEstimates.simpleRandomWalk_hlozExceptional_series_ne_top
      hProp13 hc hgap t
  · exact simpleRandomWalk_paidTransitionBadHistoryEvent_series_ne_top hc data

end

end Erdos1165.HLOZSourceCorrectUpperAssembly
