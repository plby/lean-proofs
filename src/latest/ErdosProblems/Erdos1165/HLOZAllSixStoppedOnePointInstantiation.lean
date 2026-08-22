/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingStoppedWeightedOnePoint
import ErdosProblems.Erdos1165.HLOZAllSixExactCoordinateProductClosure

/-!
# Canonical stopped endpoint one-point input for all-six product screening

The state-dependent endpoint thinning theorem supplies the final external
one-point field of `TilingStoppedExternalOnePointData`.  This file inserts
that theorem into the exact-coordinate all-six candidate-overflow bound.
-/

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZAllSixStoppedOnePointInstantiation

open HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure
open HLOZGapRandomClockScreen HLOZLowScaleCandidateOverflow
open HLOZGapEstimate
open HLOZProposition48Candidates ScreeningInstantiation
open TilingLazyDecomposition TilingStoppedWeightedOnePoint
open HLOZTilingGapRandomClockScreen

noncomputable section

/-- At every sufficiently large level, the checked stopped endpoint-chain
estimate constructs the precise external one-point datum required by the
all-six product screen. -/
theorem eventually_tilingStoppedExternalOnePointData
    (t : DominoTiling) :
    ∀ᶠ m : ℕ in atTop, ∀ (cutoff : ℕ) (band : RandomClockBand),
      cutoff ≤ ExternalProposition44.hlozCutoff44 m →
      band.vertexPhase = false →
      ExternalProposition44.hlozOnePointLevel44 m + 1 ≤
        band.externalThreshold →
      TilingStoppedExternalOnePointData t m cutoff band := by
  filter_upwards
    [eventually_simpleRandomWalk_tilingRandomClockEndpoint_weightedOneSite44 t]
      with m hweighted
  intro cutoff band hcutoff hphase hthreshold
  exact {
    cutoff_le := hcutoff
    threshold_margin := hthreshold
    weighted := hweighted cutoff band hcutoff hphase hthreshold }

/-- Per-band candidate overflow with no external one-point premise and with
literal exact coordinate probabilities.  Only endpoint bands are used,
as required by the state-dependent thinning theorem. -/
theorem eventually_simpleRandomWalk_tilingRandomClockBandOverflow_le_of_exactProductData
    (t : DominoTiling) :
    ∀ᶠ m : ℕ in atTop, ∀ (cutoff : ℕ) (band : RandomClockBand),
      cutoff ≤ ExternalProposition44.hlozCutoff44 m →
      band.vertexPhase = false →
      ExternalProposition44.hlozOnePointLevel44 m + 1 ≤
        band.externalThreshold →
      kappaOne ≤ band.beta →
      ∀ data : AllSixExactCoordinateBandProductData t m cutoff band,
        data.lawStart ≤ m →
        simpleRandomWalk
            {s | candidateBudget48 m band.beta <
              (tilingRandomClockBandSites t m cutoff s band).card} ≤
          allSixBandOverflowCoefficient
            (HLOZAllSixFactoredProductClosure.allSixBandProductDataOfFactoredData
              (allSixFactoredBandProductDataOfExactCoordinateData data)) := by
  filter_upwards [eventually_tilingStoppedExternalOnePointData t,
      eventually_candidateBudgetArithmeticAt, eventually_gt_atTop (0 : ℕ)] with
      m hone hbudget hm
  intro cutoff band hcutoff hphase hthreshold hbeta data hstart
  rw [allSixBandOverflowCoefficient, dif_pos ⟨hstart, hm⟩]
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_exactCoordinateProductData
    hbudget hbeta (hone cutoff band hcutoff hphase hthreshold) data hstart hm

/-- Finite-band Proposition 4.8 overflow with both the stopped external
one-point input and the literal coordinate normalization discharged. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_exactProductData
    (t : DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hcutoff : ∀ᶠ m : ℕ in atTop,
      cutoff m ≤ ExternalProposition44.hlozCutoff44 m)
    (hphase : ∀ m band, band ∈ bands m → band.vertexPhase = false)
    (hthreshold : ∀ᶠ m : ℕ in atTop, ∀ band ∈ bands m,
      ExternalProposition44.hlozOnePointLevel44 m + 1 ≤
        band.externalThreshold)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band,
      AllSixExactCoordinateBandProductData t m (cutoff m) band)
    (hstart : ∀ᶠ m : ℕ in atTop, ∀ band ∈ bands m,
      (data m band).lawStart ≤ m) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          allSixBandOverflowCoefficient
            (HLOZAllSixFactoredProductClosure.allSixBandProductDataOfFactoredData
              (allSixFactoredBandProductDataOfExactCoordinateData
                (data m band))) := by
  filter_upwards [eventually_tilingStoppedExternalOnePointData t,
      eventually_candidateBudgetArithmeticAt, hcutoff, hthreshold, hstart,
      eventually_gt_atTop (0 : ℕ)] with
      m hone hbudget hcutoffM hthresholdM hstartM hm
  unfold tilingRandomClockCandidateOverflow candidateOverflow
  refine (Screening.measure_someCandidateBad_le_sum simpleRandomWalk
    (bands m) (fun band ↦
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m (cutoff m) s band).card})).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  rw [allSixBandOverflowCoefficient,
    dif_pos ⟨hstartM band hband, hm⟩]
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_exactCoordinateProductData
    hbudget (hbeta m band hband)
      (hone (cutoff m) band hcutoffM (hphase m band hband)
        (hthresholdM band hband))
      (data m band) (hstartM band hband) hm

end

end Erdos1165.HLOZAllSixStoppedOnePointInstantiation
