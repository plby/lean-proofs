/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZLargeDeficitSpatialScreen
import ErdosProblems.Erdos1165.HLOZNoLazyFullBetaProductBranch

/-!
# Direct full-beta exceptional series assembly

This module is the carrier-independent analytic endpoint for the no-lazy
product proof.  It combines a source-low product-beta series with the already
closed source-high spatial-beta series and then adds the standard late-clock
and mesh-overflow payments.  The eventual literal FullGap theorem constructs
the product-beta series internally before invoking this adapter; no
`HasGapDeficitReturnHarnack` premise is used here.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZNoLazyFullBetaDirectSeries

open HLOZFullBetaRegimeSplit HLOZLargeDeficitSpatialScreen
open HLOZNoLazyFullBetaProductBranch
open HLOZPathEvents HLOZUpperEstimates
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The two levels below the exact beta-regime decomposition.  This event is
eventually empty and makes the direct series comparison unconditional in
`m`. -/
def fullBetaSmallLevelEvent (m : ℕ) : Set WalkPath :=
  if 1 < m then ∅ else Set.univ

theorem eventually_fullBetaSmallLevelEvent_eq_empty :
    ∀ᶠ m : ℕ in atTop, fullBetaSmallLevelEvent m = ∅ := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  rw [fullBetaSmallLevelEvent, if_pos (by omega)]

theorem simpleRandomWalk_fullBetaSmallLevelEvent_series_ne_top :
    ∑' m, simpleRandomWalk (fullBetaSmallLevelEvent m) ≠ ∞ := by
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk
    fullBetaSmallLevelEvent (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_fullBetaSmallLevelEvent_eq_empty] with m hm
  rw [hm]
  simp

/-- Pointwise majorant for the entire on-time low-gap family: a finite
prefix and the two exact beta regimes. -/
def fullBetaDirectLowGapMajorant (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  fullBetaSmallLevelEvent m ∪
    (onTimeProductBetaLowGapExceptionalEvent t m ∪
      onTimeSpatialBetaLowGapExceptionalEvent t m)

theorem onTimeLowGap_subset_fullBetaDirectLowGapMajorant
    (t : DominoTiling) (m : ℕ) :
    onTimeLowGapDeficitExceptionalEvent t m ⊆
      fullBetaDirectLowGapMajorant t m := by
  intro s hs
  by_cases hm : 1 < m
  · exact Or.inr
      (onTimeLowGap_subset_productBeta_union_spatialBeta t hm hs)
  · apply Or.inl
    simp [fullBetaSmallLevelEvent, hm]

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

private theorem simpleRandomWalk_validStepWalk_compl_series_ne_top :
    ∑' _m : ℕ, simpleRandomWalk validStepWalkᶜ ≠ ∞ := by
  simp only [HLOZLazyOverflowClosure.simpleRandomWalk_validStepWalk_compl]
  simp

/-- The full product-beta family is summable from the two exact no-lazy
pieces: the candidate-local product screen and its named valid low-external
complement.  The remaining invalid-walk term has zero simple-random-walk
mass. -/
theorem simpleRandomWalk_onTimeProductBetaLowGapExceptional_series_ne_top_of_candidateLocal
    (t : DominoTiling) (externalThreshold : ℕ → ℕ)
    (hcandidate : ∑' m, simpleRandomWalk
      (onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
        (externalThreshold m)) ≠ ∞)
    (hcomplement : ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m
        (externalThreshold m)) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (onTimeProductBetaLowGapExceptionalEvent t m) ≠ ∞ := by
  have hmajor := measure_union_series_ne_top
    simpleRandomWalk_validStepWalk_compl_series_ne_top
    (measure_union_series_ne_top hcandidate hcomplement)
  exact ne_top_of_le_ne_top hmajor <|
    ENNReal.tsum_le_tsum fun m ↦ measure_mono
      (onTimeProductBeta_subset_valid_compl_union_candidateLocal_union_complement
        t m (externalThreshold m))

/-- The full direct low-gap majorant is summable once the literal source-low
product construction supplies its series.  The spatial branch has no data
or probability premise. -/
theorem simpleRandomWalk_fullBetaDirectLowGapMajorant_series_ne_top
    (t : DominoTiling)
    (hproduct : ∑' m, simpleRandomWalk
      (onTimeProductBetaLowGapExceptionalEvent t m) ≠ ∞) :
    ∑' m, simpleRandomWalk (fullBetaDirectLowGapMajorant t m) ≠ ∞ := by
  exact measure_union_series_ne_top
    simpleRandomWalk_fullBetaSmallLevelEvent_series_ne_top
    (measure_union_series_ne_top hproduct
      (simpleRandomWalk_onTimeSpatialBetaLowGapExceptionalEvent_series_ne_top
        t))

/-- Direct summability of the raw on-time low-gap event, avoiding the
intermediate Harnack package. -/
theorem simpleRandomWalk_onTimeLowGapDeficitExceptional_series_ne_top_of_product
    (t : DominoTiling)
    (hproduct : ∑' m, simpleRandomWalk
      (onTimeProductBetaLowGapExceptionalEvent t m) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (onTimeLowGapDeficitExceptionalEvent t m) ≠ ∞ := by
  have hmajor :=
    simpleRandomWalk_fullBetaDirectLowGapMajorant_series_ne_top t hproduct
  exact ne_top_of_le_ne_top hmajor <|
    ENNReal.tsum_le_tsum fun m ↦
      measure_mono (onTimeLowGap_subset_fullBetaDirectLowGapMajorant t m)

/-- Direct HLOZ exceptional-series endpoint.  In the final upper assembly,
`hproduct` is produced from literal static-source fibres, cofinal positive
interfaces, and the concrete Theta/transport payments before this theorem is
called. -/
theorem simpleRandomWalk_hlozExceptional_series_ne_top_of_product
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (t : DominoTiling)
    (hproduct : ∑' m, simpleRandomWalk
      (onTimeProductBetaLowGapExceptionalEvent t m) ≠ ∞) :
    ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞ := by
  have hlate := simpleRandomWalk_lateLevel_series_ne_top hProp13
  have hoverflow := simpleRandomWalk_meshOverflow_series_ne_top hProp13 t
  have hlow :=
    simpleRandomWalk_onTimeLowGapDeficitExceptional_series_ne_top_of_product
      t hproduct
  have hmajor : ∑' m,
      ((simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
        simpleRandomWalk (meshOverflowEvent t m)) +
        simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m)) ≠ ∞ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hlate, hoverflow⟩, hlow⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  calc
    simpleRandomWalk (hlozExceptionalEvent t m) ≤
        simpleRandomWalk
            (lateLevelSet upperTailDelta m 4 ∪ meshOverflowEvent t m) +
          simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) :=
      measure_union_le _ _
    _ ≤ (simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
          simpleRandomWalk (meshOverflowEvent t m)) +
        simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) := by
      gcongr
      exact measure_union_le _ _

/-- Concrete no-lazy direct endpoint.  A source construction need only close
the candidate-local screen and its explicitly named low-external complement;
the product-beta, spatial-beta, late-clock, and mesh terms are assembled
internally. -/
theorem simpleRandomWalk_hlozExceptional_series_ne_top_of_candidateLocal
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (t : DominoTiling) (externalThreshold : ℕ → ℕ)
    (hcandidate : ∑' m, simpleRandomWalk
      (onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
        (externalThreshold m)) ≠ ∞)
    (hcomplement : ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m
        (externalThreshold m)) ≠ ∞) :
    ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞ :=
  simpleRandomWalk_hlozExceptional_series_ne_top_of_product hProp13 t
    (simpleRandomWalk_onTimeProductBetaLowGapExceptional_series_ne_top_of_candidateLocal
      t externalThreshold hcandidate hcomplement)

end

end Erdos1165.HLOZNoLazyFullBetaDirectSeries
