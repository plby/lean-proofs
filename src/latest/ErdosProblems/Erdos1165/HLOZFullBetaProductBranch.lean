/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFullBetaRegimeSplit
import ErdosProblems.Erdos1165.HLOZTilingEndpointGapClosure

/-!
# Proposition 4.8 branch of the full beta gap screen

This is the measure-level endpoint screen for the exact source event whose
selected adjacent beta strip has upper exponent at most `7 / 10`.
-/

open MeasureTheory Set
open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZFullBetaProductBranch

open HLOZFullBetaRegimeSplit HLOZGapRandomClockScreen HLOZPathEvents
open HLOZGapRandomClockNumerics
open HLOZProposition48Candidates HLOZTilingEndpointBandExtraction
open HLOZTilingEndpointGapClosure HLOZTilingGapRandomClockScreen
open HLOZTilingEndpointBandSelector

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Fully selected source-low screen.  No failed-pair or beta-band selection
premise remains. -/
theorem measure_onTimeProductBetaLowGapExceptionalEvent_le_endpointScreen
    (t : DominoTiling) (m cap externalThreshold : ℕ)
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤ m + 1) :
    simpleRandomWalk
        (onTimeProductBetaLowGapExceptionalEvent t m) ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m
              (levelCutoffTime upperTailDelta m)
              (sourceProductEndpointBands m cap externalThreshold)) +
          ∑ band ∈ sourceProductEndpointBands m cap externalThreshold,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  exact measure_gapEvent_le_tilingLazyRandomClockScreen_on_valid t
    (onTimeProductBetaLowGapExceptionalEvent t m) m
    (levelCutoffTime upperTailDelta m) cap
    (sourceProductEndpointBands m cap externalThreshold)
    (tilingLazyGoodEndpointExtraction_onTimeProductBeta
      hm hthreshold hcapacity)

/-- The geometric-return contribution of all source-low endpoint bands is
closed numerically, uniformly in the level-dependent lazy and external
thresholds. -/
theorem eventually_sourceProductEndpoint_geometric_sum_le
    (cap externalThreshold : ℕ → ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost
            (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
            band.returns ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  exact eventually_randomClockBand_geometric_sum_le_of_dynamic_bounds
    (fun m ↦ sourceProductEndpointBands m (cap m) (externalThreshold m))
    canonicalEndpointBandIndex canonicalEndpointLowGapTemplates
    (Nat.card CanonicalEndpointLowGapBandTag) hc
    (fun p hp ↦ canonicalEndpointLowGapTemplate_scale hp)
    (fun m band hband ↦ sourceProductEndpointBand_projects hband)
    (fun m ↦ sourceProductEndpointBands_card_le
      m (cap m) (externalThreshold m))
    (fun m band hband ↦ sourceProductEndpointBand_betaUpper hband)
    (fun m band hband ↦ sourceProductEndpointBand_returns hband)

end

end Erdos1165.HLOZFullBetaProductBranch
