/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingEndpointBandSelector
import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockClosure
import ErdosProblems.Erdos1165.HLOZLazyOverflowClosure

/-!
# Null-support closure of the endpoint-only all-six screen

The parity-to-endpoint argument is valid on `validStepWalk`.  This module
removes that restriction at measure level using its already proved null
complement, and supplies the supported analogue of the quantitative all-six
random-clock closure.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZTilingEndpointGapClosure

open HLOZGapBetaArithmetic HLOZGapBetaNumerics HLOZGapEstimate
open HLOZGapRandomClockNumerics HLOZGapRandomClockScreen
open HLOZLazyOverflowClosure HLOZPathEvents HLOZProposition48Candidates
open HLOZTilingEndpointBandExtraction HLOZTilingEndpointBandSelector
open HLOZTilingGapRandomClockClosure HLOZTilingGapRandomClockScreen
open TilingVariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The endpoint screen may be proved only on genuine nearest-neighbor paths;
the invalid complement contributes zero simple-random-walk mass. -/
theorem measure_gapEvent_le_tilingLazyRandomClockScreen_on_valid
    (t : DominoTiling) (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : TilingLazyGoodRandomClockExtraction t
      (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
      m cutoff cap bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  have hsupport : gapEvent ⊆
      (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) ∪
        VariableStoppedTracePartition.validStepWalkᶜ := by
    intro s hs
    by_cases hvalid :
        s ∈ VariableStoppedTracePartition.validStepWalk
    · exact Or.inl ⟨hs, hvalid⟩
    · exact Or.inr hvalid
  calc
    simpleRandomWalk gapEvent ≤
        simpleRandomWalk
          ((gapEvent ∩ VariableStoppedTracePartition.validStepWalk) ∪
            VariableStoppedTracePartition.validStepWalkᶜ) :=
      measure_mono hsupport
    _ ≤ simpleRandomWalk
          (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) +
        simpleRandomWalk VariableStoppedTracePartition.validStepWalkᶜ :=
      measure_union_le _ _
    _ = simpleRandomWalk
        (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) := by
      rw [simpleRandomWalk_validStepWalk_compl, add_zero]
    _ ≤ simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) :=
      measure_gapEvent_le_tilingLazyRandomClockScreen t
        (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
        m cutoff cap bands hextract

/-- Fully selected all-six screen for the corrected broad-window low-gap
event.  The only hypotheses are the numerical positivity and cap margins;
there is no pathwise band-selection premise. -/
theorem measure_onTimeBroadLowGapDeficitExceptionalEvent_le_endpointScreen
    (t : DominoTiling) (m cap externalThreshold : ℕ)
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ ScreeningInstantiation.alphaMax) ≤ m + 1) :
    simpleRandomWalk
        (onTimeBroadLowGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m
              (levelCutoffTime upperTailDelta m)
              (canonicalEndpointLowGapBands m cap externalThreshold)) +
          ∑ band ∈ canonicalEndpointLowGapBands m cap externalThreshold,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  exact measure_gapEvent_le_tilingLazyRandomClockScreen_on_valid t
    (onTimeBroadLowGapDeficitExceptionalEvent t m) m
    (levelCutoffTime upperTailDelta m) cap
    (canonicalEndpointLowGapBands m cap externalThreshold)
    (tilingLazyGoodEndpointExtraction_onTimeBroad
      hm hthreshold hcapacity)

/-- Quantitative all-six closure with endpoint extraction only on the
measure-one nearest-neighbor support. -/
theorem hasGapDeficitReturnHarnack_of_tilingLazyRandomClock_bounds_on_valid
    {c : ℝ} (hc : 0 < c)
    (cap : DominoTiling → ℕ → ℕ)
    (bands : DominoTiling → ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : DominoTiling → Finset (GapScale × ℕ))
    (B : DominoTiling → ℕ)
    (hextract : ∀ t m,
      TilingLazyGoodRandomClockExtraction t
        (onTimeLowGapDeficitExceptionalEvent t m ∩
          VariableStoppedTracePartition.validStepWalk) m
        (levelCutoffTime upperTailDelta m)
        (cap t m) (bands t m))
    (lazyCost candidateCost : DominoTiling → ℕ → ℝ≥0∞)
    (hlazy : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap t m)) ≤
        lazyCost t m)
    (hcandidate : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m
            (levelCutoffTime upperTailDelta m)
            (bands t m)) ≤ candidateCost t m)
    (hother : ∀ t, ∀ᶠ m : ℕ in atTop,
      lazyCost t m + candidateCost t m ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)))
    (hscale : ∀ t p, p ∈ templates t → p.1 ∈ lowGapMesh)
    (hprojects : ∀ t m band, band ∈ bands t m →
      (band.scale, index m band) ∈ templates t)
    (hcard : ∀ t m, (bands t m).card ≤ B t)
    (hbeta : ∀ t m band, band ∈ bands t m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index m band + 1))
    (hreturns : ∀ t m band, band ∈ bands t m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index m band)) ≤
        band.returns) :
    HLOZUpperEstimates.HasGapDeficitReturnHarnack c := by
  intro t
  have hreturn :=
    eventually_randomClockBand_geometric_sum_le_of_dynamic_bounds
      (bands t) index (templates t) (B t) (c := 2 * c) (by linarith)
      (hscale t) (hprojects t) (hcard t) (hbeta t) (hreturns t)
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg 2 hc
  filter_upwards [hlazy t, hcandidate t, hother t, hreturn, habsorb]
    with m hlazyM hcandidateM hotherM hreturnM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
  refine (measure_gapEvent_le_tilingLazyRandomClockScreen_on_valid t
    (onTimeLowGapDeficitExceptionalEvent t m) m
    (levelCutoffTime upperTailDelta m) (cap t m)
    (bands t m) (hextract t m)).trans ?_
  calc
    simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap t m)) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m
              (levelCutoffTime upperTailDelta m)
              (bands t m)) +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) ≤
      lazyCost t m +
        (candidateCost t m +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by gcongr
    _ = (lazyCost t m + candidateCost t m) +
        ∑ band ∈ bands t m,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := by ac_rfl
    _ ≤ q + q := add_le_add hotherM hreturnM
    _ = (2 : ℝ≥0∞) * q := (two_mul q).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

end

end Erdos1165.HLOZTilingEndpointGapClosure
