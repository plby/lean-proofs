/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFullBetaProductBranch

/-!
# Source-filtered endpoint extraction

The ordinary endpoint screen enlarges the candidate overflow to the whole
path space.  The shell-zero replacement is valid only on the actual staged
source.  These variants retain the intersection with the lazy-good target
event, so a downstream deterministic routing theorem can split it into the
literal shell-zero source and the appropriate balance complement.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZFilteredFullBetaProductBranch

open HLOZFullBetaProductBranch HLOZFullBetaRegimeSplit
open HLOZGapEstimate HLOZGapRandomClockScreen HLOZLazyOverflowClosure
open HLOZPathEvents
open HLOZProposition48Candidates HLOZTilingEndpointBandExtraction
open HLOZTilingEndpointGapClosure HLOZTilingGapRandomClockScreen
open TilingVariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Candidate enumeration with the overflow kept inside the target event. -/
theorem measure_tilingRandomClockExtraction_le_inter
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cutoff : ℕ}
    {bands : Finset RandomClockBand}
    (hextract : TilingRandomClockExtraction t gapEvent m cutoff bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk
          (gapEvent ∩
            tilingRandomClockCandidateOverflow t m cutoff bands) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := by
  let sites := tilingRandomClockBandSites t m cutoff
  let budget : RandomClockBand → ℕ := fun band ↦
    candidateBudget48 m band.beta
  let realizes := RandomClockPairRealizes m cutoff
  let overflow := candidateOverflow bands sites budget
  let screened := gapEvent \ overflow
  have hsplit : gapEvent ⊆ (gapEvent ∩ overflow) ∪ screened := by
    intro s hs
    by_cases hoverflow : s ∈ overflow
    · exact Or.inl ⟨hs, hoverflow⟩
    · exact Or.inr ⟨hs, hoverflow⟩
  calc
    simpleRandomWalk gapEvent ≤
        simpleRandomWalk ((gapEvent ∩ overflow) ∪ screened) :=
      measure_mono hsplit
    _ ≤ simpleRandomWalk (gapEvent ∩ overflow) +
        simpleRandomWalk screened := measure_union_le _ _
    _ ≤ simpleRandomWalk (gapEvent ∩ overflow) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
            band.returns := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget
        (fun band ↦ HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
        RandomClockBand.returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            gapEvent bands sites budget realizes hextract)
        (range_candidateCountBound bands budget)
        (by
          intro band _hband slot _hslot
          exact measure_tilingRandomClockBandSlotSuccess_le_geometric
            (tilingRandomClockCandidateMeasurability_closed t m cutoff)
              band slot)
    _ = simpleRandomWalk
          (gapEvent ∩
            tilingRandomClockCandidateOverflow t m cutoff bands) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := rfl

/-- Lazy split without discarding the target restriction on the candidate
overflow. -/
theorem measure_gapEvent_le_tilingLazyRandomClockFilteredScreen
    (t : DominoTiling) (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : TilingLazyGoodRandomClockExtraction
      t gapEvent m cutoff cap bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingLazyGoodPart t gapEvent m cap ∩
              tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  have hsplit : gapEvent ⊆
      tilingLazyOverflowExceptionalEvent t m cap ∪
        tilingLazyGoodPart t gapEvent m cap := by
    intro s hs
    by_cases hoverflow : s ∈ tilingLazyOverflowExceptionalEvent t m cap
    · exact Or.inl hoverflow
    · exact Or.inr ⟨hs, hoverflow⟩
  calc
    simpleRandomWalk gapEvent ≤
        simpleRandomWalk
          (tilingLazyOverflowExceptionalEvent t m cap ∪
            tilingLazyGoodPart t gapEvent m cap) := measure_mono hsplit
    _ ≤ simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
          simpleRandomWalk (tilingLazyGoodPart t gapEvent m cap) :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingLazyGoodPart t gapEvent m cap ∩
              tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
      gcongr
      exact measure_tilingRandomClockExtraction_le_inter hextract

/-- Endpoint-only version on the measure-one nearest-neighbor support. -/
theorem measure_gapEvent_le_tilingLazyRandomClockFilteredScreen_on_valid
    (t : DominoTiling) (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : TilingLazyGoodRandomClockExtraction t
      (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
        m cutoff cap bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingLazyGoodPart t
                (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
                m cap ∩
              tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  have hsupport : gapEvent ⊆
      (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) ∪
        VariableStoppedTracePartition.validStepWalkᶜ := by
    intro s hs
    by_cases hvalid : s ∈ VariableStoppedTracePartition.validStepWalk
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
            (tilingLazyGoodPart t
                (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
                m cap ∩
              tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) :=
      measure_gapEvent_le_tilingLazyRandomClockFilteredScreen t
        (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
          m cutoff cap bands hextract

/-- Concrete source-low endpoint screen with the candidate event kept on
the actual lazy-good low-gap stage. -/
theorem measure_onTimeProductBetaLowGapExceptionalEvent_le_filteredEndpointScreen
    (t : DominoTiling) (m cap externalThreshold : ℕ)
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤ m + 1) :
    simpleRandomWalk (onTimeProductBetaLowGapExceptionalEvent t m) ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingLazyGoodPart t
                (onTimeProductBetaLowGapExceptionalEvent t m ∩
                  VariableStoppedTracePartition.validStepWalk)
                m cap ∩
              tilingRandomClockCandidateOverflow t m
                (levelCutoffTime upperTailDelta m)
                (sourceProductEndpointBands m cap externalThreshold)) +
          ∑ band ∈ sourceProductEndpointBands m cap externalThreshold,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  exact measure_gapEvent_le_tilingLazyRandomClockFilteredScreen_on_valid t
    (onTimeProductBetaLowGapExceptionalEvent t m) m
    (levelCutoffTime upperTailDelta m) cap
    (sourceProductEndpointBands m cap externalThreshold)
    (tilingLazyGoodEndpointExtraction_onTimeProductBeta (t := t)
      hm hthreshold hcapacity)

end

end Erdos1165.HLOZFilteredFullBetaProductBranch
