/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFullBetaRegimeSplit
import ErdosProblems.Erdos1165.HLOZThetaSourceBalance

/-!
# Candidate-local full-beta product extraction

The legacy full-beta endpoint extraction removes a global stopped-lazy
overflow event.  The source proof needs no such global predicate: for the
single failed-pair endpoint selected by the beta decomposition, the oriented
`V₂`/Theta-good source gives the required external local-time lower bound.

This module isolates that no-lazy deterministic seam.  Its good event records
only the literal endpoint lower bound for the selected failed pair.  A later
source/transport theorem routes the complement to the oriented Theta and
checker payments.  No event-probability estimate occurs here.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZNoLazyFullBetaProductBranch

open HLOZFullBetaRegimeSplit HLOZGapBetaArithmetic
open HLOZGapEstimate HLOZGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates HLOZTilingEndpointBandExtraction
open HLOZTilingEndpointBandSelector HLOZTilingGapRandomClockScreen
open HLOZTilingGapBandExtraction
open HLOZThetaSourceBalance
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber
open TilingExternalPhaseSplit TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A selected source-low failed pair whose new endpoint already has the
literal endpoint-chain local time needed by its random-clock band. -/
def CandidateLocalProductBetaWitness
    {t : DominoTiling} {m : ℕ} {s : WalkPath}
    (externalThreshold : ℕ)
    (p : LowGapFailedPair t m (levelCutoffTime upperTailDelta m) s)
    (j : ℕ) : Prop :=
  FullFailedPairBetaBand p j ∧
    deficitExponent48 (meshExponent p.scale) (j + 1) ≤ (7 / 10 : ℝ) ∧
    externalThreshold ≤
      pathPhasedExternalLocalTime t (compatibleOrientation (s p.nNew))
        s p.nOld (s p.nNew)

/-- The no-lazy product branch.  Valid support is included explicitly
because the endpoint-phase identification is a deterministic statement on
nearest-neighbor paths. -/
def onTimeCandidateLocalProductBetaLowGapExceptionalEvent
    (t : DominoTiling) (m externalThreshold : ℕ) : Set WalkPath :=
  onTimeLowGapDeficitExceptionalEvent t m ∩ validStepWalk ∩
    {s | ∃ (p : LowGapFailedPair t m
        (levelCutoffTime upperTailDelta m) s) (j : ℕ),
      CandidateLocalProductBetaWitness externalThreshold p j}

theorem onTimeCandidateLocalProductBeta_subset_productBeta
    (t : DominoTiling) (m externalThreshold : ℕ) :
    onTimeCandidateLocalProductBetaLowGapExceptionalEvent
        t m externalThreshold ⊆
      onTimeProductBetaLowGapExceptionalEvent t m := by
  rintro s ⟨⟨hgap, _hvalid⟩, p, j, hfull, hbeta, _hexternal⟩
  exact ⟨hgap, p, j, hfull, hbeta⟩

theorem onTimeCandidateLocalProductBeta_subset_valid
    (t : DominoTiling) (m externalThreshold : ℕ) :
    onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold ⊆ validStepWalk :=
  fun _ hs ↦ hs.1.2

/-- The exact valid product-beta paths for which no selected low-beta failed
pair supplies the displayed endpoint-chain threshold.  This is the sole
deterministic complement of the candidate-local extraction; it is not a
generic exceptional event or a probability assumption. -/
def onTimeProductBetaCandidateLocalComplementEvent
    (t : DominoTiling) (m externalThreshold : ℕ) : Set WalkPath :=
  (onTimeProductBetaLowGapExceptionalEvent t m ∩ validStepWalk) \
    onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold

/-- Exact no-lazy split of the full source-low product event.  Invalid paths
are null under simple random walk; the remaining two terms are respectively
the candidate-local screen and its literal low-external complement. -/
theorem onTimeProductBeta_subset_valid_compl_union_candidateLocal_union_complement
    (t : DominoTiling) (m externalThreshold : ℕ) :
    onTimeProductBetaLowGapExceptionalEvent t m ⊆
      validStepWalkᶜ ∪
        (onTimeCandidateLocalProductBetaLowGapExceptionalEvent
            t m externalThreshold ∪
          onTimeProductBetaCandidateLocalComplementEvent
            t m externalThreshold) := by
  intro s hs
  by_cases hvalid : s ∈ validStepWalk
  · by_cases hlocal : s ∈
        onTimeCandidateLocalProductBetaLowGapExceptionalEvent
          t m externalThreshold
    · exact Or.inr (Or.inl hlocal)
    · exact Or.inr (Or.inr ⟨⟨hs, hvalid⟩, hlocal⟩)
  · exact Or.inl hvalid

/-- Pathwise meaning of the named complement: every admissible low-beta
failed-pair witness has endpoint-chain local time strictly below the target
threshold.  This is the exact deterministic statement to be contradicted by
the oriented `V₂`/Theta-good candidate-local cap. -/
theorem mem_onTimeProductBetaCandidateLocalComplementEvent_iff
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath} :
    s ∈ onTimeProductBetaCandidateLocalComplementEvent
        t m externalThreshold ↔
      s ∈ onTimeProductBetaLowGapExceptionalEvent t m ∧
        s ∈ validStepWalk ∧
        ∀ (p : LowGapFailedPair t m
            (levelCutoffTime upperTailDelta m) s) (j : ℕ),
          FullFailedPairBetaBand p j →
          deficitExponent48 (meshExponent p.scale) (j + 1) ≤
              (7 / 10 : ℝ) →
          pathPhasedExternalLocalTime t
              (compatibleOrientation (s p.nNew)) s p.nOld (s p.nNew) <
            externalThreshold := by
  constructor
  · rintro ⟨⟨hproduct, hvalid⟩, hnotLocal⟩
    refine ⟨hproduct, hvalid, ?_⟩
    intro p j hfull hbeta
    by_contra hnotLt
    apply hnotLocal
    exact ⟨⟨hproduct.1, hvalid⟩, p, j, hfull, hbeta,
      Nat.le_of_not_gt hnotLt⟩
  · rintro ⟨hproduct, hvalid, hlow⟩
    refine ⟨⟨hproduct, hvalid⟩, ?_⟩
    rintro ⟨_hsame, p, j, hfull, hbeta, hexternal⟩
    exact (not_lt_of_ge hexternal) (hlow p j hfull hbeta)

/-! ## The three literal creation-source profiles -/

/-- Every candidate-local product path carries the exact rank-one creation,
no-next-level, and `D_eta` data.  This is extracted directly from the
terminal four-favorite configuration; no transition filter or lazy event is
used. -/
theorem onTimeCandidateLocalProductBeta_rankOne_creationSourceData
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    ∃ n, ThresholdCreation s m 1 n ∧
      thresholdCount s n (m + 1) = 0 ∧
      tilingDEtaAtCreation t m 1 (shellWidth48 m)
        (m - shellWidth48 m) s := by
  rcases hs.1.1.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, _hfailure⟩
  have htime : n₁ < n₄ :=
    creation_time_lt (by omega) (by omega) (by omega) h₁ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₁ : thresholdCount s n₁ (m + 1) = 0 := by
    change thresholdCount s n₁ (m + 1) ≤
      thresholdCount s n₄ (m + 1) at hmono
    omega
  refine ⟨n₁, h₁, hnext₁, ?_⟩
  exact tilingDEtaAtCreation_of_creation_of_dominoSeparated hm (by omega) rfl
    h₁ hnext₁ (thresholdDominoSeparated_of_singleton
      (thresholdSites_eq_singleton_at_first_creation h₁))

/-- Rank-two creation-source data on the same candidate-local event. -/
theorem onTimeCandidateLocalProductBeta_rankTwo_creationSourceData
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    ∃ n, ThresholdCreation s m 2 n ∧
      thresholdCount s n (m + 1) = 0 ∧
      tilingDEtaAtCreation t m 2 (shellWidth48 m)
        (m - shellWidth48 m) s := by
  rcases hs.1.1.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, _hfailure⟩
  have htime : n₂ < n₄ :=
    creation_time_lt (by omega) (by omega) (by omega) h₂ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₂ : thresholdCount s n₂ (m + 1) = 0 := by
    change thresholdCount s n₂ (m + 1) ≤
      thresholdCount s n₄ (m + 1) at hmono
    omega
  refine ⟨n₂, h₂, hnext₂, ?_⟩
  exact tilingDEtaAtCreation_of_creation_of_dominoSeparated hm (by omega) rfl
    h₂ hnext₂ (thresholdDominoSeparated_of_pair
      (thresholdSites_eq_pair_at_second_creation h₁ h₂) hsep.1)

/-- Rank-three creation-source data on the same candidate-local event. -/
theorem onTimeCandidateLocalProductBeta_rankThree_creationSourceData
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    ∃ n, ThresholdCreation s m 3 n ∧
      thresholdCount s n (m + 1) = 0 ∧
      tilingDEtaAtCreation t m 3 (shellWidth48 m)
        (m - shellWidth48 m) s := by
  rcases hs.1.1.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, _hfailure⟩
  have htime : n₃ < n₄ :=
    creation_time_lt (by omega) (by omega) (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₃ : thresholdCount s n₃ (m + 1) = 0 := by
    change thresholdCount s n₃ (m + 1) ≤
      thresholdCount s n₄ (m + 1) at hmono
    omega
  rcases hsep with ⟨h₁₂, h₁₃, _h₁₄, h₂₃, _h₂₄, _h₃₄⟩
  refine ⟨n₃, h₃, hnext₃, ?_⟩
  exact tilingDEtaAtCreation_of_creation_of_dominoSeparated hm (by omega) rfl
    h₃ hnext₃ (thresholdDominoSeparated_of_triple
      (thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃)
      h₁₂ h₁₃ h₂₃)

/-- Direct constructor for a candidate-local endpoint extraction.  Unlike
`tilingLazyGoodRandomClockExtraction_of_band_realization`, the selected path
event itself supplies the one endpoint lower bound; no all-sites lazy-good
predicate is introduced. -/
theorem tilingRandomClockExtraction_of_candidateLocal_band_realization
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cutoff : ℕ}
    {bands : Finset RandomClockBand}
    (hselect : ∀ s ∈ gapEvent,
      ∃ band ∈ bands, ∃ x : Point,
        RandomClockPairRealizes m cutoff s band x ∧
        x ∈ pathPhaseFilteredExternalVisitedSites t band.orientation
          band.vertexPhase s
            (pathTruncatedLevelTime m band.oldRank cutoff s) ∧
        band.externalThreshold ≤
          pathPhaseFilteredExternalLocalTime t band.orientation
            band.vertexPhase s
              (pathTruncatedLevelTime m band.oldRank cutoff s) x ∧
        (∀ y ∈ favoriteSites s
            (pathTruncatedLevelTime m band.oldRank cutoff s),
          x ≠ y ∧ ¬Tilings.sameDomino t x y) ∧
        deficitShellLabel
            (tilingRandomClockTotalLocalTime m cutoff band)
            m (shellWidth48 m) s x < shellCount48 m band.beta) :
    TilingRandomClockExtraction t gapEvent m cutoff bands := by
  intro s hs _hnoOverflow
  obtain ⟨band, hband, x, hrealizes, hvisited, hexternal,
      hsep, hshell⟩ := hselect s hs
  refine ⟨band, hband, x,
    mem_tilingRandomClockBandSites_of_lazy_cap hvisited hexternal
      hsep hshell, hrealizes⟩

/-- Candidate enumeration with the target restriction retained.  This is
the no-lazy measure split: the only exceptional term is the raw candidate
overflow on the actual candidate-local good event. -/
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

/-- Concrete source-low extraction from only the selected endpoint lower
bound.  The cap still labels the finite band family and supplies the scalar
margin in the beta arithmetic; it is never asserted at unrelated sites. -/
theorem tilingCandidateLocalEndpointExtraction_onTimeProductBeta
    {t : DominoTiling} {m cap externalThreshold : ℕ}
    (hm : 1 < m) (hthreshold : 0 < externalThreshold) :
    TilingRandomClockExtraction t
      (onTimeCandidateLocalProductBetaLowGapExceptionalEvent
        t m externalThreshold)
      m (levelCutoffTime upperTailDelta m)
      (sourceProductEndpointBands m cap externalThreshold) := by
  apply tilingRandomClockExtraction_of_candidateLocal_band_realization
  intro s hs
  obtain ⟨⟨_hgap, hvalid⟩, p, j, hfull, hbeta, hfullExternal⟩ := hs
  rcases hfull with ⟨hj, hband, hupper⟩
  have holdLe : p.oldRank ≤ 3 := by
    have hrankSucc := p.rank_succ
    have hnewLe := p.newRank_le_four
    omega
  let pair : Fin 3 := ⟨p.oldRank - 1, by omega⟩
  have hpairOld : (pair : ℕ) + 1 = p.oldRank := by
    have hpos := p.oldRank_pos
    dsimp only [pair]
    omega
  have hpairNew : (pair : ℕ) + 2 = p.newRank := by
    rw [p.rank_succ, ← hpairOld]
  let orientation := compatibleOrientation (s p.nNew)
  have hcompatible : OrientationCompatible orientation (s p.nNew) :=
    compatibleOrientation_compatible _
  have hendpoint : externalThreshold ≤
      pathPhaseFilteredExternalLocalTime t orientation false s p.nOld
        (s p.nNew) := by
    change externalThreshold ≤
      phasedExternalVertexLocalTime t orientation .endpoint
        (finitePathList (pathPrefix s p.nOld)) (s p.nNew)
    rw [← pathPhasedExternalLocalTime_eq_endpoint_of_compatible
      t orientation s p.nOld (s p.nNew) hvalid hcompatible]
    exact hfullExternal
  have hvisited : s p.nNew ∈
      pathPhaseFilteredExternalVisitedSites t orientation false s p.nOld := by
    change s p.nNew ∈ phasedExternalVertexVisitedSites t orientation .endpoint
      (finitePathList (pathPrefix s p.nOld))
    rw [phasedExternalVertexVisitedSites,
      mem_tilingExternalPhaseVisitedSites_iff]
    exact hthreshold.trans_le hendpoint
  have hj64 : j < betaBandCount :=
    index_lt_betaBandCount_of_betaNext_le_sevenTenths p.scale_low hbeta
  let index : Fin betaBandCount := ⟨j, hj64⟩
  let tag : CanonicalEndpointLowGapBandTag :=
    { pair := pair
      scale := p.scale
      orientation := boolOfOrientation orientation
      index := index }
  let band := canonicalEndpointLowGapBand m cap externalThreshold tag
  have hranks : band.oldRank = p.oldRank ∧ band.newRank = p.newRank := by
    simpa only [band, tag, canonicalEndpointLowGapBand] using
      And.intro hpairOld hpairNew
  have hbandScale : band.scale = p.scale := by
    simpa only [band, tag, canonicalEndpointLowGapBand] using
      endpointLowGapScale_eq_of_mem tag p.scale_low
  have hreturns : band.returns + 1 ≤ p.deficit := by
    have hmPos : 0 < m := by omega
    dsimp only [band, tag, canonicalEndpointLowGapBand, index]
    rw [requiredReturns48_add_one
      (Real.rpow_pos_of_pos (by exact_mod_cast hmPos) _)]
    exact hband.1
  have hrealizes := p.randomClockPairRealizes band hranks hbandScale hreturns
  have hcanonical : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold :=
    canonicalEndpointLowGapBand_mem m cap externalThreshold tag p.scale_low
  have hbandBeta : band.beta ≤ (7 / 10 : ℝ) := by
    simpa only [band, tag, canonicalEndpointLowGapBand,
      endpointLowGapScale_eq_of_mem tag p.scale_low, index] using hbeta
  refine ⟨band,
    mem_sourceProductEndpointBands_iff.mpr ⟨hcanonical, hbandBeta⟩,
    s p.nNew, hrealizes, ?_, ?_, ?_, ?_⟩
  · simpa only [band, tag, canonicalEndpointLowGapBand,
      orientationOfBool_boolOfOrientation, p.oldClock, hpairOld] using hvisited
  · simpa only [band, tag, canonicalEndpointLowGapBand,
      orientationOfBool_boolOfOrientation, p.oldClock, hpairOld] using hendpoint
  · simpa only [band, tag, canonicalEndpointLowGapBand,
      orientationOfBool_boolOfOrientation, p.oldClock, hpairOld] using p.separated
  · simpa only [band, tag, canonicalEndpointLowGapBand,
      tilingRandomClockTotalLocalTime,
      ScreeningInstantiation.deficitShellLabel, p.oldClock, hpairOld,
      LowGapFailedPair.deficit] using hband.2

/-- Measure-level candidate-local source-low screen.  There is no lazy
exceptional event: the geometric term and the raw overflow intersection are
the only two contributions. -/
theorem
    measure_onTimeCandidateLocalProductBetaLowGapExceptionalEvent_le_screen
    (t : DominoTiling) (m cap externalThreshold : ℕ)
    (hm : 1 < m) (hthreshold : 0 < externalThreshold) :
    simpleRandomWalk
        (onTimeCandidateLocalProductBetaLowGapExceptionalEvent
          t m externalThreshold) ≤
      simpleRandomWalk
          (onTimeCandidateLocalProductBetaLowGapExceptionalEvent
              t m externalThreshold ∩
            tilingRandomClockCandidateOverflow t m
              (levelCutoffTime upperTailDelta m)
              (sourceProductEndpointBands m cap externalThreshold)) +
        ∑ band ∈ sourceProductEndpointBands m cap externalThreshold,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := by
  exact measure_tilingRandomClockExtraction_le_inter
    (tilingCandidateLocalEndpointExtraction_onTimeProductBeta
      (t := t) (m := m) (cap := cap)
      (externalThreshold := externalThreshold) hm hthreshold)

end

end Erdos1165.HLOZNoLazyFullBetaProductBranch
