/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingEndpointBandSelector

/-!
# Source-correct full beta regime split for HLOZ Lemma 4.10

The paper does not split failed pairs at one fixed deficit cutoff.  It first
places the deficit in an adjacent beta strip, then uses Proposition 4.8 when
the upper strip exponent is at most `7 / 10`, and a deterministic spatial
enumeration when that exponent is larger.  This file defines those two exact
events on the complete 128-step beta mesh and proves that they cover the raw
on-time low-gap event.
-/

open Set

namespace Erdos1165.HLOZFullBetaRegimeSplit

open HLOZGapBetaArithmetic HLOZGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates HLOZTilingEndpointBandExtraction
open HLOZTilingEndpointBandSelector HLOZTilingGapBandExtraction
open HLOZTilingGapRandomClockScreen ScreeningInstantiation
open LazyDecomposition PreStoppingSpatialLaw SpatialInsertionFiber
open TilingExternalPhaseSplit TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Complete adjacent-strip data, including the upper threshold which is
logically stronger than the shell-label field retained by
`FailedPairBetaBand`. -/
def FullFailedPairBetaBand
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (j : ℕ) : Prop :=
  j < fullBetaBandCount ∧ FailedPairBetaBand p j ∧
    p.deficit < Nat.ceil ((m : ℝ) ^
      deficitExponent48 (meshExponent p.scale) (j + 1))

/-- Source low-beta branch: some failed pair lies in a full-mesh strip whose
upper exponent is still in the Proposition 4.8 range. -/
def onTimeProductBetaLowGapExceptionalEvent
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  onTimeLowGapDeficitExceptionalEvent t m ∩
    {s | ∃ (p : LowGapFailedPair t m
          (levelCutoffTime upperTailDelta m) s) (j : ℕ),
      FullFailedPairBetaBand p j ∧
        deficitExponent48 (meshExponent p.scale) (j + 1) ≤ (7 / 10 : ℝ)}

/-- Source high-beta branch: some failed pair lies in a full-mesh strip whose
upper exponent is beyond the Proposition 4.8 range. -/
def onTimeSpatialBetaLowGapExceptionalEvent
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  onTimeLowGapDeficitExceptionalEvent t m ∩
    {s | ∃ (p : LowGapFailedPair t m
          (levelCutoffTime upperTailDelta m) s) (j : ℕ),
      FullFailedPairBetaBand p j ∧
        (7 / 10 : ℝ) <
          deficitExponent48 (meshExponent p.scale) (j + 1)}

theorem onTimeProductBeta_subset_raw (t : DominoTiling) (m : ℕ) :
    onTimeProductBetaLowGapExceptionalEvent t m ⊆
      onTimeLowGapDeficitExceptionalEvent t m := fun _ hs ↦ hs.1

theorem onTimeSpatialBeta_subset_raw (t : DominoTiling) (m : ℕ) :
    onTimeSpatialBetaLowGapExceptionalEvent t m ⊆
      onTimeLowGapDeficitExceptionalEvent t m := fun _ hs ↦ hs.1

/-- Every raw failed path enters one of the source's two beta regimes. -/
theorem onTimeLowGap_subset_productBeta_union_spatialBeta
    (t : DominoTiling) {m : ℕ} (hm : 1 < m) :
    onTimeLowGapDeficitExceptionalEvent t m ⊆
      onTimeProductBetaLowGapExceptionalEvent t m ∪
        onTimeSpatialBetaLowGapExceptionalEvent t m := by
  intro s hs
  obtain ⟨p⟩ := nonempty_lowGapFailedPair_of_mem_onTime hs
  obtain ⟨j, hj, hband, hupper⟩ := exists_failedPairBetaBand_full p hm
  rcases le_or_gt
      (deficitExponent48 (meshExponent p.scale) (j + 1))
      (7 / 10 : ℝ) with hlow | hhigh
  · exact Or.inl ⟨hs, p, j, ⟨hj, hband, hupper⟩, hlow⟩
  · exact Or.inr ⟨hs, p, j, ⟨hj, hband, hupper⟩, hhigh⟩

/-- Exact union equality (the branches need not be disjoint because a path
may contain several failed pairs). -/
theorem onTimeLowGap_eq_productBeta_union_spatialBeta
    (t : DominoTiling) {m : ℕ} (hm : 1 < m) :
    onTimeLowGapDeficitExceptionalEvent t m =
      onTimeProductBetaLowGapExceptionalEvent t m ∪
        onTimeSpatialBetaLowGapExceptionalEvent t m := by
  apply Set.Subset.antisymm
  · exact onTimeLowGap_subset_productBeta_union_spatialBeta t hm
  · rintro s (hs | hs)
    · exact hs.1
    · exact hs.1

/-- The affine beta mesh is monotone in its natural index throughout the
low spatial regime. -/
theorem deficitExponent48_mono_index_of_lowGap
    {a : GapScale} (ha : a ∈ lowGapMesh) :
    Monotone (deficitExponent48 (meshExponent a)) := by
  intro i j hij
  have hbase := meshExponent_add_delta_le_kappaOne_of_mem_lowGapMesh ha
  have hstep : 0 ≤ kappaOne - meshExponent a - meshDelta :=
    by linarith
  unfold deficitExponent48
  gcongr

/-- Any strip still below `7 / 10` occurs before the existing 64-tag
endpoint list terminates. -/
theorem index_lt_betaBandCount_of_betaNext_le_sevenTenths
    {a : GapScale} (ha : a ∈ lowGapMesh) {j : ℕ}
    (hbeta : deficitExponent48 (meshExponent a) (j + 1) ≤
      (7 / 10 : ℝ)) :
    j < betaBandCount := by
  by_contra hnot
  have hindex : betaBandCount ≤ j + 1 := by omega
  have hmono := deficitExponent48_mono_index_of_lowGap ha hindex
  have hterminal := alphaMax_lt_terminal_deficitExponent48 ha
  have hseven : (7 / 10 : ℝ) < alphaMax := by
    norm_num [alphaMax]
  linarith

/-- The canonical endpoint list restricted to exactly the beta range in
which the source invokes Proposition 4.8. -/
noncomputable def sourceProductEndpointBands
    (m cap externalThreshold : ℕ) : Finset RandomClockBand :=
  (canonicalEndpointLowGapBands m cap externalThreshold).filter fun band ↦
    band.beta ≤ (7 / 10 : ℝ)

theorem mem_sourceProductEndpointBands_iff
    {m cap externalThreshold : ℕ} {band : RandomClockBand} :
    band ∈ sourceProductEndpointBands m cap externalThreshold ↔
      band ∈ canonicalEndpointLowGapBands m cap externalThreshold ∧
        band.beta ≤ (7 / 10 : ℝ) := by
  classical
  simp [sourceProductEndpointBands]

theorem sourceProductEndpointBands_card_le
    (m cap externalThreshold : ℕ) :
    (sourceProductEndpointBands m cap externalThreshold).card ≤
      Nat.card CanonicalEndpointLowGapBandTag := by
  exact (Finset.card_filter_le _ _).trans
    (canonicalEndpointLowGapBands_card_le m cap externalThreshold)

theorem sourceProductEndpointBand_vertexPhase
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    band.vertexPhase = false :=
  canonicalEndpointLowGapBand_vertexPhase
    (mem_sourceProductEndpointBands_iff.mp hband).1

theorem sourceProductEndpointBand_betaUpperRange
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    band.beta ≤ (7 / 10 : ℝ) :=
  (mem_sourceProductEndpointBands_iff.mp hband).2

theorem sourceProductEndpointBand_betaLower
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    kappaOne ≤ band.beta :=
  canonicalEndpointLowGapBand_betaLower
    (mem_sourceProductEndpointBands_iff.mp hband).1

theorem sourceProductEndpointBand_scale
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    band.scale ∈ lowGapMesh :=
  canonicalEndpointLowGapBand_scale
    (mem_sourceProductEndpointBands_iff.mp hband).1

theorem sourceProductEndpointBand_projects
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    (band.scale, canonicalEndpointBandIndex m band) ∈
      canonicalEndpointLowGapTemplates :=
  canonicalEndpointLowGapBand_projects
    (mem_sourceProductEndpointBands_iff.mp hband).1

theorem sourceProductEndpointBand_betaUpper
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    band.beta ≤ deficitExponent48 (meshExponent band.scale)
      (canonicalEndpointBandIndex m band + 1) :=
  canonicalEndpointLowGapBand_betaUpper
    (mem_sourceProductEndpointBands_iff.mp hband).1

theorem sourceProductEndpointBand_returns
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    requiredReturns48 m
        (deficitExponent48 (meshExponent band.scale)
          (canonicalEndpointBandIndex m band)) ≤ band.returns :=
  canonicalEndpointLowGapBand_returns
    (mem_sourceProductEndpointBands_iff.mp hband).1

/-- The source low-beta event has a fully concrete endpoint extraction.  Its
only non-path input is the scalar cap margin reserving room for every deficit
whose selected upper beta is at most `7 / 10`. -/
theorem tilingLazyGoodEndpointExtraction_onTimeProductBeta
    {t : DominoTiling} {m cap externalThreshold : ℕ}
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤ m + 1) :
    TilingLazyGoodRandomClockExtraction t
      (onTimeProductBetaLowGapExceptionalEvent t m ∩
        VariableStoppedTracePartition.validStepWalk)
      m (levelCutoffTime upperTailDelta m) cap
      (sourceProductEndpointBands m cap externalThreshold) := by
  apply tilingLazyGoodRandomClockExtraction_of_band_realization
  intro s hs
  obtain ⟨p, j, hfull, hbeta⟩ := hs.1.1.2
  rcases hfull with ⟨hj, hband, hupper⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm.le
  have hpower : (m : ℝ) ^
        deficitExponent48 (meshExponent p.scale) (j + 1) ≤
      (m : ℝ) ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR hbeta
  have hdeficit : p.deficit <
      Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) :=
    hupper.trans_le (Nat.ceil_mono hpower)
  have hsum := p.localTime_add_deficit
  have hlarge : cap + externalThreshold ≤
      localTime s p.nOld (s p.nNew) := by omega
  have hvalid : s ∈ VariableStoppedTracePartition.validStepWalk := hs.1.2
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
  have hgood : TilingLazyGoodAt t orientation p.nOld cap s :=
    tiling_lazy_cap_at_creation_of_mem_good hs p.oldRank_pos holdLe
      p.oldCreation
  have hfullExternal : externalThreshold ≤
      pathPhasedExternalLocalTime t orientation s p.nOld (s p.nNew) := by
    apply pathPhasedExternalLocalTime_lower_bound_of_boundary_lazy_cap
      (hgood (s p.nNew))
    exact hlarge
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

end

end Erdos1165.HLOZFullBetaRegimeSplit
