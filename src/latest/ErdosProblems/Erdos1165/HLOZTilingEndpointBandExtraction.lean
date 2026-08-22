/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingGapBandExtraction
import ErdosProblems.Erdos1165.TilingExternalPhaseSplit

/-!
# Endpoint-only all-six low-gap bands

The one-point estimate applies to the endpoint chain of the state-dependent
deleted walk.  For a genuine nearest-neighbour path, a site compatible with
the chosen temporal orientation has no midpoint occurrences.  This module
therefore selects the compatible temporal orientation and retains only bands
whose vertex phase is the endpoint phase.  Invalid paths are kept outside
the pathwise extraction; they form a measurable null set under simple random
walk.
-/

open Set

namespace Erdos1165.HLOZTilingEndpointBandExtraction

open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open HLOZGapBetaArithmetic
open HLOZTilingGapBandExtraction HLOZTilingGapRandomClockScreen
open LazyDecomposition SpatialInsertionFiber PreStoppingSpatialLaw
open TilingExternalPhaseSplit TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Choose the temporal orientation whose endpoint checkerboard class
contains `x`. -/
noncomputable def compatibleOrientation (x : Point) : Orientation := by
  classical
  exact
  if EvenPoint x then .even else .shifted

theorem compatibleOrientation_compatible (x : Point) :
    OrientationCompatible (compatibleOrientation x) x := by
  classical
  unfold compatibleOrientation
  by_cases hx : EvenPoint x
  · rw [if_pos hx]
    exact hx
  · have hodd : OddPoint x :=
      (evenPoint_or_oddPoint x).resolve_left hx
    rw [if_neg hx]
    exact hodd

def orientationOfBool : Bool → Orientation
  | false => .even
  | true => .shifted

def boolOfOrientation : Orientation → Bool
  | .even => false
  | .shifted => true

@[simp] theorem orientationOfBool_boolOfOrientation (o : Orientation) :
    orientationOfBool (boolOfOrientation o) = o := by
  cases o <;> rfl

/-- Finite path-independent index. -/
structure CanonicalEndpointLowGapBandTag where
  pair : Fin 3
  scale : GapScale
  orientation : Bool
  index : Fin betaBandCount
  deriving DecidableEq

private abbrev EndpointTagCoordinate :=
  Fin 3 × (GapScale × (Bool × Fin betaBandCount))

private def coordinateOfEndpointTag
    (tag : CanonicalEndpointLowGapBandTag) : EndpointTagCoordinate :=
  ⟨tag.pair, tag.scale, tag.orientation, tag.index⟩


private theorem coordinateOfEndpointTag_injective :
    Function.Injective coordinateOfEndpointTag := by
  intro a b h
  cases a
  cases b
  simp_all [coordinateOfEndpointTag]

noncomputable local instance endpointTagFinite :
    Finite CanonicalEndpointLowGapBandTag :=
  Finite.of_injective coordinateOfEndpointTag
    coordinateOfEndpointTag_injective

private def admissibleEndpointLowGapTags : Set CanonicalEndpointLowGapBandTag :=
  {tag | tag.scale ∈ lowGapMesh}

/-- A fixed low scale used only to make the band constructor total outside
the enumerated low mesh. -/
def firstLowGapScale : GapScale := ⟨0, by simp [meshSteps]⟩

theorem firstLowGapScale_mem : firstLowGapScale ∈ lowGapMesh := by
  rw [mem_lowGapMesh_iff]
  constructor
  · rw [properGapMesh, Finset.mem_erase]
    constructor
    · intro h
      have hv := congrArg Fin.val h
      norm_num [firstLowGapScale, overflowScale, meshSteps] at hv
    · exact Finset.mem_univ _
  · norm_num [meshExponent, firstLowGapScale,
      ScreeningInstantiation.meshDelta, ScreeningInstantiation.kappaTwo]

noncomputable def endpointLowGapScale
    (tag : CanonicalEndpointLowGapBandTag) : GapScale :=
  if tag.scale ∈ lowGapMesh then tag.scale else firstLowGapScale

theorem endpointLowGapScale_mem (tag : CanonicalEndpointLowGapBandTag) :
    endpointLowGapScale tag ∈ lowGapMesh := by
  classical
  unfold endpointLowGapScale
  split_ifs with h
  · exact h
  · exact firstLowGapScale_mem

@[simp] theorem endpointLowGapScale_eq_of_mem
    (tag : CanonicalEndpointLowGapBandTag) (hscale : tag.scale ∈ lowGapMesh) :
    endpointLowGapScale tag = tag.scale := by
  simp [endpointLowGapScale, hscale]

/-- One endpoint band.  Physical creation times and the redundant midpoint
phase are absent from its finite index. -/
noncomputable def canonicalEndpointLowGapBand
    (m cap externalThreshold : ℕ)
    (tag : CanonicalEndpointLowGapBandTag) : RandomClockBand :=
  { orientation := orientationOfBool tag.orientation
    vertexPhase := false
    oldRank := tag.pair + 1
    newRank := tag.pair + 2
    returns := requiredReturns48 m
      (deficitExponent48 (meshExponent tag.scale) tag.index)
    externalThreshold := externalThreshold
    lazyCap := cap
    beta := deficitExponent48 (meshExponent tag.scale) (tag.index + 1)
    scale := endpointLowGapScale tag
    oldRank_pos := by omega
    newRank_pos := by omega
    rank_lt := by omega
    newRank_le_four := by omega
    scale_proper :=
      (mem_lowGapMesh_iff.mp (endpointLowGapScale_mem tag)).1 }

private def canonicalEndpointLowGapBandSet
    (m cap externalThreshold : ℕ) : Set RandomClockBand :=
  canonicalEndpointLowGapBand m cap externalThreshold ''
    admissibleEndpointLowGapTags

private theorem canonicalEndpointLowGapBandSet_finite
    (m cap externalThreshold : ℕ) :
    (canonicalEndpointLowGapBandSet m cap externalThreshold).Finite := by
  apply Set.Finite.image
  exact Set.toFinite admissibleEndpointLowGapTags

/-- The literal finite list of endpoint bands. -/
noncomputable def canonicalEndpointLowGapBands
    (m cap externalThreshold : ℕ) : Finset RandomClockBand :=
  (canonicalEndpointLowGapBandSet_finite
    m cap externalThreshold).toFinset

theorem canonicalEndpointLowGapBand_mem
    (m cap externalThreshold : ℕ)
    (tag : CanonicalEndpointLowGapBandTag) :
    tag.scale ∈ lowGapMesh →
    canonicalEndpointLowGapBand m cap externalThreshold tag ∈
      canonicalEndpointLowGapBands m cap externalThreshold := by
  intro hscale
  rw [canonicalEndpointLowGapBands,
    Set.Finite.mem_toFinset]
  exact ⟨tag, hscale, rfl⟩

/-- Membership in the canonical finite band list is exactly representation
by one admissible endpoint tag. -/
theorem mem_canonicalEndpointLowGapBands_iff
    (m cap externalThreshold : ℕ) (band : RandomClockBand) :
    band ∈ canonicalEndpointLowGapBands m cap externalThreshold ↔
      ∃ tag : CanonicalEndpointLowGapBandTag,
        tag.scale ∈ lowGapMesh ∧
          canonicalEndpointLowGapBand m cap externalThreshold tag = band := by
  rw [canonicalEndpointLowGapBands, Set.Finite.mem_toFinset]
  rfl

/-- A uniform cardinal bound independent of the level and the two local-time
cutoffs.  This deliberately counts all endpoint tags, so collisions between
tags can only improve the estimate. -/
theorem canonicalEndpointLowGapBands_card_le
    (m cap externalThreshold : ℕ) :
    (canonicalEndpointLowGapBands m cap externalThreshold).card ≤
      Nat.card CanonicalEndpointLowGapBandTag := by
  rw [canonicalEndpointLowGapBands,
    ← Set.ncard_eq_toFinset_card _
      (canonicalEndpointLowGapBandSet_finite m cap externalThreshold)]
  exact (Set.ncard_image_le (Set.toFinite admissibleEndpointLowGapTags)).trans
    (Set.ncard_le_card admissibleEndpointLowGapTags)

theorem canonicalEndpointLowGapBand_scale
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    band.scale ∈ lowGapMesh := by
  obtain ⟨tag, hscale, rfl⟩ :=
    (mem_canonicalEndpointLowGapBands_iff
      m cap externalThreshold band).mp hband
  simpa only [canonicalEndpointLowGapBand,
    endpointLowGapScale_eq_of_mem tag hscale] using hscale

theorem canonicalEndpointLowGapBand_vertexPhase
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    band.vertexPhase = false := by
  obtain ⟨tag, _hscale, rfl⟩ :=
    (mem_canonicalEndpointLowGapBands_iff
      m cap externalThreshold band).mp hband
  rfl

theorem canonicalEndpointLowGapBand_externalThreshold
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    band.externalThreshold = externalThreshold := by
  obtain ⟨tag, _hscale, rfl⟩ :=
    (mem_canonicalEndpointLowGapBands_iff
      m cap externalThreshold band).mp hband
  rfl

theorem canonicalEndpointLowGapBand_lazyCap
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    band.lazyCap = cap := by
  obtain ⟨tag, _hscale, rfl⟩ :=
    (mem_canonicalEndpointLowGapBands_iff
      m cap externalThreshold band).mp hband
  rfl

/-- Sound endpoint-chain extraction on the support of simple random walk.
Compared with the earlier endpoint/midpoint split, the required actual local
time is only `cap + externalThreshold`: no factor two is lost. -/
theorem tilingLazyGoodEndpointExtraction_of_failedPairBetaBands
    {t : DominoTiling} {gapEvent : Set WalkPath}
    {m cutoff cap externalThreshold : ℕ}
    (hthreshold : 0 < externalThreshold)
    (hselect : ∀ s ∈
        tilingLazyGoodPart t
          (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) m cap,
      ∃ p : LowGapFailedPair t m cutoff s,
        cap + externalThreshold ≤ localTime s p.nOld (s p.nNew) ∧
          ∃ j < betaBandCount, FailedPairBetaBand p j) :
    TilingLazyGoodRandomClockExtraction t
      (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
      m cutoff cap
      (canonicalEndpointLowGapBands m cap externalThreshold) := by
  apply tilingLazyGoodRandomClockExtraction_of_band_realization
  intro s hs
  obtain ⟨p, hlarge, j, hj, hbeta⟩ := hselect s hs
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
  let index : Fin betaBandCount := ⟨j, hj⟩
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
    have hm : 0 < m := by
      have hlt : 0 < localTime s p.nOld (s p.nNew) := by omega
      rw [← p.localTime_add_deficit]
      omega
    dsimp only [band, tag, canonicalEndpointLowGapBand,
      index]
    rw [requiredReturns48_add_one
      (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)]
    exact hbeta.1
  have hrealizes := p.randomClockPairRealizes band hranks hbandScale hreturns
  refine ⟨band,
    canonicalEndpointLowGapBand_mem m cap externalThreshold tag p.scale_low,
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
      LowGapFailedPair.deficit] using hbeta.2

end

end Erdos1165.HLOZTilingEndpointBandExtraction
