/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZRawProp49NarrowCandidateGeometry

/-!
# Literal source-cardinality bounds outside the raw payment

The rankwise creation-source overflow is a finite union over endpoint bands.
For a low mesh cell and ranks one through three that list is nonempty: the
index-zero band has beta exactly `kappaOne`, hence lies below `7 / 10`.
Consequently the complement of the union overflow gives the four literal
oriented source-cardinality bounds, rather than a vacuous statement about an
empty band list.
-/

open Set

namespace Erdos1165.HLOZRawProp49SourceCardinality

open HLOZCandidateLocalLazyCap HLOZFullBetaRegimeSplit
open HLOZGapBetaArithmetic HLOZPathEvents HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion HLOZRawProp49UnpaidProfile
open HLOZRawShellCreationBridge HLOZSourceCorrectFullGapClosure
open HLOZSourceCorrectFilteredTransitions HLOZThetaSourceBalance
open HLOZTilingEndpointBandExtraction HLOZTilingGapBandExtraction
open LazyDecomposition
open ScreeningInstantiation
open TilingOrientedShellZeroSourcePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A concrete source-product band at every low scale and old rank one,
two, or three. -/
theorem exists_sourceProductEndpointBandAtRank
    (m cap externalThreshold rank : ℕ) (a : GapScale)
    (hrank : 0 < rank) (hrank_le : rank ≤ 3) (ha : a ∈ lowGapMesh) :
    ∃ band ∈ sourceProductEndpointBandsAtRank
        m cap externalThreshold rank,
      band.scale = a := by
  classical
  let pair : Fin 3 := ⟨rank - 1, by omega⟩
  let tag : CanonicalEndpointLowGapBandTag :=
    { pair := pair
      scale := a
      orientation := false
      index := ⟨0, by simp [betaBandCount]⟩ }
  let band := canonicalEndpointLowGapBand m cap externalThreshold tag
  have hcanonical : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold :=
    canonicalEndpointLowGapBand_mem m cap externalThreshold tag ha
  have hbeta : band.beta ≤ (7 / 10 : ℝ) := by
    simp only [band, tag, canonicalEndpointLowGapBand,
      endpointLowGapScale_eq_of_mem tag ha]
    norm_num [deficitExponent48, kappaOne]
  have hsource : band ∈
      sourceProductEndpointBands m cap externalThreshold :=
    mem_sourceProductEndpointBands_iff.mpr ⟨hcanonical, hbeta⟩
  have holdRank : band.oldRank = rank := by
    simp only [band, tag, canonicalEndpointLowGapBand, pair]
    omega
  refine ⟨band, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hsource, holdRank⟩
  · simp only [band, tag, canonicalEndpointLowGapBand,
      endpointLowGapScale_eq_of_mem tag ha]

/-- The four rank-local cardinal inequalities furnished by the complement of
the literal creation-source overflow. -/
structure RawProp49SourceCardinalityProfile
    (t : DominoTiling) (m rank : ℕ) (s : WalkPath) : Prop where
  canonical_even :
    (orientedCanonicalDominantNearBasesAtCreation t .even m rank
      (shellWidth48 m) s).card ≤ orientedSourceCut48 m
  canonical_shifted :
    (orientedCanonicalDominantNearBasesAtCreation t .shifted m rank
      (shellWidth48 m) s).card ≤ orientedSourceCut48 m
  opposite_even :
    (orientedOppositeDominantNearEndpointsAtCreation t .even m rank
      (shellWidth48 m) s).card ≤ orientedSourceCut48 m
  opposite_shifted :
    (orientedOppositeDominantNearEndpointsAtCreation t .shifted m rank
      (shellWidth48 m) s).card ≤ orientedSourceCut48 m

/-- A raw unpaid low history has all four literal source-cardinality bounds.
The low mesh witness is used only to exhibit one genuine band in the rank
filtered finite list. -/
theorem RawProp49UnpaidProfile.sourceCardinalityProfile
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {rank m : ℕ} {a : GapScale} {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (hrank : 0 < rank) (hrank_le : rank ≤ 3) (ha : a ∈ lowGapMesh) :
    RawProp49SourceCardinalityProfile t m rank s := by
  obtain ⟨band, hband, _hscale⟩ :=
    exists_sourceProductEndpointBandAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank a hrank hrank_le ha
  have hnot : s ∉ orientedCreationSourceOverflowEvent t m band := by
    intro hoverflow
    exact hprofile.source_card_good ⟨band, hband, hoverflow⟩
  have hrankBand : band.oldRank = rank := (Finset.mem_filter.mp hband).2
  constructor
  · by_contra hcard
    apply hnot
    exact Or.inl (Or.inl (Or.inl (by
      simpa only [Set.mem_ofPred_eq, hrankBand] using Nat.lt_of_not_ge hcard)))
  · by_contra hcard
    apply hnot
    exact Or.inl (Or.inl (Or.inr (by
      simpa only [Set.mem_ofPred_eq, hrankBand] using Nat.lt_of_not_ge hcard)))
  · by_contra hcard
    apply hnot
    exact Or.inl (Or.inr (by
      simpa only [Set.mem_ofPred_eq, hrankBand] using Nat.lt_of_not_ge hcard))
  · by_contra hcard
    apply hnot
    exact Or.inr (by
      simpa only [Set.mem_ofPred_eq, hrankBand] using Nat.lt_of_not_ge hcard)

end

end Erdos1165.HLOZRawProp49SourceCardinality
