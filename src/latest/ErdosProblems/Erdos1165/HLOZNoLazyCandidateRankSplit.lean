/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyFullBetaProductBranch
import ErdosProblems.Erdos1165.HLOZSourceCorrectFilteredTransitions

/-!
# Carrier-independent rank split for the no-lazy product screen

The source-low endpoint list is indexed by one of the three old-favorite
ranks.  This module records that finite split before any shell recurrence,
source carrier, or positive-interface data are introduced.  In particular,
the exact candidate-local product event is preserved in every rank term.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZNoLazyCandidateRankSplit

open HLOZFullBetaRegimeSplit HLOZGapRandomClockScreen
open HLOZNoLazyFullBetaProductBranch HLOZPathEvents
open HLOZProposition48Candidates HLOZTilingEndpointBandSelector
open HLOZSourceCorrectFilteredTransitions
open HLOZThetaSourceBalance
open HLOZTilingEndpointBandExtraction HLOZTilingGapRandomClockScreen

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The raw overflow term in the no-lazy candidate-local measure screen. -/
def candidateLocalProductOverflowEvent
    (t : DominoTiling) (m cutoff cap externalThreshold : ℕ) : Set WalkPath :=
  onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
      externalThreshold ∩
    tilingRandomClockCandidateOverflow t m cutoff
      (sourceProductEndpointBands m cap externalThreshold)

/-- The same exact overflow restricted to endpoint bands with the displayed
old-favorite rank. -/
def candidateLocalProductOverflowAtRank
    (t : DominoTiling) (m cutoff cap externalThreshold rank : ℕ) :
    Set WalkPath :=
  onTimeCandidateLocalProductBetaLowGapExceptionalEvent t m
      externalThreshold ∩
    rankCandidateOverflowEvent t m cutoff cap externalThreshold rank

/-- Every source-low endpoint band has one of the three genuine old-favorite
ranks.  This follows from the literal `Fin 3` endpoint tag. -/
theorem sourceProductEndpointBand_oldRank_eq_one_or_two_or_three
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m cap externalThreshold) :
    band.oldRank = 1 ∨ band.oldRank = 2 ∨ band.oldRank = 3 := by
  have hcanonical := (mem_sourceProductEndpointBands_iff.mp hband).1
  obtain ⟨tag, _hscale, htag⟩ :=
    (mem_canonicalEndpointLowGapBands_iff m cap externalThreshold band).mp
      hcanonical
  rw [← htag]
  change (tag.pair : ℕ) + 1 = 1 ∨
    (tag.pair : ℕ) + 1 = 2 ∨ (tag.pair : ℕ) + 1 = 3
  omega

/-- The full source-low candidate overflow is covered by the three old-rank
subfamilies. -/
theorem tilingRandomClockCandidateOverflow_sourceProduct_subset_rank_union
    (t : DominoTiling) (m cutoff cap externalThreshold : ℕ) :
    tilingRandomClockCandidateOverflow t m cutoff
        (sourceProductEndpointBands m cap externalThreshold) ⊆
      rankCandidateOverflowEvent t m cutoff cap externalThreshold 1 ∪
        (rankCandidateOverflowEvent t m cutoff cap externalThreshold 2 ∪
          rankCandidateOverflowEvent t m cutoff cap externalThreshold 3) := by
  intro s hs
  rcases hs with ⟨band, hband, hoverflow⟩
  rcases sourceProductEndpointBand_oldRank_eq_one_or_two_or_three hband with
      hrank | hrank | hrank
  · exact Or.inl ⟨band, Finset.mem_filter.mpr ⟨hband, hrank⟩, hoverflow⟩
  · exact Or.inr (Or.inl
      ⟨band, Finset.mem_filter.mpr ⟨hband, hrank⟩, hoverflow⟩)
  · exact Or.inr (Or.inr
      ⟨band, Finset.mem_filter.mpr ⟨hband, hrank⟩, hoverflow⟩)

/-- The exact candidate-local overflow splits into three intersections with
the same candidate-local product event.  No source event is enlarged during
this finite routing step. -/
theorem candidateLocalProductOverflowEvent_subset_rank_union
    (t : DominoTiling) (m cutoff cap externalThreshold : ℕ) :
    candidateLocalProductOverflowEvent t m cutoff cap externalThreshold ⊆
      candidateLocalProductOverflowAtRank t m cutoff cap externalThreshold 1 ∪
        (candidateLocalProductOverflowAtRank t m cutoff cap externalThreshold 2 ∪
          candidateLocalProductOverflowAtRank t m cutoff cap externalThreshold 3) := by
  intro s hs
  have hranks :=
    tilingRandomClockCandidateOverflow_sourceProduct_subset_rank_union
      t m cutoff cap externalThreshold hs.2
  rcases hranks with hrank | hrank | hrank
  · exact Or.inl ⟨hs.1, hrank⟩
  · exact Or.inr (Or.inl ⟨hs.1, hrank⟩)
  · exact Or.inr (Or.inr ⟨hs.1, hrank⟩)

/-! ## Exact creation profiles retained by the rank split -/

/-- The rank-one overflow intersection retains the literal creation,
no-next-level, and `D_eta` data of the candidate-local product event. -/
theorem candidateLocalProductOverflowAtRank_one_creationSourceData
    {t : DominoTiling} {m cutoff cap externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ candidateLocalProductOverflowAtRank t m cutoff cap
      externalThreshold 1) :
    ∃ n, ThresholdCreation s m 1 n ∧
      thresholdCount s n (m + 1) = 0 ∧
      tilingDEtaAtCreation t m 1 (shellWidth48 m)
        (m - shellWidth48 m) s :=
  onTimeCandidateLocalProductBeta_rankOne_creationSourceData hm hs.1

/-- Rank-two creation data on the exact rankwise overflow. -/
theorem candidateLocalProductOverflowAtRank_two_creationSourceData
    {t : DominoTiling} {m cutoff cap externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ candidateLocalProductOverflowAtRank t m cutoff cap
      externalThreshold 2) :
    ∃ n, ThresholdCreation s m 2 n ∧
      thresholdCount s n (m + 1) = 0 ∧
      tilingDEtaAtCreation t m 2 (shellWidth48 m)
        (m - shellWidth48 m) s :=
  onTimeCandidateLocalProductBeta_rankTwo_creationSourceData hm hs.1

/-- Rank-three creation data on the exact rankwise overflow. -/
theorem candidateLocalProductOverflowAtRank_three_creationSourceData
    {t : DominoTiling} {m cutoff cap externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ candidateLocalProductOverflowAtRank t m cutoff cap
      externalThreshold 3) :
    ∃ n, ThresholdCreation s m 3 n ∧
      thresholdCount s n (m + 1) = 0 ∧
      tilingDEtaAtCreation t m 3 (shellWidth48 m)
        (m - shellWidth48 m) s :=
  onTimeCandidateLocalProductBeta_rankThree_creationSourceData hm hs.1

end

end Erdos1165.HLOZNoLazyCandidateRankSplit
