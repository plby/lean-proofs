/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPaymentFilteredTilingEndpointSourceRowData

/-!
# Raw Proposition 4.9 profiles outside the source/Theta payment

This is the deterministic first half of the six-row cover.  A raw rank
transition outside the concrete source/Theta payment is a valid path, occurs
after the harmless finite level prefix, creates its old-favorite rank before
the cutoff, and is outside both the four-class source-cardinality overflow
and the transported source/Theta/checker payment.

No probability or transition estimate occurs in these statements.
-/

open Set

namespace Erdos1165.HLOZRawProp49UnpaidProfile

open HLOZPathEvents HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion HLOZRawOrientedSourceThetaPayment
open HLOZSourceCorrectFullGapClosure
open HLOZSourceOrientedThetaRankPayment
open HLOZThetaSourceBalance
open LazyDecomposition ScreeningInstantiation
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZRawFullGapProductPromotion.GapTriple

/-- The complete creation profile available pathwise after subtracting the
literal rank source/Theta payment. -/
structure RawProp49UnpaidProfile
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (s : WalkPath) : Prop where
  level_two : 2 ≤ m
  valid : s ∈ validStepWalk
  on_time_profile : ∃ creationTime,
    ThresholdCreation s m rank creationTime ∧
    thresholdCount s creationTime (m + 1) = 0 ∧
    tilingDEtaAtCreation t m rank (shellWidth48 m)
      (m - shellWidth48 m) s ∧
    TilingThresholdDominoSeparated t s creationTime m ∧
    creationTime ≤ levelCutoffTime upperTailDelta m
  source_card_good : s ∉ orientedCreationSourceOverflowUnionAtRank
    data t rank m
  source_theta_good : s ∉ candidateLocalSourceThetaPaymentAtRank
    data t rank m

private theorem rawProp49UnpaidProfile_of_preliminary
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (hrank : 0 < rank)
    (preliminary : Set WalkPath) (s : WalkPath)
    (hpreliminary : s ∈ preliminary)
    (hprofile : RawSourceCreationProfile t m rank s)
    (hsource : preliminary ∩
        orientedCreationSourceOverflowUnionAtRank data t rank m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t rank m)
    (hunpaid : s ∉ rawOrientedSourceThetaTotalPaymentAtRank
      data t rank m) :
    RawProp49UnpaidProfile data t rank m s := by
  have hm : 2 ≤ m := by
    by_contra hm
    apply hunpaid
    exact Or.inl (by simp [sourceThetaSmallLevelPayment, hm])
  have hvalid : s ∈ validStepWalk := by
    by_contra hvalid
    apply hunpaid
    exact Or.inr (Or.inl hvalid)
  have hsourceGood : s ∉
      orientedCreationSourceOverflowUnionAtRank data t rank m := by
    intro hoverflow
    exact hunpaid (hsource ⟨hpreliminary, hoverflow⟩)
  have hthetaGood : s ∉
      candidateLocalSourceThetaPaymentAtRank data t rank m := by
    intro htheta
    exact hunpaid (Or.inr (Or.inr (Or.inr htheta)))
  rcases hprofile with ⟨N, hcreation, hnext, hD, hsep⟩
  have hclock : N ≤ levelCutoffTime upperTailDelta m := by
    by_contra hclock
    apply hunpaid
    exact Or.inr (Or.inr (Or.inl
      (creation_after_levelCutoff_mem_lateLevelSet hrank hcreation hnext
        (Nat.lt_of_not_ge hclock))))
  exact
    { level_two := hm
      valid := hvalid
      on_time_profile := ⟨N, hcreation, hnext, hD, hsep, hclock⟩
      source_card_good := hsourceGood
      source_theta_good := hthetaGood }

/-- Rank-one raw transition histories outside the exact source/Theta payment
carry the complete good creation profile. -/
theorem firstRawCandidatePreliminary_unpaid_profile
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath)
    (hs : s ∈ firstRawCandidatePreliminary t m a \
      rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) :
    RawProp49UnpaidProfile data t 1 m s := by
  exact rawProp49UnpaidProfile_of_preliminary data t 1 m (by omega)
    (firstRawCandidatePreliminary t m a) s hs.1
    (firstRawCandidatePreliminary_sourceCreationProfile (by
      have : 2 ≤ m := by
        by_contra hm
        exact hs.2 (Or.inl (by simp [sourceThetaSmallLevelPayment, hm]))
      omega) hs.1)
    (firstRawSource_subset_rawOrientedSourceThetaTotalPayment data t m a)
    hs.2

/-- Rank-two analogue of `firstRawCandidatePreliminary_unpaid_profile`. -/
theorem secondRawCandidatePreliminary_unpaid_profile
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath)
    (hs : s ∈ secondRawCandidatePreliminary t m a \
      rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) :
    RawProp49UnpaidProfile data t 2 m s := by
  exact rawProp49UnpaidProfile_of_preliminary data t 2 m (by omega)
    (secondRawCandidatePreliminary t m a) s hs.1
    (secondRawCandidatePreliminary_sourceCreationProfile (by
      have : 2 ≤ m := by
        by_contra hm
        exact hs.2 (Or.inl (by simp [sourceThetaSmallLevelPayment, hm]))
      omega) hs.1)
    (secondRawSource_subset_rawOrientedSourceThetaTotalPayment data t m a)
    hs.2

/-- Rank-three analogue of `firstRawCandidatePreliminary_unpaid_profile`. -/
theorem thirdRawCandidatePreliminary_unpaid_profile
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath)
    (hs : s ∈ thirdRawCandidatePreliminary t m a \
      rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) :
    RawProp49UnpaidProfile data t 3 m s := by
  exact rawProp49UnpaidProfile_of_preliminary data t 3 m (by omega)
    (thirdRawCandidatePreliminary t m a) s hs.1
    (thirdRawCandidatePreliminary_sourceCreationProfile (by
      have : 2 ≤ m := by
        by_contra hm
        exact hs.2 (Or.inl (by simp [sourceThetaSmallLevelPayment, hm]))
      omega) hs.1)
    (thirdRawSource_subset_rawOrientedSourceThetaTotalPayment data t m a)
    hs.2

end

end Erdos1165.HLOZRawProp49UnpaidProfile
