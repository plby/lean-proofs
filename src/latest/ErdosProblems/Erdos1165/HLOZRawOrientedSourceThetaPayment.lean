/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaRankPayment

/-!
# Raw transition source-overflow payments

The three raw transition preliminaries carry literal rank creation,
no-next-level, `D_eta`, and domino separation.  Splitting their creation clock
at the deterministic cutoff reduces the on-time part to the existing
transported source/Theta payment; the remaining late and invalid parts are
already summable.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZRawOrientedSourceThetaPayment

open ExternalProposition44 HLOZGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion HLOZSourceOrientedThetaRankPayment
open HLOZShellZeroReplacementWindows HLOZSourceCorrectFullGapClosure
open HLOZThetaSourceBalance HLOZTilingGapBandExtraction LazyDecomposition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def RawSourceCreationProfile
    (t : DominoTiling) (m rank : ℕ) (s : WalkPath) : Prop :=
  ∃ time,
    ThresholdCreation s m rank time ∧
    thresholdCount s time (m + 1) = 0 ∧
    tilingDEtaAtCreation t m rank (shellWidth48 m)
      (m - shellWidth48 m) s ∧
    TilingThresholdDominoSeparated t s time m

theorem firstRawCandidatePreliminary_sourceCreationProfile
    {t : DominoTiling} {m : ℕ}
    {a : HLOZRawFullGapProductPromotion.GapTriple} {s : WalkPath}
    (hm : 0 < m) (hs : s ∈ firstRawCandidatePreliminary t m a) :
    RawSourceCreationProfile t m 1 s := by
  rcases hs.1 with hstage
  simp only [firstTransitionEvent, Set.mem_iUnion] at hstage
  rcases hstage with ⟨n₁, n₂, h₁, h₂, hnext, _hsep, _ha⟩
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₁ : thresholdCount s n₁ (m + 1) = 0 := by
    change thresholdCount s n₁ (m + 1) ≤
      thresholdCount s n₂ (m + 1) at hmono
    omega
  have hsep₁ := thresholdDominoSeparated_of_singleton (t := t)
    (thresholdSites_eq_singleton_at_first_creation h₁)
  exact ⟨n₁, h₁, hnext₁,
    tilingDEtaAtCreation_of_creation_of_dominoSeparated hm
      (by omega) rfl h₁ hnext₁ hsep₁, hsep₁⟩

theorem secondRawCandidatePreliminary_sourceCreationProfile
    {t : DominoTiling} {m : ℕ}
    {a : HLOZRawFullGapProductPromotion.GapTriple} {s : WalkPath}
    (hm : 0 < m) (hs : s ∈ secondRawCandidatePreliminary t m a) :
    RawSourceCreationProfile t m 2 s := by
  rcases hs.1 with hstage
  simp only [secondTransitionEvent, Set.mem_iUnion] at hstage
  rcases hstage with
    ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, h₁₂, _h₁₃, _h₂₃, _ha₁, _ha₂⟩
  have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₂ : thresholdCount s n₂ (m + 1) = 0 := by
    change thresholdCount s n₂ (m + 1) ≤
      thresholdCount s n₃ (m + 1) at hmono
    omega
  have hsep₂ := thresholdDominoSeparated_of_pair
    (thresholdSites_eq_pair_at_second_creation h₁ h₂) h₁₂
  exact ⟨n₂, h₂, hnext₂,
    tilingDEtaAtCreation_of_creation_of_dominoSeparated hm
      (by omega) rfl h₂ hnext₂ hsep₂, hsep₂⟩

theorem thirdRawCandidatePreliminary_sourceCreationProfile
    {t : DominoTiling} {m : ℕ}
    {a : HLOZRawFullGapProductPromotion.GapTriple} {s : WalkPath}
    (hm : 0 < m) (hs : s ∈ thirdRawCandidatePreliminary t m a) :
    RawSourceCreationProfile t m 3 s := by
  rcases hs.1 with hstage
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hstage
  rcases hstage with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
      _ha₁, _ha₂, _ha₃⟩
  have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₃ : thresholdCount s n₃ (m + 1) = 0 := by
    change thresholdCount s n₃ (m + 1) ≤
      thresholdCount s n₄ (m + 1) at hmono
    omega
  rcases hsep with ⟨h₁₂, h₁₃, _h₁₄, h₂₃, _h₂₄, _h₃₄⟩
  have hsep₃ := thresholdDominoSeparated_of_triple
    (thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃)
      h₁₂ h₁₃ h₂₃
  exact ⟨n₃, h₃, hnext₃,
    tilingDEtaAtCreation_of_creation_of_dominoSeparated hm
      (by omega) rfl h₃ hnext₃ hsep₃, hsep₃⟩

def rawOrientedSourceThetaTotalPaymentAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  sourceThetaSmallLevelPayment m ∪
    (validStepWalkᶜ ∪
      (lateLevelSet upperTailDelta m rank ∪
        candidateLocalSourceThetaPaymentAtRank data t rank m))

private theorem rawPreliminarySource_subset_totalPayment_of_profile
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (hm : 2 ≤ m) (hrank : 0 < rank)
    (preliminary : Set WalkPath)
    (hprofile : ∀ s ∈ preliminary, RawSourceCreationProfile t m rank s) :
    preliminary ∩ orientedCreationSourceOverflowUnionAtRank data t rank m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t rank m := by
  rintro s ⟨hpreliminary, band, hband, hsource⟩
  rcases hprofile s hpreliminary with
    ⟨N, hcreation, hnext, hD, hsep⟩
  by_cases hvalid : s ∈ validStepWalk
  · by_cases hclock : N ≤ levelCutoffTime upperTailDelta m
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      have hrankBand : band.oldRank = rank := (Finset.mem_filter.mp hband).2
      rcases hsource with ((h | h) | h) | h
      · exact orientedCreationClass_mem_source_theta_or_checker data t .even
          .canonical hm hrank hvalid hband hcreation hnext hD hsep hclock
            (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
            (fun hbad ↦ nomatch hbad)
      · exact orientedCreationClass_mem_source_theta_or_checker data t .shifted
          .canonical hm hrank hvalid hband hcreation hnext hD hsep hclock
            (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
            (fun hbad ↦ nomatch hbad)
      · exact orientedCreationClass_mem_source_theta_or_checker data t .even
          .opposite hm hrank hvalid hband hcreation hnext hD hsep hclock
            (fun hbad ↦ nomatch hbad)
            (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
      · exact orientedCreationClass_mem_source_theta_or_checker data t .shifted
          .opposite hm hrank hvalid hband hcreation hnext hD hsep hclock
            (fun hbad ↦ nomatch hbad)
            (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      exact creation_after_levelCutoff_mem_lateLevelSet hrank hcreation hnext
        (Nat.lt_of_not_ge hclock)
  · exact Or.inr (Or.inl hvalid)

theorem firstRawSource_subset_rawOrientedSourceThetaTotalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ)
    (a : HLOZRawFullGapProductPromotion.GapTriple) :
    firstRawCandidatePreliminary t m a ∩
        orientedCreationSourceOverflowUnionAtRank data t 1 m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 1 m := by
  by_cases hm : 2 ≤ m
  · exact rawPreliminarySource_subset_totalPayment_of_profile data t 1 m hm
      (by omega) _ (fun _ hs ↦
        firstRawCandidatePreliminary_sourceCreationProfile (by omega) hs)
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem secondRawSource_subset_rawOrientedSourceThetaTotalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ)
    (a : HLOZRawFullGapProductPromotion.GapTriple) :
    secondRawCandidatePreliminary t m a ∩
        orientedCreationSourceOverflowUnionAtRank data t 2 m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 2 m := by
  by_cases hm : 2 ≤ m
  · exact rawPreliminarySource_subset_totalPayment_of_profile data t 2 m hm
      (by omega) _ (fun _ hs ↦
        secondRawCandidatePreliminary_sourceCreationProfile (by omega) hs)
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem thirdRawSource_subset_rawOrientedSourceThetaTotalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ)
    (a : HLOZRawFullGapProductPromotion.GapTriple) :
    thirdRawCandidatePreliminary t m a ∩
        orientedCreationSourceOverflowUnionAtRank data t 3 m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 3 m := by
  by_cases hm : 2 ≤ m
  · exact rawPreliminarySource_subset_totalPayment_of_profile data t 3 m hm
      (by omega) _ (fun _ hs ↦
        thirdRawCandidatePreliminary_sourceCreationProfile (by omega) hs)
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem candidateLocalSourceOne_subset_rawOrientedSourceThetaTotalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalOrientedSourceEventAtRank data t 1 m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 1 m := by
  by_cases hm : 2 ≤ m
  · intro s hs
    exact Or.inr (Or.inr (Or.inr
      (candidateLocalOrientedSourceEventAtRank_one_subset_payment
        data t m hm hs)))
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem candidateLocalSourceTwo_subset_rawOrientedSourceThetaTotalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalOrientedSourceEventAtRank data t 2 m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 2 m := by
  by_cases hm : 2 ≤ m
  · intro s hs
    exact Or.inr (Or.inr (Or.inr
      (candidateLocalOrientedSourceEventAtRank_two_subset_payment
        data t m hm hs)))
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem candidateLocalSourceThree_subset_rawOrientedSourceThetaTotalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalOrientedSourceEventAtRank data t 3 m ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 3 m := by
  by_cases hm : 2 ≤ m
  · intro s hs
    exact Or.inr (Or.inr (Or.inr
      (candidateLocalOrientedSourceEventAtRank_three_subset_payment
        data t m hm hs)))
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

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

theorem simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (rawOrientedSourceThetaTotalPaymentAtRank data t rank m) ≠ ∞ :=
  measure_union_series_ne_top
    simpleRandomWalk_sourceThetaSmallLevelPayment_series_ne_top
    (measure_union_series_ne_top
      simpleRandomWalk_validStepWalk_compl_series_ne_top
      (measure_union_series_ne_top
        (simpleRandomWalk_lateRankCutoff_series_ne_top hProp13 rank hrank)
        (simpleRandomWalk_candidateLocalSourceThetaPaymentAtRank_series_ne_top
          hProp13 data t rank hrank)))

end

end Erdos1165.HLOZRawOrientedSourceThetaPayment
