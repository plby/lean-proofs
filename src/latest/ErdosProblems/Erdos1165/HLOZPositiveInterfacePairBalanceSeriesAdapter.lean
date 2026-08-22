/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZConcreteSourceThetaSeriesAdapter
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairBalancedSeries
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowObstructionBand

/-!
# Concrete balance-series adapter for the exact-pair split

The harmonic exact-pair carrier is already summable.  This adapter reduces
the final concrete positive-interface balance record to the three rankwise
series of genuinely unbalanced histories.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairBalanceSeriesAdapter

open HLOZConcreteFullBetaProductData
open HLOZConcreteSourceThetaSeriesAdapter
open HLOZNoLazyFullBetaProductBranch
open HLOZPathEvents
open HLOZPositiveInterfacePairBalancedSeries
open HLOZPositiveInterfacePairWindowObstructionBand
open HLOZRawFullGapProductPromotion
open HLOZSourceCorrectFullGapClosure
open HLOZUpperEstimates

noncomputable section

abbrev DominoTiling := Tilings.Tiling

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

/-- Balanced harmonic payment together with the exceptional arithmetic
complement at one old-favorite rank. -/
def positiveInterfacePairBalancePaymentAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m ∪
    positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank data t rank m

/-- The three old-favorite ranks used by the final product recurrence. -/
def concretePositiveInterfacePairBalancePayment
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  positiveInterfacePairBalancePaymentAtRank concreteFullBetaProductData
      t 1 m ∪
    (positiveInterfacePairBalancePaymentAtRank concreteFullBetaProductData
        t 2 m ∪
      positiveInterfacePairBalancePaymentAtRank concreteFullBetaProductData
        t 3 m)

theorem positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) {s : WalkPath}
    (hprofile : s ∈ positiveInterfaceCreationNoNextProfileEvent m rank)
    (hremainder : s ∈
      positiveInterfaceBalanceRemainderUnionAtRank data t rank m) :
    s ∈ positiveInterfacePairBalancePaymentAtRank data t rank m :=
  positiveInterfaceCreationProfile_inter_balanceRemainder_subset_pair_split
    data t rank m ⟨hprofile, hremainder⟩

private theorem candidateLocal_rankOne_mem_creationProfile
    {t : DominoTiling} {m : ℕ} {s : WalkPath}
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m (concreteFullBetaProductData.externalThreshold m)) :
    s ∈ positiveInterfaceCreationNoNextProfileEvent m 1 := by
  by_cases hm : 0 < m
  · rcases onTimeCandidateLocalProductBeta_rankOne_creationSourceData hm hs with
      ⟨n, hcreation, hnext, _hD⟩
    simp only [positiveInterfaceCreationNoNextProfileEvent, if_pos hm,
      Set.mem_setOf_eq]
    exact ⟨n, hcreation, hnext⟩
  · simp [positiveInterfaceCreationNoNextProfileEvent, hm]

private theorem candidateLocal_rankTwo_mem_creationProfile
    {t : DominoTiling} {m : ℕ} {s : WalkPath}
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m (concreteFullBetaProductData.externalThreshold m)) :
    s ∈ positiveInterfaceCreationNoNextProfileEvent m 2 := by
  by_cases hm : 0 < m
  · rcases onTimeCandidateLocalProductBeta_rankTwo_creationSourceData hm hs with
      ⟨n, hcreation, hnext, _hD⟩
    simp only [positiveInterfaceCreationNoNextProfileEvent, if_pos hm,
      Set.mem_setOf_eq]
    exact ⟨n, hcreation, hnext⟩
  · simp [positiveInterfaceCreationNoNextProfileEvent, hm]

private theorem candidateLocal_rankThree_mem_creationProfile
    {t : DominoTiling} {m : ℕ} {s : WalkPath}
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m (concreteFullBetaProductData.externalThreshold m)) :
    s ∈ positiveInterfaceCreationNoNextProfileEvent m 3 := by
  by_cases hm : 0 < m
  · rcases onTimeCandidateLocalProductBeta_rankThree_creationSourceData hm hs with
      ⟨n, hcreation, hnext, _hD⟩
    simp only [positiveInterfaceCreationNoNextProfileEvent, if_pos hm,
      Set.mem_setOf_eq]
    exact ⟨n, hcreation, hnext⟩
  · simp [positiveInterfaceCreationNoNextProfileEvent, hm]

private theorem raw_mem_creationProfile
    {m rank : ℕ} {s : WalkPath}
    (hprofile : ∃ n, ThresholdCreation s m rank n ∧
      thresholdCount s n (m + 1) = 0) :
    s ∈ positiveInterfaceCreationNoNextProfileEvent m rank := by
  by_cases hm : 0 < m
  · simpa [positiveInterfaceCreationNoNextProfileEvent, hm] using hprofile
  · simp [positiveInterfaceCreationNoNextProfileEvent, hm]

theorem candidateLocalProductPositiveInterfaceBalanceRemainderEvent_subset_payment
    (t : DominoTiling) (m : ℕ) :
    candidateLocalProductPositiveInterfaceBalanceRemainderEvent
        concreteFullBetaProductData t m ⊆
      concretePositiveInterfacePairBalancePayment t m := by
  rintro s (h₁ | h₂ | h₃)
  · exact Or.inl
      (positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
        concreteFullBetaProductData t 1 m
        (candidateLocal_rankOne_mem_creationProfile h₁.1) h₁.2)
  · exact Or.inr (Or.inl
      (positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
        concreteFullBetaProductData t 2 m
        (candidateLocal_rankTwo_mem_creationProfile h₂.1) h₂.2))
  · exact Or.inr (Or.inr
      (positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
        concreteFullBetaProductData t 3 m
        (candidateLocal_rankThree_mem_creationProfile h₃.1) h₃.2))

theorem firstRawBalanceRemainder_subset_payment
    (t : DominoTiling) (m : ℕ)
    (a : HLOZRawFullGapProductPromotion.GapTriple) :
    firstRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank
          concreteFullBetaProductData t 1 m ⊆
      concretePositiveInterfacePairBalancePayment t m := by
  intro s hs
  exact Or.inl
    (positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
      concreteFullBetaProductData t 1 m
      (raw_mem_creationProfile
        (firstRawCandidatePreliminary_creationProfile hs.1)) hs.2)

theorem secondRawBalanceRemainder_subset_payment
    (t : DominoTiling) (m : ℕ)
    (a : HLOZRawFullGapProductPromotion.GapTriple) :
    secondRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank
          concreteFullBetaProductData t 2 m ⊆
      concretePositiveInterfacePairBalancePayment t m := by
  intro s hs
  exact Or.inr (Or.inl
    (positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
      concreteFullBetaProductData t 2 m
      (raw_mem_creationProfile
        (secondRawCandidatePreliminary_creationProfile hs.1)) hs.2))

theorem thirdRawBalanceRemainder_subset_payment
    (t : DominoTiling) (m : ℕ)
    (a : HLOZRawFullGapProductPromotion.GapTriple) :
    thirdRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank
          concreteFullBetaProductData t 3 m ⊆
      concretePositiveInterfacePairBalancePayment t m := by
  intro s hs
  exact Or.inr (Or.inr
    (positiveInterfaceBalanceRemainderUnionAtRank_subset_payment
      concreteFullBetaProductData t 3 m
      (raw_mem_creationProfile
        (thirdRawCandidatePreliminary_creationProfile hs.1)) hs.2))

theorem simpleRandomWalk_positiveInterfacePairBalancePaymentAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ)
    (hunbalanced : ∑' m, simpleRandomWalk
      (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
        data t rank m) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (positiveInterfacePairBalancePaymentAtRank data t rank m) ≠ ∞ :=
  measure_union_series_ne_top
    (simpleRandomWalk_positiveInterfaceBalancedPairPaymentUnionAtRank_series_ne_top
      data t rank)
    hunbalanced

/-- Construct the final concrete balance record once the three genuinely
unbalanced rankwise series have been paid. -/
def concretePositiveInterfaceBalanceSeriesData_of_unbalanced
    (hunbalancedOne : ∀ t : DominoTiling,
      ∑' m, simpleRandomWalk
        (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
          concreteFullBetaProductData t 1 m) ≠ ∞)
    (hunbalancedTwo : ∀ t : DominoTiling,
      ∑' m, simpleRandomWalk
        (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
          concreteFullBetaProductData t 2 m) ≠ ∞)
    (hunbalancedThree : ∀ t : DominoTiling,
      ∑' m, simpleRandomWalk
        (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
          concreteFullBetaProductData t 3 m) ≠ ∞) :
    ConcretePositiveInterfaceBalanceSeriesData where
  balance := concretePositiveInterfacePairBalancePayment
  candidateLocal_subset :=
    candidateLocalProductPositiveInterfaceBalanceRemainderEvent_subset_payment
  firstRaw_subset := firstRawBalanceRemainder_subset_payment
  secondRaw_subset := secondRawBalanceRemainder_subset_payment
  thirdRaw_subset := thirdRawBalanceRemainder_subset_payment
  series := by
    intro t
    exact measure_union_series_ne_top
      (simpleRandomWalk_positiveInterfacePairBalancePaymentAtRank_series_ne_top
        concreteFullBetaProductData t 1 (hunbalancedOne t))
      (measure_union_series_ne_top
        (simpleRandomWalk_positiveInterfacePairBalancePaymentAtRank_series_ne_top
          concreteFullBetaProductData t 2 (hunbalancedTwo t))
        (simpleRandomWalk_positiveInterfacePairBalancePaymentAtRank_series_ne_top
          concreteFullBetaProductData t 3 (hunbalancedThree t)))

/-- The exact-pair construction supplies the complete positive-interface
balance series required by the corrected product upper assembly. -/
def concretePositiveInterfaceBalanceSeriesData :
    ConcretePositiveInterfaceBalanceSeriesData :=
  concretePositiveInterfaceBalanceSeriesData_of_unbalanced
    (fun t ↦
      simpleRandomWalk_positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_series_ne_top
        t 1)
    (fun t ↦
      simpleRandomWalk_positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_series_ne_top
        t 2)
    (fun t ↦
      simpleRandomWalk_positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_series_ne_top
        t 3)

end

end Erdos1165.HLOZPositiveInterfacePairBalanceSeriesAdapter
