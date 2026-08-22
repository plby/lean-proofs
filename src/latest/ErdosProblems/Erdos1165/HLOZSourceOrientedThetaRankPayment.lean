/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalLazyCap
import ErdosProblems.Erdos1165.HLOZNoLazyFullBetaProductBranch
import ErdosProblems.Erdos1165.HLOZRawFullGapProductPromotion
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaTransportGeometry

/-!
# Rankwise oriented source and Theta payment

The candidate-local product branch already carries the four genuine creation
times, their domino separation, and an on-time terminal clock.  This module
uses those deterministic facts to route each of the four orientation/spatial
classes into the literal transported source, the physical restricted-Theta
payment, or the single checker-origin payment.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaRankPayment

open ExternalProposition44 HLOZAllTilingSourceTransportScreen
open HLOZCandidateLocalLazyCap
open HLOZCheckerOriginShiftPayment HLOZNoLazyFullBetaProductBranch
open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion HLOZRawShellCreationBridge
open HLOZShellZeroReplacementWindows HLOZSourceCorrectFullGapClosure
open HLOZSourceCorrectFilteredTransitions
open HLOZSourceEndpointTransportTable HLOZSourceOrientedThetaTransportGeometry
open HLOZSourceOrientedThetaTransportPayment HLOZThetaOneSourceShift
open HLOZThetaSourceBalance LazyDecomposition PreStoppingSpatialLaw
open ScreeningInstantiation SpatialInsertionFiber
open HLOZTilingGapBandExtraction
open TilingOrientedShellZeroSourcePartition TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The four transported physical restricted-Theta screens at one creation
rank.  Empty/impossible table rows are harmless and allow one uniform event
for all six tilings. -/
def allTilingRestrictedThetaPaymentAtRank
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  (transportedRestrictedThetaSourceOnTimeEvent t .even .canonical m rank ∪
      transportedRestrictedThetaSourceOnTimeEvent t .shifted .canonical m rank) ∪
    (transportedRestrictedThetaSourceOnTimeEvent t .even .opposite m rank ∪
      transportedRestrictedThetaSourceOnTimeEvent t .shifted .opposite m rank)

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

theorem simpleRandomWalk_allTilingRestrictedThetaPaymentAtRank_series_ne_top
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (allTilingRestrictedThetaPaymentAtRank t rank m) ≠ ∞ := by
  apply measure_union_series_ne_top
  · exact measure_union_series_ne_top
      (simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent_series_ne_top
        t .even .canonical rank hrank)
      (simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent_series_ne_top
        t .shifted .canonical rank hrank)
  · exact measure_union_series_ne_top
      (simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent_series_ne_top
        t .even .opposite rank hrank)
      (simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent_series_ne_top
        t .shifted .opposite rank hrank)

/-- Complete rank payment after the raw four-way creation-source split. -/
def candidateLocalSourceThetaPaymentAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  allTilingSourcePaymentAtRank data t rank m ∪
    (allTilingRestrictedThetaPaymentAtRank t rank m ∪
      allTilingCheckerOriginShiftPaidEvent t rank m)

theorem simpleRandomWalk_candidateLocalSourceThetaPaymentAtRank_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (candidateLocalSourceThetaPaymentAtRank data t rank m) ≠ ∞ := by
  apply measure_union_series_ne_top
  · exact simpleRandomWalk_allTilingSourcePaymentAtRank_series_ne_top
      data t rank
  · exact measure_union_series_ne_top
      (simpleRandomWalk_allTilingRestrictedThetaPaymentAtRank_series_ne_top
        t rank hrank)
      (simpleRandomWalk_allTilingCheckerOriginShiftPaidEvent_series_ne_top
        hProp13 t rank hrank)

private theorem canonicalBandSource_mem_payment
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ}
    {band : RandomClockBand} (hband : band ∈
      sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
        (data.externalThreshold m) rank)
    {s : WalkPath} (hs : s ∈ canonicalBandSourceEvent t o m band) :
    s ∈ allTilingSourcePaymentAtRank data t rank m := by
  have hu := canonicalBandSourceEvent_subset_unionAtRank
    data t o rank m band hband hs
  cases t <;> cases o <;> simp only [allTilingSourcePaymentAtRank] <;> aesop

private theorem oppositeBandSource_mem_payment
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ}
    {band : RandomClockBand} (hband : band ∈
      sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
        (data.externalThreshold m) rank)
    {s : WalkPath} (hs : s ∈ transportedBandSourceEvent t o .opposite m band) :
    s ∈ allTilingSourcePaymentAtRank data t rank m := by
  cases t with
  | checker d =>
      have hu := shiftedCheckerBandSourceEvent_subset_unionAtRank
        data d o rank m band hband hs
      cases o <;> simp only [allTilingSourcePaymentAtRank] <;> aesop
  | evenColumns =>
      have hu := reflectedColumnBandSourceEvent_subset_unionAtRank
        data .evenColumns o rank m band hband hs
      cases o <;> simp only [allTilingSourcePaymentAtRank] <;> aesop
  | oddColumns =>
      have hu := reflectedColumnBandSourceEvent_subset_unionAtRank
        data .oddColumns o rank m band hband hs
      cases o <;> simp only [allTilingSourcePaymentAtRank] <;> aesop

private theorem transportedTheta_mem_payment
    {t : DominoTiling} {o : Orientation} {cls : DominantEndpointClass}
    {rank m : ℕ} {s : WalkPath}
    (hs : s ∈ transportedRestrictedThetaSourceOnTimeEvent t o cls m rank) :
    s ∈ allTilingRestrictedThetaPaymentAtRank t rank m := by
  cases o <;> cases cls <;>
    simp only [allTilingRestrictedThetaPaymentAtRank] <;> aesop

/-- One band/class route from a genuine original creation profile.  The
target source profile is constructed internally under the one-step or
reflection transport. -/
theorem orientedCreationClass_mem_source_theta_or_checker
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    {rank m N : ℕ} {band : RandomClockBand} {s : WalkPath}
    (hm : 2 ≤ m) (hrank : 0 < rank)
    (hvalid : s ∈ validStepWalk)
    (hband : band ∈ sourceProductEndpointBandsAtRank m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank)
    (hcreation : ThresholdCreation s m rank N)
    (hnext : thresholdCount s N (m + 1) = 0)
    (hD : tilingDEtaAtCreation t m rank (shellWidth48 m)
      (m - shellWidth48 m) s)
    (hsep : TilingThresholdDominoSeparated t s N m)
    (hclock : N ≤ levelCutoffTime upperTailDelta m)
    (hcardCanonical : cls = .canonical → orientedSourceCut48 m <
      (orientedCanonicalDominantNearBasesAtCreation t o m rank
        (shellWidth48 m) s).card)
    (hcardOpposite : cls = .opposite → orientedSourceCut48 m <
      (orientedOppositeDominantNearEndpointsAtCreation t o m rank
        (shellWidth48 m) s).card) :
    s ∈ candidateLocalSourceThetaPaymentAtRank data t rank m := by
  have hrankBand : band.oldRank = rank := (Finset.mem_filter.mp hband).2
  have hclock44 : N ≤ hlozCutoff44 m := by
    simpa only [HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
      using hclock
  cases cls with
  | canonical =>
      have hcreationClock : creationTimeNat m rank s = N :=
        creationTimeNat_eq_of_creation hcreation
      have hcard : orientedSourceCut48 m <
          (orientedTilingVTwoAtCreation t o m rank (shellWidth48 m) s).card := by
        rw [← orientedCanonicalDominantNearBasesAtCreation_eq_vTwo
          t o m rank (shellWidth48 m) s]
        · exact hcardCanonical rfl
        · simpa only [hcreationClock] using hnext
      have hdichotomy := mem_transportedBandSource_or_restrictedTheta
        (t := t) (o := o) (cls := .canonical) (m := m) (k := rank)
        (band := band) (s := s)
        (by simpa only [sourceTransportPath, id_eq] using
          (show ReachesThreshold s m rank from ⟨N, hcreation.1⟩))
        hrankBand
        (by simpa only [sourceTransportPath, id_eq, hcreationClock] using hclock44)
        (by simpa only [sourceTransportTargetTiling, sourceTransportPath,
          id_eq] using hD)
        (by simpa only [sourceTransportPath, id_eq, hcreationClock] using hnext)
        (by simpa only [sourceTransportTargetTiling,
          sourceTransportTargetOrientation, sourceTransportPath, id_eq] using hcard)
      rcases hdichotomy with hsource | htheta
      · exact Or.inl (canonicalBandSource_mem_payment hband hsource)
      · exact Or.inr (Or.inl (transportedTheta_mem_payment htheta))
  | opposite =>
      cases t with
      | checker d =>
          let omega : StepPath := stepsOfWalk s
          have homega : trajectory omega = s := hvalid
          have hcreationOmega : ThresholdCreation (trajectory omega) m rank N := by
            simpa only [homega] using hcreation
          have hnextOmega : thresholdCount (trajectory omega) N (m + 1) = 0 := by
            simpa only [homega] using hnext
          have hsepOmega : TilingThresholdDominoSeparated (.checker d)
              (trajectory omega) N m := by
            simpa only [homega] using hsep
          by_cases horigin : trajectory omega ∈
              checkerOriginShiftExceptionEvent d m rank (shellWidth48 m)
          · apply Or.inr
            apply Or.inr
            simpa only [homega, allTilingCheckerOriginShiftPaidEvent] using
              (checkerOriginShiftException_mem_paid_of_creation omega d hrank
                hcreationOmega hnextOmega horigin)
          · have hcardOriginal : orientedSourceCut48 m <
                (orientedOppositeDominantNearEndpointsAtCreation (.checker d) o
                  m rank (shellWidth48 m) (trajectory omega)).card := by
              simpa only [homega] using hcardOpposite rfl
            have hcard := lt_of_lt_of_le hcardOriginal
              (orientedOppositeChecker_card_le_shifted_vTwoAtCreation
                omega d o hm hrank hcreationOmega hnextOmega horigin)
            have horiginLT : localTime (trajectory omega) N 0 < m := by
              have h := not_mem_checkerOriginShiftExceptionEvent horigin
              rw [creationTimeNat_eq_of_creation hcreationOmega] at h
              exact h
            have hNpos := thresholdCreation_time_pos_of_two_le omega hm hrank
              hcreationOmega
            obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
            have hshiftCreation := thresholdCreation_oneStepRecenter omega n m rank
              (by omega) hcreationOmega
              (by simpa only [Nat.succ_eq_add_one] using horiginLT)
            have hshiftClock : creationTimeNat m rank
                (oneStepRecenter (trajectory omega)) = n :=
              creationTimeNat_eq_of_creation hshiftCreation
            have hshiftD := tilingDEtaAtCreation_oneStepRecenter omega d
              (w := shellWidth48 m) (low := m - shellWidth48 m) hm hrank
              rfl hcreationOmega hnextOmega hsepOmega
                (by simpa only [Nat.succ_eq_add_one] using horiginLT)
            have hshiftNext : thresholdCount (oneStepRecenter (trajectory omega))
                n (m + 1) = 0 := by
              rw [thresholdCount_oneStepRecenter_eq omega n (m + 1)
                (by omega)]
              · exact hnextOmega
              · exact (by simpa only [Nat.succ_eq_add_one] using
                  horiginLT.trans (Nat.lt_succ_self m))
            have hdichotomy := mem_transportedBandSource_or_restrictedTheta
              (t := .checker d) (o := o) (cls := .opposite)
              (m := m) (k := rank) (band := band) (s := trajectory omega)
              (by simpa only [sourceTransportPath, homega] using
                (show ReachesThreshold (oneStepRecenter (trajectory omega))
                    m rank from ⟨n, hshiftCreation.1⟩))
              hrankBand
              (by simpa only [sourceTransportPath, hshiftClock,
                  HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
                using Nat.le_trans (Nat.le_succ n) hclock)
              (by simpa only [sourceTransportTargetTiling, sourceTransportPath,
                  shiftedCheckerTarget, shiftedCheckerTiling] using hshiftD)
              (by simpa only [sourceTransportPath, hshiftClock] using hshiftNext)
              (by simpa only [sourceTransportTargetTiling,
                  sourceTransportTargetOrientation, sourceTransportPath,
                  shiftedCheckerTarget, shiftedCheckerTiling] using hcard)
            rcases hdichotomy with hsource | htheta
            · apply Or.inl
              apply oppositeBandSource_mem_payment hband
              simpa only [homega] using hsource
            · apply Or.inr
              apply Or.inl
              apply transportedTheta_mem_payment
              simpa only [homega] using htheta
      | evenColumns =>
          have hcard := lt_of_lt_of_le (hcardOpposite rfl)
            (orientedOppositeColumn_card_le_reflected_vTwoAtCreation
              (t := .evenColumns) (by trivial) o s (by omega) hcreation hnext)
          have hreflectCreation :=
            (thresholdCreation_horizontalReflectPath s m rank N (by omega)).2
              hcreation
          have hreflectClock : creationTimeNat m rank
              (horizontalReflectPath s) = N :=
            creationTimeNat_eq_of_creation hreflectCreation
          have hreflectD := tilingDEtaAtCreation_horizontalReflectPath
            (t := .evenColumns) (w := shellWidth48 m)
              (low := m - shellWidth48 m) (by trivial) s (by omega) hrank rfl
              hcreation hnext hsep
          have hreflectNext : thresholdCount (horizontalReflectPath s) N
              (m + 1) = 0 := by
            rw [thresholdCount_horizontalReflectPath s N (m + 1) (by omega)]
            exact hnext
          have hdichotomy := mem_transportedBandSource_or_restrictedTheta
            (t := .evenColumns) (o := o) (cls := .opposite)
            (m := m) (k := rank) (band := band) (s := s)
            (by simpa only [sourceTransportPath] using
              (show ReachesThreshold (horizontalReflectPath s) m rank from
                ⟨N, hreflectCreation.1⟩))
            hrankBand
            (by simpa only [sourceTransportPath, hreflectClock] using hclock44)
            (by simpa only [sourceTransportTargetTiling, sourceTransportPath,
                reflectedColumnTarget, reflectedColumnTiling] using hreflectD)
            (by simpa only [sourceTransportPath, hreflectClock] using hreflectNext)
            (by simpa only [sourceTransportTargetTiling,
                sourceTransportTargetOrientation, sourceTransportPath,
                reflectedColumnTiling] using hcard)
          rcases hdichotomy with hsource | htheta
          · exact Or.inl (oppositeBandSource_mem_payment hband hsource)
          · exact Or.inr (Or.inl (transportedTheta_mem_payment htheta))
      | oddColumns =>
          have hcard := lt_of_lt_of_le (hcardOpposite rfl)
            (orientedOppositeColumn_card_le_reflected_vTwoAtCreation
              (t := .oddColumns) (by trivial) o s (by omega) hcreation hnext)
          have hreflectCreation :=
            (thresholdCreation_horizontalReflectPath s m rank N (by omega)).2
              hcreation
          have hreflectClock : creationTimeNat m rank
              (horizontalReflectPath s) = N :=
            creationTimeNat_eq_of_creation hreflectCreation
          have hreflectD := tilingDEtaAtCreation_horizontalReflectPath
            (t := .oddColumns) (w := shellWidth48 m)
              (low := m - shellWidth48 m) (by trivial) s (by omega) hrank rfl
              hcreation hnext hsep
          have hreflectNext : thresholdCount (horizontalReflectPath s) N
              (m + 1) = 0 := by
            rw [thresholdCount_horizontalReflectPath s N (m + 1) (by omega)]
            exact hnext
          have hdichotomy := mem_transportedBandSource_or_restrictedTheta
            (t := .oddColumns) (o := o) (cls := .opposite)
            (m := m) (k := rank) (band := band) (s := s)
            (by simpa only [sourceTransportPath] using
              (show ReachesThreshold (horizontalReflectPath s) m rank from
                ⟨N, hreflectCreation.1⟩))
            hrankBand
            (by simpa only [sourceTransportPath, hreflectClock] using hclock44)
            (by simpa only [sourceTransportTargetTiling, sourceTransportPath,
                reflectedColumnTarget, reflectedColumnTiling] using hreflectD)
            (by simpa only [sourceTransportPath, hreflectClock] using hreflectNext)
            (by simpa only [sourceTransportTargetTiling,
                sourceTransportTargetOrientation, sourceTransportPath,
                reflectedColumnTiling] using hcard)
          rcases hdichotomy with hsource | htheta
          · exact Or.inl (oppositeBandSource_mem_payment hband hsource)
          · exact Or.inr (Or.inl (transportedTheta_mem_payment htheta))

private def CandidateLocalCreationProfile
    (t : DominoTiling) (m rank : ℕ) (s : WalkPath) : Prop :=
  ∃ time,
    ThresholdCreation s m rank time ∧
    thresholdCount s time (m + 1) = 0 ∧
    tilingDEtaAtCreation t m rank (shellWidth48 m)
      (m - shellWidth48 m) s ∧
    TilingThresholdDominoSeparated t s time m ∧
    time ≤ levelCutoffTime upperTailDelta m

private theorem candidateLocal_terminal_time_le_cutoff
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    ∀ {n : ℕ}, ThresholdCreation s m 4 n →
      n ≤ levelCutoffTime upperTailDelta m := by
  rcases hs.2 with ⟨p, _j, _hfull, _hbeta, _hexternal⟩
  intro n hn
  have htime : n = p.nTerminal :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hn p.terminalCreation
  rw [htime, ← p.terminalClock]
  exact HLOZGapRandomClockScreen.pathTruncatedLevelTime_le
    m 4 (levelCutoffTime upperTailDelta m) s

private theorem candidateLocal_rankOne_profile
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    CandidateLocalCreationProfile t m 1 s := by
  rcases hs.1.1.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, _hfailure⟩
  have htime : n₁ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₁ : thresholdCount s n₁ (m + 1) = 0 := by
    change thresholdCount s n₁ (m + 1) ≤
      thresholdCount s n₄ (m + 1) at hmono
    omega
  have hsep₁ := thresholdDominoSeparated_of_singleton (t := t)
    (thresholdSites_eq_singleton_at_first_creation h₁)
  exact ⟨n₁, h₁, hnext₁,
    tilingDEtaAtCreation_of_creation_of_dominoSeparated hm
      (by omega) rfl h₁ hnext₁ hsep₁,
    hsep₁, htime.le.trans (candidateLocal_terminal_time_le_cutoff hs h₄)⟩

private theorem candidateLocal_rankTwo_profile
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    CandidateLocalCreationProfile t m 2 s := by
  rcases hs.1.1.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, _hfailure⟩
  have htime : n₂ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₂ : thresholdCount s n₂ (m + 1) = 0 := by
    change thresholdCount s n₂ (m + 1) ≤
      thresholdCount s n₄ (m + 1) at hmono
    omega
  have hsep₂ := thresholdDominoSeparated_of_pair
    (thresholdSites_eq_pair_at_second_creation h₁ h₂) hsep.1
  exact ⟨n₂, h₂, hnext₂,
    tilingDEtaAtCreation_of_creation_of_dominoSeparated hm
      (by omega) rfl h₂ hnext₂ hsep₂,
    hsep₂, htime.le.trans (candidateLocal_terminal_time_le_cutoff hs h₄)⟩

private theorem candidateLocal_rankThree_profile
    {t : DominoTiling} {m externalThreshold : ℕ} {s : WalkPath}
    (hm : 0 < m)
    (hs : s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
      t m externalThreshold) :
    CandidateLocalCreationProfile t m 3 s := by
  rcases hs.1.1.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, _hfailure⟩
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
      (by omega) rfl h₃ hnext₃ hsep₃,
    hsep₃, htime.le.trans (candidateLocal_terminal_time_le_cutoff hs h₄)⟩

private theorem candidateLocal_sourceAtRank_subset_payment_of_profile
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (hm : 2 ≤ m) (hrank : 0 < rank)
    (hprofile : ∀ s ∈ onTimeCandidateLocalProductBetaLowGapExceptionalEvent
        t m (data.externalThreshold m),
      CandidateLocalCreationProfile t m rank s) :
    candidateLocalOrientedSourceEventAtRank data t rank m ⊆
      candidateLocalSourceThetaPaymentAtRank data t rank m := by
  rintro s ⟨hlocal, band, hband, hsource⟩
  have hrankBand : band.oldRank = rank := (Finset.mem_filter.mp hband).2
  rcases hprofile s hlocal with
    ⟨N, hcreation, hnext, hD, hsep, hclock⟩
  rcases hsource with ((h | h) | h) | h
  · exact orientedCreationClass_mem_source_theta_or_checker data t .even
      .canonical hm hrank hlocal.1.2 hband hcreation hnext hD hsep hclock
        (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
        (fun hbad ↦ nomatch hbad)
  · exact orientedCreationClass_mem_source_theta_or_checker data t .shifted
      .canonical hm hrank hlocal.1.2 hband hcreation hnext hD hsep hclock
        (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
        (fun hbad ↦ nomatch hbad)
  · exact orientedCreationClass_mem_source_theta_or_checker data t .even
      .opposite hm hrank hlocal.1.2 hband hcreation hnext hD hsep hclock
        (fun hbad ↦ nomatch hbad)
        (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)
  · exact orientedCreationClass_mem_source_theta_or_checker data t .shifted
      .opposite hm hrank hlocal.1.2 hband hcreation hnext hD hsep hclock
        (fun hbad ↦ nomatch hbad)
        (fun _ ↦ by simpa only [Set.mem_ofPred_eq, hrankBand] using h)

theorem candidateLocalOrientedSourceEventAtRank_one_subset_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (hm : 2 ≤ m) :
    candidateLocalOrientedSourceEventAtRank data t 1 m ⊆
      candidateLocalSourceThetaPaymentAtRank data t 1 m :=
  candidateLocal_sourceAtRank_subset_payment_of_profile data t 1 m hm
    (by omega) (fun _ hs ↦ candidateLocal_rankOne_profile (by omega) hs)

theorem candidateLocalOrientedSourceEventAtRank_two_subset_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (hm : 2 ≤ m) :
    candidateLocalOrientedSourceEventAtRank data t 2 m ⊆
      candidateLocalSourceThetaPaymentAtRank data t 2 m :=
  candidateLocal_sourceAtRank_subset_payment_of_profile data t 2 m hm
    (by omega) (fun _ hs ↦ candidateLocal_rankTwo_profile (by omega) hs)

theorem candidateLocalOrientedSourceEventAtRank_three_subset_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (hm : 2 ≤ m) :
    candidateLocalOrientedSourceEventAtRank data t 3 m ⊆
      candidateLocalSourceThetaPaymentAtRank data t 3 m :=
  candidateLocal_sourceAtRank_subset_payment_of_profile data t 3 m hm
    (by omega) (fun _ hs ↦ candidateLocal_rankThree_profile (by omega) hs)

/-- Finite prefix needed only because the checker recentering profile starts
at level two. -/
def sourceThetaSmallLevelPayment (m : ℕ) : Set WalkPath :=
  if 2 ≤ m then ∅ else Set.univ

theorem simpleRandomWalk_sourceThetaSmallLevelPayment_series_ne_top :
    ∑' m, simpleRandomWalk (sourceThetaSmallLevelPayment m) ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · exact ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _
  · intro m hm
    have hnot : ¬m < 2 := by
      simpa only [Finset.mem_range] using hm
    have hmge : 2 ≤ m := Nat.le_of_not_gt hnot
    simp [sourceThetaSmallLevelPayment, hmge]

def candidateLocalSourceThetaTotalPaymentAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  sourceThetaSmallLevelPayment m ∪
    candidateLocalSourceThetaPaymentAtRank data t rank m

theorem simpleRandomWalk_candidateLocalSourceThetaTotalPaymentAtRank_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (candidateLocalSourceThetaTotalPaymentAtRank data t rank m) ≠ ∞ :=
  measure_union_series_ne_top
    simpleRandomWalk_sourceThetaSmallLevelPayment_series_ne_top
    (simpleRandomWalk_candidateLocalSourceThetaPaymentAtRank_series_ne_top
      hProp13 data t rank hrank)

theorem candidateLocalOrientedSourceEventAtRank_one_subset_totalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalOrientedSourceEventAtRank data t 1 m ⊆
      candidateLocalSourceThetaTotalPaymentAtRank data t 1 m := by
  by_cases hm : 2 ≤ m
  · exact fun s hs ↦ Or.inr
      (candidateLocalOrientedSourceEventAtRank_one_subset_payment data t m hm hs)
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem candidateLocalOrientedSourceEventAtRank_two_subset_totalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalOrientedSourceEventAtRank data t 2 m ⊆
      candidateLocalSourceThetaTotalPaymentAtRank data t 2 m := by
  by_cases hm : 2 ≤ m
  · exact fun s hs ↦ Or.inr
      (candidateLocalOrientedSourceEventAtRank_two_subset_payment data t m hm hs)
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem candidateLocalOrientedSourceEventAtRank_three_subset_totalPayment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) :
    candidateLocalOrientedSourceEventAtRank data t 3 m ⊆
      candidateLocalSourceThetaTotalPaymentAtRank data t 3 m := by
  by_cases hm : 2 ≤ m
  · exact fun s hs ↦ Or.inr
      (candidateLocalOrientedSourceEventAtRank_three_subset_payment data t m hm hs)
  · exact fun _ _ ↦ Or.inl (by simp [sourceThetaSmallLevelPayment, hm])

theorem simpleRandomWalk_candidateLocalOrientedSourceEventAtRank_one_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank data t 1 m) ≠ ∞ :=
  ne_top_of_le_ne_top
    (simpleRandomWalk_candidateLocalSourceThetaTotalPaymentAtRank_series_ne_top
      hProp13 data t 1 (by omega))
    (ENNReal.tsum_le_tsum fun m ↦ measure_mono
      (candidateLocalOrientedSourceEventAtRank_one_subset_totalPayment data t m))

theorem simpleRandomWalk_candidateLocalOrientedSourceEventAtRank_two_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank data t 2 m) ≠ ∞ :=
  ne_top_of_le_ne_top
    (simpleRandomWalk_candidateLocalSourceThetaTotalPaymentAtRank_series_ne_top
      hProp13 data t 2 (by omega))
    (ENNReal.tsum_le_tsum fun m ↦ measure_mono
      (candidateLocalOrientedSourceEventAtRank_two_subset_totalPayment data t m))

theorem simpleRandomWalk_candidateLocalOrientedSourceEventAtRank_three_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank data t 3 m) ≠ ∞ :=
  ne_top_of_le_ne_top
    (simpleRandomWalk_candidateLocalSourceThetaTotalPaymentAtRank_series_ne_top
      hProp13 data t 3 (by omega))
    (ENNReal.tsum_le_tsum fun m ↦ measure_mono
      (candidateLocalOrientedSourceEventAtRank_three_subset_totalPayment data t m))

end

end Erdos1165.HLOZSourceOrientedThetaRankPayment
