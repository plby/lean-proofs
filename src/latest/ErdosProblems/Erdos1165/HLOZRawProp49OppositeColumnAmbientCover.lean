/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZRawProp49CanonicalAmbientCover

/-!
# Opposite-column Proposition 4.9 ambient coverage

Horizontal reflection turns an opposite dominant endpoint into a canonical
base for the paired column tiling.  This file proves that an unpaid raw path
belongs to the corresponding transported Proposition 4.9 candidate row.
The target support budget is derived from the complement of the literal
transported source/Theta payment, not from an unjustified reverse cardinal
comparison.
-/

open Set

namespace Erdos1165.HLOZRawProp49OppositeColumnAmbientCover

open ExternalProposition44 HLOZAllTilingSourceTransportScreen
open HLOZCandidateLocalLazyCap HLOZPathEvents
open HLOZGapRandomClockScreen
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49PathCoverage
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open HLOZRawProp49CanonicalAmbientCover
open HLOZRawProp49SourceCardinality HLOZRawProp49UnpaidProfile
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceCorrectFullGapClosure HLOZSourceEndpointTransportTable
open HLOZSourceCorrectFilteredTransitions
open HLOZSourceOrientedThetaRankPayment
open HLOZSourceOrientedThetaSourcePaymentSeries
open HLOZSourceOrientedThetaTransportPayment
open HLOZSourceOrientedThetaTransportGeometry
open HLOZSourceOrientedThetaWindowSplit
open HLOZSourceTransportCoordinateMass
open HLOZSourceTransportStoppedCandidateFamily
open HLOZThetaOneSourceShift HLOZThetaSourceBalance
open HLOZTransportedCanonicalProp49Row
open LazyDecomposition ScreeningInstantiation SpatialInsertionFiber
open TilingLazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingShellZeroAllCreationTraceBridge TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition
open HLOZTilingEndpointBandExtraction

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem not_isTilingBase_of_dominantEndpointClass_opposite
    {t : DominoTiling} {x : Point}
    (hclass : dominantEndpointClass t x = .opposite) :
    ¬ IsTilingBase t x := by
  intro hbase
  simp [dominantEndpointClass, hbase] at hclass

private theorem oppositeBandSource_mem_payment
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ}
    {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBandsAtRank m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank)
    {s : WalkPath}
    (hs : s ∈ transportedBandSourceEvent t o .opposite m band) :
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
    {t : DominoTiling} {o : Orientation} {rank m : ℕ} {s : WalkPath}
    (hs : s ∈ transportedRestrictedThetaSourceOnTimeEvent
      t o .opposite m rank) :
    s ∈ allTilingRestrictedThetaPaymentAtRank t rank m := by
  cases o <;>
    simp only [allTilingRestrictedThetaPaymentAtRank] at hs ⊢ <;> aesop

/-- The target support of an unpaid opposite row is small.  If it were
large, the exact target source-or-restricted-Theta dichotomy would put the
original path back in its excluded rank payment. -/
theorem targetSourceSupport_card_le_initialBudget_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ} {a : GapScale}
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (hrank : 0 < rank) (hrank_le : rank ≤ 3) (ha : a ∈ lowGapMesh)
    (htargetReach : ReachesThreshold
      (sourceTransportPath t .opposite s) m rank)
    (htargetClock : creationTimeNat m rank
        (sourceTransportPath t .opposite s) ≤ hlozCutoff44 m)
    (htargetD : tilingDEtaAtCreation
      (sourceTransportTargetTiling t .opposite) m rank (shellWidth48 m)
        (m - shellWidth48 m) (sourceTransportPath t .opposite s))
    (htargetNext : thresholdCount (sourceTransportPath t .opposite s)
      (creationTimeNat m rank (sourceTransportPath t .opposite s))
        (m + 1) = 0) :
    (SourceSupportAt (sourceTransportTargetTiling t .opposite)
      (sourceTransportTargetOrientation t o .opposite) m
      (sourceTransportPath t .opposite s)
      (creationTimeNat m rank (sourceTransportPath t .opposite s))).card ≤
        initialBudget48 m := by
  by_contra hcard
  have hcard' : orientedSourceCut48 m <
      (orientedTilingVTwoAtCreation
        (sourceTransportTargetTiling t .opposite)
        (sourceTransportTargetOrientation t o .opposite)
        m rank (shellWidth48 m) (sourceTransportPath t .opposite s)).card := by
    have hcut : orientedSourceCut48 m ≤ initialBudget48 m :=
      Nat.div_le_self _ _
    simpa only [SourceSupportAt, orientedShellZeroSourceSupportAt,
      orientedTilingVTwoAtCreation] using hcut.trans_lt (Nat.lt_of_not_ge hcard)
  obtain ⟨band, hband, _hscale⟩ := exists_sourceProductEndpointBandAtRank
    m (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank a
      hrank hrank_le ha
  have hdichotomy := mem_transportedBandSource_or_restrictedTheta
    (t := t) (o := o) (cls := .opposite) (m := m) (k := rank)
      (band := band) (s := s) htargetReach
      (Finset.mem_filter.mp hband).2 htargetClock htargetD htargetNext hcard'
  apply hprofile.source_theta_good
  rcases hdichotomy with hsource | htheta
  · exact Or.inl (oppositeBandSource_mem_payment hband hsource)
  · exact Or.inr (Or.inl (transportedTheta_mem_payment htheta))

/-- Outside the same unpaid rank event, the target restricted source-Theta
set is empty. -/
theorem targetRestrictedTheta_eq_empty_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ} {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (htargetReach : ReachesThreshold
      (sourceTransportPath t .opposite s) m rank)
    (htargetClock : creationTimeNat m rank
        (sourceTransportPath t .opposite s) ≤ hlozCutoff44 m) :
    orientedRestrictedThetaSourceAtCreation
      (sourceTransportTargetTiling t .opposite)
      (sourceTransportTargetOrientation t o .opposite)
      m rank (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) (sourceTransportPath t .opposite s) = ∅ := by
  by_contra hne
  have htheta : s ∈ transportedRestrictedThetaSourceOnTimeEvent
      t o .opposite m rank :=
    ⟨htargetReach, htargetClock, Finset.nonempty_iff_ne_empty.mpr hne⟩
  exact hprofile.source_theta_good
    (Or.inr (Or.inl (transportedTheta_mem_payment htheta)))

/-- An unpaid opposite endpoint of a column tiling is covered by the
transported ambient Proposition 4.9 row. -/
theorem mem_targetAmbientPreimage_opposite_column_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} (ht : IsColumnTiling t)
    {o : Orientation} {rank m : ℕ}
    (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (candidate : Point)
    (hclass : dominantEndpointClass t candidate = .opposite)
    (horientation : OrientationCompatible o candidate)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner t candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ sourceTransportPreimage t .opposite
      (targetAmbientFamily t o .opposite m rank a low hm hrank hwindow
        harithmetic hexternalArithmetic).someCandidate := by
  rcases hprofile.on_time_profile with
    ⟨N, hcreation, hnext, _hD, hsep, hclock⟩
  have hcreationClock : creationTimeNat m rank s = N :=
    creationTimeNat_eq_of_creation hcreation
  have hpathEq : sourceTransportPath t .opposite s =
      horizontalReflectPath s := by
    cases t <;> simp_all [IsColumnTiling, sourceTransportPath]
  have htilingEq : sourceTransportTargetTiling t .opposite =
      reflectedColumnTiling t := by
    cases t <;> simp_all [IsColumnTiling, sourceTransportTargetTiling,
      reflectedColumnTiling]
  have horientationEq : sourceTransportTargetOrientation t o .opposite = o := by
    cases t <;> simp_all [IsColumnTiling, sourceTransportTargetOrientation]
  let target := sourceTransportPath t .opposite s
  let targetTiling := sourceTransportTargetTiling t .opposite
  let targetOrientation := sourceTransportTargetOrientation t o .opposite
  let targetCandidate := horizontalReflectPoint candidate
  have htargetCreation : ThresholdCreation target m rank N := by
    change ThresholdCreation (sourceTransportPath t .opposite s) m rank N
    rw [hpathEq]
    exact (thresholdCreation_horizontalReflectPath s m rank N (by omega)).2 hcreation
  have htargetClockEq : creationTimeNat m rank target = N :=
    creationTimeNat_eq_of_creation htargetCreation
  have htargetReach : ReachesThreshold target m rank :=
    ⟨N, htargetCreation.1⟩
  have htargetNext : thresholdCount target
      (creationTimeNat m rank target) (m + 1) = 0 := by
    rw [htargetClockEq]
    change thresholdCount (sourceTransportPath t .opposite s) N (m + 1) = 0
    rw [hpathEq, thresholdCount_horizontalReflectPath]
    · exact hnext
    · omega
  have htargetD : tilingDEtaAtCreation targetTiling m rank
      (shellWidth48 m) (m - shellWidth48 m) target := by
    change tilingDEtaAtCreation (sourceTransportTargetTiling t .opposite)
      m rank (shellWidth48 m) (m - shellWidth48 m)
        (sourceTransportPath t .opposite s)
    rw [htilingEq, hpathEq]
    exact tilingDEtaAtCreation_horizontalReflectPath ht s (by omega) hrank
      rfl hcreation hnext hsep
  have htargetClock : creationTimeNat m rank target ≤ hlozCutoff44 m := by
    rw [htargetClockEq]
    simpa only
      [HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
      using hclock
  have hcard : (SourceSupportAt targetTiling targetOrientation m target
      (creationTimeNat m rank target)).card ≤ initialBudget48 m := by
    exact targetSourceSupport_card_le_initialBudget_of_unpaid
      (t := t) (o := o) (a := a) hprofile hrank hrank_le ha htargetReach
        htargetClock htargetD htargetNext
  have htargetNotTheta := targetRestrictedTheta_eq_empty_of_unpaid
    (t := t) (o := o) hprofile htargetReach htargetClock
  have htargetTheta : orientedTilingThetaAtCreation targetTiling
      targetOrientation m rank
      (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) target = ∅ := by
    apply orientedTilingThetaAtCreation_eq_empty_of_restrictedSource_empty
    · exact htargetNext
    · exact htargetNotTheta
  have htargetValid : target ∈ validStepWalk := by
    have hs : trajectory (stepsOfWalk s) = s := hprofile.valid
    change sourceTransportPath t .opposite s ∈ validStepWalk
    rw [hpathEq, ← hs, horizontalReflectPath_trajectory]
    exact trajectory_mem_validStepWalk _
  have hnotBase : ¬ IsTilingBase t candidate :=
    not_isTilingBase_of_dominantEndpointClass_opposite hclass
  have htargetBase : IsTilingBase targetTiling targetCandidate :=
    by
      change IsTilingBase (sourceTransportTargetTiling t .opposite)
        (horizontalReflectPoint candidate)
      rw [htilingEq]
      exact (isTilingBase_reflectedColumn_iff_not ht candidate).2 hnotBase
  have htargetClass : dominantEndpointClass targetTiling targetCandidate =
      .canonical := by
    simp [dominantEndpointClass, htargetBase]
  have htargetOrientation : OrientationCompatible targetOrientation
      targetCandidate := by
    change OrientationCompatible
      (sourceTransportTargetOrientation t o .opposite)
        (horizontalReflectPoint candidate)
    rw [horientationEq]
    exact (orientationCompatible_horizontalReflectPoint_iff o candidate).2
      horientation
  have htargetDominance : localTime target (creationTimeNat m rank target)
        (tilingPartner targetTiling targetCandidate) ≤
      localTime target (creationTimeNat m rank target) targetCandidate := by
    rw [htargetClockEq]
    change localTime (sourceTransportPath t .opposite s) N
        (tilingPartner (sourceTransportTargetTiling t .opposite)
          (horizontalReflectPoint candidate)) ≤
      localTime (sourceTransportPath t .opposite s) N
        (horizontalReflectPoint candidate)
    rw [hpathEq, htilingEq, tilingPartner_reflectedColumn ht,
      localTime_horizontalReflectPath, localTime_horizontalReflectPath]
    simpa only [hcreationClock] using hdominance
  have htargetNarrow : localTime target (creationTimeNat m rank target)
      targetCandidate ∈ prop49NarrowTotalWindow m a := by
    rw [htargetClockEq]
    change localTime (sourceTransportPath t .opposite s) N
      (horizontalReflectPoint candidate) ∈ prop49NarrowTotalWindow m a
    rw [hpathEq, localTime_horizontalReflectPath]
    simpa only [hcreationClock] using hnarrow
  have hcandidate := dominantEndpoint_mem_sourceSupportAt
    (t := targetTiling) (o := targetOrientation) (m := m) (k := rank)
      (a := a)
      hwindow harithmetic htargetClass htargetOrientation htargetDominance
        htargetNarrow
  have htargetMem :=
    mem_sourceProp49StoppedHistoryCandidateFamily_univ_of_path
      (t := targetTiling) (o := targetOrientation) a low hm hrank hwindow
        harithmetic hexternalArithmetic htargetValid htargetReach hcard
        htargetTheta targetCandidate hcandidate htargetNarrow
  unfold sourceTransportPreimage targetAmbientFamily
  dsimp only [target, targetTiling, targetOrientation] at htargetMem ⊢
  exact htargetMem

private theorem mem_transportedAmbientFamily_opposite_column_iff
    (t : DominoTiling) (ht : IsColumnTiling t)
    (o : Orientation) (m rank : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hrank : 0 < rank)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (s : WalkPath) :
    s ∈ (transportedAmbientFamily t o .opposite m rank a low hm hrank hwindow
        harithmetic hexternalArithmetic).someCandidate ↔
      s ∈ sourceTransportPreimage t .opposite
        (targetAmbientFamily t o .opposite m rank a low hm hrank hwindow
          harithmetic hexternalArithmetic).someCandidate := by
  cases t with
  | checker d => contradiction
  | evenColumns =>
      change s ∈ (stoppedHistoryCandidateFamilySourceTransport
          .evenColumns .opposite
          (targetAmbientFamily .evenColumns o .opposite m rank a low hm hrank
            hwindow harithmetic hexternalArithmetic)
          (targetAmbientNear_measurable .evenColumns o .opposite m rank a low
            hm hrank hwindow harithmetic
              hexternalArithmetic)).someCandidate ↔ _
      rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport]
  | oddColumns =>
      change s ∈ (stoppedHistoryCandidateFamilySourceTransport
          .oddColumns .opposite
          (targetAmbientFamily .oddColumns o .opposite m rank a low hm hrank
            hwindow harithmetic hexternalArithmetic)
          (targetAmbientNear_measurable .oddColumns o .opposite m rank a low
            hm hrank hwindow harithmetic
              hexternalArithmetic)).someCandidate ↔ _
      rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport]

/-- The same statement expressed as membership in the finite-table
transported ambient family. -/
theorem mem_transportedAmbientFamily_opposite_column_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} (ht : IsColumnTiling t)
    {o : Orientation} {rank m : ℕ}
    (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (candidate : Point)
    (hclass : dominantEndpointClass t candidate = .opposite)
    (horientation : OrientationCompatible o candidate)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner t candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (transportedAmbientFamily t o .opposite m rank a low hm hrank
      hwindow harithmetic hexternalArithmetic).someCandidate := by
  have hpreimage := mem_targetAmbientPreimage_opposite_column_of_unpaid
    ht a low hm hrank hrank_le ha hwindow harithmetic hexternalArithmetic
      hprofile candidate hclass horientation hdominance hnarrow
  exact (mem_transportedAmbientFamily_opposite_column_iff t ht o m rank a low
    hm hrank hwindow harithmetic hexternalArithmetic s).2 hpreimage

end

end Erdos1165.HLOZRawProp49OppositeColumnAmbientCover
