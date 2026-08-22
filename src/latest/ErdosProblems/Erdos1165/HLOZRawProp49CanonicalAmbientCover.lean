/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49PathCoverage
import ErdosProblems.Erdos1165.HLOZRawProp49SourceCardinality
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Row

/-!
# Canonical Proposition 4.9 row coverage outside the raw payment

For a canonical dominant endpoint, the raw narrow-window candidate is
literally a coordinate of the original oriented source support.  Outside the
rank source/Theta payment, its exact source support is small and its complete
Theta set is empty.  Hence the path belongs to the unrestricted canonical
Proposition 4.9 stopped-candidate family.

This is an ambient-row statement.  It deliberately makes no claim that the
whole stopped source atom lies inside a later rankwise filtered past.
-/

open Set

namespace Erdos1165.HLOZRawProp49CanonicalAmbientCover

open ExternalProposition44 HLOZPathEvents
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49PathCoverage
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZRawProp49SourceCardinality HLOZRawProp49UnpaidProfile
open HLOZRawShellCreationBridge HLOZShellZeroReplacementWindows
open HLOZShellZeroExternalWindow HLOZSourceCorrectFullGapClosure
open HLOZSourceEndpointTransportTable
open HLOZSourceOrientedThetaRankPayment
open HLOZSourceOrientedThetaSourcePaymentSeries
open HLOZSourceOrientedThetaTransportGeometry
open HLOZSourceOrientedThetaTransportPayment
open HLOZSourceOrientedThetaWindowSplit
open HLOZThetaSourceBalance HLOZTransportedCanonicalProp49Row
open LazyDecomposition ScreeningInstantiation SpatialInsertionFiber
open TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition TilingShellZeroSourcePartition
open TilingShellZeroAllCreationTraceBridge
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem isTilingBase_of_dominantEndpointClass_canonical
    {t : DominoTiling} {x : Point}
    (hclass : dominantEndpointClass t x = .canonical) :
    IsTilingBase t x := by
  by_contra hbase
  simp [dominantEndpointClass, hbase] at hclass

/-- A canonical dominant narrow-window endpoint is a literal coordinate of
the oriented source support at the old creation clock. -/
theorem dominantEndpoint_mem_sourceSupportAt
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {a : GapScale}
    {s : WalkPath} {candidate : Point}
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hclass : dominantEndpointClass t candidate = .canonical)
    (horientation : OrientationCompatible o candidate)
    (hdominance : localTime s (creationTimeNat m k s)
        (tilingPartner t candidate) ≤
      localTime s (creationTimeNat m k s) candidate)
    (hnarrow : localTime s (creationTimeNat m k s) candidate ∈
      prop49NarrowTotalWindow m a) :
    candidate ∈ SourceSupportAt t o m s (creationTimeNat m k s) := by
  classical
  have hsource : localTime s (creationTimeNat m k s) candidate ∈
      shellZeroSourceTotalWindow m (shellWidth48 m) :=
    prop49NarrowTotalWindow_subset_source
      ((show 1 ≤ 2 by norm_num).trans harithmetic.1)
      harithmetic.2.1 hwindow.cut_le_width_pred hnarrow
  have hpositive : 0 < localTime s (creationTimeNat m k s) candidate := by
    have hlower := (mem_shellZeroSourceTotalWindow.mp hsource).1
    have hwidth := harithmetic.2.1
    omega
  have hbase : IsTilingBase t candidate :=
    isTilingBase_of_dominantEndpointClass_canonical hclass
  rw [SourceSupportAt, orientedShellZeroSourceSupportAt,
    mem_orientedTilingVTwoBases_iff, tilingVTwoBases, Finset.mem_filter]
  refine ⟨⟨?_, hdominance, hsource⟩, horientation⟩
  rw [visitedTilingBases, Finset.mem_image]
  refine ⟨candidate, ?_, ?_⟩
  · exact (mem_visitedSites_iff_localTime_pos _ _ _).mpr hpositive
  · simp [tilingBase, hbase]

/-- Outside the rank source/Theta payment, the complete canonical Theta set
is empty at the old creation clock. -/
theorem canonical_theta_eq_empty_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ} {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s) :
    orientedTilingThetaAtCreation t o m rank (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s = ∅ := by
  rcases hprofile.on_time_profile with
    ⟨N, hcreation, hnext, _hD, _hsep, hclock⟩
  have hcreationClock : creationTimeNat m rank s = N :=
    creationTimeNat_eq_of_creation hcreation
  have hclock44 : creationTimeNat m rank s ≤ hlozCutoff44 m := by
    rw [hcreationClock]
    simpa only
      [HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
      using hclock
  have hrestricted : orientedRestrictedThetaSourceAtCreation t o m rank
      (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) s = ∅ := by
    by_contra hne
    have hthetaEvent : s ∈ transportedRestrictedThetaSourceOnTimeEvent
        t o .canonical m rank := by
      change s ∈ restrictedThetaSourceOnTimeEvent t o m rank
      exact ⟨⟨N, hcreation.1⟩, hclock44,
        Finset.nonempty_iff_ne_empty.mpr hne⟩
    apply hprofile.source_theta_good
    apply Or.inr
    apply Or.inl
    cases o <;>
      simp only [allTilingRestrictedThetaPaymentAtRank,
        Set.mem_union] at hthetaEvent ⊢ <;> aesop
  apply orientedTilingThetaAtCreation_eq_empty_of_restrictedSource_empty
  · simpa only [hcreationClock] using hnext
  · exact hrestricted

/-- The original-path canonical row covers every unpaid physical dominant
endpoint in the narrow Proposition 4.9 window. -/
theorem mem_targetAmbientFamily_canonical_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ}
    (a : GapScale) (low : ℕ)
    (hrank : 0 < rank)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (hcardProfile : RawProp49SourceCardinalityProfile t m rank s)
    (candidate : Point)
    (hclass : dominantEndpointClass t candidate = .canonical)
    (horientation : OrientationCompatible o candidate)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner t candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (targetAmbientFamily t o .canonical m rank a low
      (by have := hprofile.level_two; omega) hrank hwindow harithmetic
        hexternalArithmetic).someCandidate := by
  have hm : 1 < m := by
    have := hprofile.level_two
    omega
  rcases hprofile.on_time_profile with
    ⟨N, hcreation, hnext, _hD, _hsep, _hclock⟩
  have hcreationClock : creationTimeNat m rank s = N :=
    creationTimeNat_eq_of_creation hcreation
  have hreach : s ∈ thresholdReachStage m rank :=
    ⟨N, hcreation.1⟩
  have hcardSource :
      (SourceSupportAt t o m s (creationTimeNat m rank s)).card ≤
        initialBudget48 m := by
    have hcardCut :
        (orientedCanonicalDominantNearBasesAtCreation t o m rank
          (shellWidth48 m) s).card ≤ orientedSourceCut48 m := by
      cases o with
      | even => exact hcardProfile.canonical_even
      | shifted => exact hcardProfile.canonical_shifted
    have hsourceEq :
        orientedCanonicalDominantNearBasesAtCreation t o m rank
            (shellWidth48 m) s =
          SourceSupportAt t o m s (creationTimeNat m rank s) := by
      exact orientedCanonicalDominantNearBasesAtCreation_eq_vTwo
        t o m rank (shellWidth48 m) s
          (by simpa only [hcreationClock] using hnext)
    rw [← hsourceEq]
    exact hcardCut.trans (Nat.div_le_self _ _)
  have hcandidate := dominantEndpoint_mem_sourceSupportAt
    (t := t) (o := o) (m := m) (k := rank) (a := a)
    hwindow harithmetic hclass horientation hdominance hnarrow
  have htheta := canonical_theta_eq_empty_of_unpaid
    (o := o) hprofile
  unfold targetAmbientFamily
  exact mem_sourceProp49StoppedHistoryCandidateFamily_univ_of_path
    (t := t) (o := o) a low hm hrank hwindow harithmetic
      hexternalArithmetic hprofile.valid hreach hcardSource htheta
      candidate hcandidate hnarrow

end

end Erdos1165.HLOZRawProp49CanonicalAmbientCover
