/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeProp49PathCoverage
import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family
import ErdosProblems.Erdos1165.HLOZRawProp49OppositeColumnAmbientCover

/-!
# Opposite checker coverage with an exposed shifted origin

An unpaid opposite checker endpoint is transported by deleting its first
step.  When the shifted physical-origin domino belongs to the target source
support, the literal origin-safe Proposition 4.9 row covers the transported
path.  The complementary non-exposed-origin case is deliberately not folded
into this statement.
-/

open Set

namespace Erdos1165.HLOZRawProp49OppositeCheckerExposedOriginCover

open ExternalProposition44 HLOZCheckerOriginSafeProp49Family
open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZCheckerOriginSafeProp49PathCoverage
open HLOZCheckerPrefixedCylinderTransport HLOZPathEvents
open HLOZCheckerOriginShiftPayment HLOZLowGapProductEndgame
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZRawProp49CanonicalAmbientCover
open HLOZPrefixedCanonicalSourceProp49PathCoverage
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open HLOZRawProp49OppositeColumnAmbientCover
open HLOZRawProp49SourceCardinality HLOZRawProp49UnpaidProfile
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceCorrectFullGapClosure
open HLOZSourceEndpointTransportTable HLOZSourceOrientedThetaRankPayment
open HLOZSourceOrientedThetaWindowSplit
open HLOZThetaOneSourceShift HLOZThetaSourceBalance
open LazyDecomposition PreStoppingSpatialLaw ScreeningInstantiation
open SpatialInsertionFiber TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem not_isTilingBase_of_opposite
    {d : Tilings.CheckerDirection} {x : Point}
    (hclass : dominantEndpointClass (.checker d) x = .opposite) :
    ¬ IsTilingBase (.checker d) x := by
  intro hbase
  simp [dominantEndpointClass, hbase] at hclass

/-- Complete recentered target data extracted from one unpaid physical
checker-opposite transition. -/
structure OppositeCheckerTargetProfile
    (d : Tilings.CheckerDirection) (rank m : ℕ) (a : GapScale)
    (e : Direction) (s : WalkPath) (candidate : Point) : Prop where
  valid : oneStepRecenter s ∈ validStepWalk
  reach : oneStepRecenter s ∈ thresholdReachStage m rank
  safe : oneStepRecenter s ∈ targetOriginSafe m rank e
  card : (SourceSupportAt (shiftedCheckerTarget d) .even m
    (oneStepRecenter s)
    (creationTimeNat m rank (oneStepRecenter s))).card ≤ initialBudget48 m
  theta : orientedTilingThetaBases (shiftedCheckerTarget d) .even m
    (shellWidth48 m) (shellZeroExternalLow48 m)
    (shellZeroExternalHigh48 m) (oneStepRecenter s)
    (creationTimeNat m rank (oneStepRecenter s)) = ∅
  candidate_mem : candidate ∈ SourceSupportAt (shiftedCheckerTarget d) .even m
    (oneStepRecenter s) (creationTimeNat m rank (oneStepRecenter s))
  narrow : localTime (oneStepRecenter s)
    (creationTimeNat m rank (oneStepRecenter s)) candidate ∈
      prop49NarrowTotalWindow m a

/-- Extract all target-row data independently of whether the shifted origin
is exposed or distinguished. -/
theorem oppositeCheckerTargetProfile_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {d : Tilings.CheckerDirection} {rank m : ℕ}
    (a : GapScale) (e : Direction)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (_hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data (.checker d) rank m s)
    (candidate : Point)
    (hclass : dominantEndpointClass (.checker d) candidate = .opposite)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner (.checker d) candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a)
    (hfirst : s 1 = directionVector e) :
    OppositeCheckerTargetProfile d rank m a e s (candidate - s 1) := by
  let omega : StepPath := stepsOfWalk s
  have homega : trajectory omega = s := hprofile.valid
  rcases hprofile.on_time_profile with
    ⟨N, hcreation, hnext, _hD, hsep, hclock⟩
  have hcreationOmega : ThresholdCreation (trajectory omega) m rank N := by
    simpa only [homega] using hcreation
  have hnextOmega : thresholdCount (trajectory omega) N (m + 1) = 0 := by
    simpa only [homega] using hnext
  have hsepOmega : TilingThresholdDominoSeparated (.checker d)
      (trajectory omega) N m := by
    simpa only [homega] using hsep
  have hgoodOrigin : trajectory omega ∉
      checkerOriginShiftExceptionEvent d m rank (shellWidth48 m) := by
    intro hbad
    apply hprofile.source_theta_good
    refine Or.inr (Or.inr ?_)
    simpa only [homega, allTilingCheckerOriginShiftPaidEvent] using
      (checkerOriginShiftException_mem_paid_of_creation omega d hrank
        hcreationOmega hnextOmega hbad)
  have horiginLT : localTime (trajectory omega) N 0 < m := by
    have h := not_mem_checkerOriginShiftExceptionEvent hgoodOrigin
    rw [creationTimeNat_eq_of_creation hcreationOmega] at h
    exact h
  have hNpos := thresholdCreation_time_pos_of_two_le omega
    hprofile.level_two hrank hcreationOmega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  have hshiftCreation : ThresholdCreation
      (oneStepRecenter (trajectory omega)) m rank n :=
    thresholdCreation_oneStepRecenter omega n m rank (by omega)
      hcreationOmega (by
        simpa only [Nat.succ_eq_add_one] using horiginLT)
  have hshiftClock : creationTimeNat m rank
      (oneStepRecenter (trajectory omega)) = n :=
    creationTimeNat_eq_of_creation hshiftCreation
  have hshiftReach : ReachesThreshold
      (oneStepRecenter (trajectory omega)) m rank :=
    ⟨n, hshiftCreation.1⟩
  have hshiftNext : thresholdCount (oneStepRecenter (trajectory omega))
      n (m + 1) = 0 := by
    rw [thresholdCount_oneStepRecenter_eq omega n (m + 1) (by omega)]
    · exact hnextOmega
    · have hltm : localTime (trajectory omega) (n + 1) 0 < m := by
        simpa only [Nat.succ_eq_add_one] using horiginLT
      have : localTime (trajectory omega) (n + 1) 0 < m + 1 := by omega
      simpa only [Nat.succ_eq_add_one] using this
  have hshiftD : tilingDEtaAtCreation (shiftedCheckerTiling d) m rank
      (shellWidth48 m) (m - shellWidth48 m)
      (oneStepRecenter (trajectory omega)) :=
    tilingDEtaAtCreation_oneStepRecenter omega d hprofile.level_two hrank rfl
      hcreationOmega hnextOmega hsepOmega (by
        simpa only [Nat.succ_eq_add_one] using horiginLT)
  have hshiftCutoff : creationTimeNat m rank
      (oneStepRecenter (trajectory omega)) ≤ hlozCutoff44 m := by
    rw [hshiftClock]
    simpa only
      [HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
      using (show n ≤ levelCutoffTime upperTailDelta m by omega)
  have hcard : (SourceSupportAt (shiftedCheckerTarget d) .even m
      (oneStepRecenter s)
      (creationTimeNat m rank (oneStepRecenter s))).card ≤
        initialBudget48 m := by
    have h := targetSourceSupport_card_le_initialBudget_of_unpaid
      (t := .checker d) (o := .shifted) (a := a) hprofile hrank hrank_le ha
      (by simpa only [sourceTransportPath, homega] using hshiftReach)
      (by simpa only [sourceTransportPath, homega] using hshiftCutoff)
      (by simpa only [sourceTransportTargetTiling, shiftedCheckerTarget,
          shiftedCheckerTiling, sourceTransportPath, homega] using hshiftD)
      (by
        change thresholdCount (oneStepRecenter s)
          (creationTimeNat m rank (oneStepRecenter s)) (m + 1) = 0
        rw [← homega, hshiftClock]
        exact hshiftNext)
    simpa only [sourceTransportTargetTiling,
      sourceTransportTargetOrientation, sourceTransportPath] using h
  have hrestricted : orientedRestrictedThetaSourceAtCreation
      (shiftedCheckerTarget d) .even m rank (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (oneStepRecenter s) = ∅ := by
    have h := targetRestrictedTheta_eq_empty_of_unpaid
      (t := .checker d) (o := .shifted) hprofile
      (by simpa only [sourceTransportPath, homega] using hshiftReach)
      (by simpa only [sourceTransportPath, homega] using hshiftCutoff)
    simpa only [sourceTransportTargetTiling,
      sourceTransportTargetOrientation, sourceTransportPath] using h
  have htheta : orientedTilingThetaAtCreation
      (shiftedCheckerTarget d) .even m rank (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (oneStepRecenter s) = ∅ := by
    apply orientedTilingThetaAtCreation_eq_empty_of_restrictedSource_empty
    · rw [← homega, hshiftClock]
      exact hshiftNext
    · exact hrestricted
  have htargetValid : oneStepRecenter s ∈ validStepWalk := by
    rw [← homega, oneStepRecenter_trajectory]
    exact trajectory_mem_validStepWalk _
  have hnotBase : ¬ IsTilingBase (.checker d) candidate :=
    not_isTilingBase_of_opposite hclass
  have hcandidateZero : candidate ≠ 0 := by
    intro hzero
    apply hnotBase
    rw [hzero]
    rfl
  let targetCandidate := candidate - s 1
  have hphysicalClock : creationTimeNat m rank s = n + 1 :=
    creationTimeNat_eq_of_creation hcreation
  have horiginalVTwo : tilingVTwoAt (.checker d)
      (prop49NarrowTotalWindow m a) (trajectory omega) (n + 1)
      candidate := by
    unfold tilingVTwoAt
    rw [homega]
    simpa only [hphysicalClock] using And.intro hdominance hnarrow
  have htargetVTwo : tilingVTwoAt (shiftedCheckerTiling d)
      (prop49NarrowTotalWindow m a) (oneStepRecenter (trajectory omega)) n
      targetCandidate := by
    rw [show targetCandidate = candidate - trajectory omega 1 by
      simp only [targetCandidate, homega]]
    apply tilingVTwoAt_oneStepRecenter_of_opposite omega d n
      (prop49NarrowTotalWindow m a) candidate hnotBase hcandidateZero
    exact horiginalVTwo
  have htargetBase : IsTilingBase (shiftedCheckerTiling d) targetCandidate :=
    by
      simpa only [targetCandidate, homega] using
        (isTilingBase_shiftedChecker_iff_not omega d candidate).2 hnotBase
  have htargetClass : dominantEndpointClass (shiftedCheckerTarget d)
      targetCandidate = .canonical := by
    simpa only [shiftedCheckerTarget, shiftedCheckerTiling] using
      (show dominantEndpointClass (shiftedCheckerTiling d) targetCandidate =
        .canonical by simp [dominantEndpointClass, htargetBase])
  have htargetOrientation : OrientationCompatible .even targetCandidate := by
    have hbaseIff : IsTilingBase (shiftedCheckerTiling d) targetCandidate ↔
        EvenPoint targetCandidate := by
      simpa only [shiftedCheckerTiling, IsTilingBase, canonicalEastTiling] using
        (isTilingBase_canonicalEast_iff_evenPoint targetCandidate)
    exact hbaseIff.mp htargetBase
  have htargetNarrow : localTime (oneStepRecenter s)
      (creationTimeNat m rank (oneStepRecenter s)) targetCandidate ∈
        prop49NarrowTotalWindow m a := by
    rw [← homega, hshiftClock]
    exact htargetVTwo.2
  have htargetDominance : localTime (oneStepRecenter s)
        (creationTimeNat m rank (oneStepRecenter s))
        (tilingPartner (shiftedCheckerTarget d) targetCandidate) ≤
      localTime (oneStepRecenter s)
        (creationTimeNat m rank (oneStepRecenter s)) targetCandidate := by
    rw [← homega, hshiftClock]
    simpa only [shiftedCheckerTarget, shiftedCheckerTiling] using
      htargetVTwo.1
  have hcandidateTarget : targetCandidate ∈
      SourceSupportAt (shiftedCheckerTarget d) .even m
        (oneStepRecenter s)
        (creationTimeNat m rank (oneStepRecenter s)) :=
    dominantEndpoint_mem_sourceSupportAt hwindow harithmetic htargetClass
      htargetOrientation htargetDominance htargetNarrow
  have hsafe : oneStepRecenter s ∈ targetOriginSafe m rank e := by
    change localTime (oneStepRecenter s)
      (creationTimeNat m rank (oneStepRecenter s))
      (0 - directionVector e) + 1 < m
    have hfirstOmega : trajectory omega 1 = directionVector e := by
      rw [homega]
      exact hfirst
    rw [← homega, hshiftClock, ← hfirstOmega,
      localTime_oneStepRecenter_origin_add_one]
    simpa only [Nat.succ_eq_add_one] using horiginLT
  exact
    { valid := htargetValid
      reach := by
        change ReachesThreshold (oneStepRecenter s) m rank
        rw [← homega]
        exact hshiftReach
      safe := hsafe
      card := hcard
      theta := htheta
      candidate_mem := hcandidateTarget
      narrow := htargetNarrow }

/-- Exact checker-opposite membership in the original exposed-origin row. -/
theorem mem_checkerOriginSafeFamily_of_unpaid_of_origin_mem
    {data : FullBetaSourceCorrectAllTilingProductData}
    {d : Tilings.CheckerDirection} {rank m : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data (.checker d) rank m s)
    (candidate : Point)
    (hclass : dominantEndpointClass (.checker d) candidate = .opposite)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner (.checker d) candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a)
    (hfirst : s 1 = directionVector e)
    (horigin : targetOriginBase (shiftedCheckerTarget d) e ∈
      SourceSupportAt (shiftedCheckerTarget d) .even m
        (oneStepRecenter s)
        (creationTimeNat m rank (oneStepRecenter s))) :
    s ∈ (checkerOriginSafeFamily
      (t := shiftedCheckerTarget d) (o := .even) a low e hm hrank hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate := by
  let profile := oppositeCheckerTargetProfile_of_unpaid a e hm hrank hrank_le
    ha hwindow harithmetic hexternalArithmetic hprofile candidate hclass
      hdominance hnarrow hfirst
  have htargetMem := mem_originSafeTargetFamily_of_path
    (t := shiftedCheckerTarget d) (o := .even) a low e hm hrank hwindow
      harithmetic hwidth hexternalArithmetic profile.valid profile.reach
      profile.safe profile.card profile.theta horigin (candidate - s 1)
      profile.candidate_mem profile.narrow
  rw [checkerOriginSafeFamily_someCandidate]
  exact ⟨by simpa only [firstDirectionWalk, Set.mem_ofPred_eq] using hfirst,
    htargetMem⟩

/-- Exact checker-opposite membership in the complete fixed-direction row;
the shifted origin may be either exposed or distinguished. -/
theorem mem_checkerCompleteOriginSafeFamily_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {d : Tilings.CheckerDirection} {rank m : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data (.checker d) rank m s)
    (candidate : Point)
    (hclass : dominantEndpointClass (.checker d) candidate = .opposite)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner (.checker d) candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a)
    (hfirst : s 1 = directionVector e) :
    s ∈ (checkerCompleteOriginSafeFamily
      (t := shiftedCheckerTarget d) (o := .even) a low e hm hrank hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate := by
  let profile := oppositeCheckerTargetProfile_of_unpaid a e hm hrank hrank_le
    ha hwindow harithmetic hexternalArithmetic hprofile candidate hclass
      hdominance hnarrow hfirst
  exact mem_checkerCompleteOriginSafeFamily_of_target_path
    (t := shiftedCheckerTarget d) (o := .even) a low e hm hrank hwindow
      harithmetic hwidth hexternalArithmetic hfirst profile.valid profile.reach
      profile.safe profile.card profile.theta (candidate - s 1)
      profile.candidate_mem profile.narrow

end

end Erdos1165.HLOZRawProp49OppositeCheckerExposedOriginCover
