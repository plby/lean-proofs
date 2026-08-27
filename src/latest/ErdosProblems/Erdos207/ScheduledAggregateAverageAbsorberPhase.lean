/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AggregateAverageAbsorberPhase
import ErdosProblems.Erdos207.TimedScheduledAggregatePairBandSuccess

/-!
# The six-event absorber phase with time-dependent survival floors

This is the long-phase wrapper needed by the sharp initial product law.  The
ordinary terminal cutoffs are kept in the active predicate, while the
additional schedules record the substantially stronger availability and
pair-star lower bounds used by the survival product.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_scheduledAggregateAveragedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut JUpper : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
    (Dschedule dschedule : ℕ → ℕ)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (houtside₀ : OutsideLeavePairsAlive H X
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A))
    (hDcut : 0 < Dcut)
    (hratio : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (havailabilityBuffer : ∀ i, i ≤ n →
      (Dcut : ℝ) + (i : ℝ) *
          averageAvailabilityLossRate Delta I Dcut + aAvail ≤
        ((absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A).available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) P.1
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) -
            qUpper P 0) + aPair ≤ ((Delta + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) →
      (delta : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) P.1
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) -
            qLower P 0) - aPair)
    (hscheduledAvailability : ∀ i S, i ≤ n →
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I Dcut) i S -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I Dcut) 0
              (absorberGreedyInitialState
                (absorberErdosForbiddenConfigurationsOn q B) A) < aAvail →
      Dschedule i ≤ S.available.card)
    (hscheduledPair : ∀ P : PairOn V, ∀ i S, i ≤ n →
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      PairAlive P.1 S →
      fixedPairLowerDeviation (qLower P)
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)
            P.1 i S -
          fixedPairLowerDeviation (qLower P)
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)
            P.1 0
              (absorberGreedyInitialState
                (absorberErdosForbiddenConfigurationsOn q B) A) < aPair →
      dschedule i ≤ (availableTrianglesContainingPair S P.1).card)
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤ qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(delta : ℝ) ≤ qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAggregateAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Kinc Delta delta I Dcut i S → PairAlive P.1 S →
      -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * delta - 2 - Delta : ℕ)) ≤
        qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAggregateAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Kinc Delta delta I Dcut i S → PairAlive P.1 S →
      qLower P (i + 1) - qLower P i ≤
        -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Delta : ℕ) + Kinc))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAggregateAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Kinc Delta delta I Dcut i S → PairAlive P.1 S →
      2 * ((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * Delta + Kglobal : ℕ) : ℝ)))) +
        2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ vPair)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAggregateAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Kinc Delta delta I Dcut i S → PairAlive P.1 S →
      2 * ((S.available.card : ℝ)⁻¹ *
          (((3 + Kpair : ℕ) : ℝ) *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Delta : ℕ) + Kinc))) +
        2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ vPair)
    (hthetaPair : 0 < thetaPair)
    (hthetaUpper : thetaPair * (JUpper : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hvPair : 0 ≤ vPair)
    (hvarianceAvail :
      2 * ((3 * Delta + Kglobal : ℕ) : ℝ) *
          averageAvailabilityLossRate Delta I Dcut +
        2 * (averageAvailabilityLossRate Delta I Dcut) ^ 2 ≤ vAvail)
    (hthetaAvail : 0 < thetaAvail)
    (hthetaAvailJump :
      thetaAvail * ((3 * Delta + Kglobal : ℕ) : ℝ) ≤ 1)
    (hvAvail : 0 ≤ vAvail)
    (hsmall : aggregateAveragedAbsorberPhaseFailure q M n sPair sGlobal sInc
      Kpair Kglobal Kinc I H X B thetaPair aPair vPair
      thetaAvail aAvail vAvail < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        OutsideLeavePairsAlive H X S ∧
        HasAvailablePairCutoff Delta S ∧ HasAvailablePairFloor delta S ∧
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        HasPairStarTwoAwayIncidenceCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kinc S ∧
        totalAvailableTwoAwayIncidences
          (absorberErdosForbiddenConfigurationsOn q B) S ≤ I ∧
        Dcut ≤ S.available.card ∧ Dschedule n ≤ S.available.card ∧
        HasAvailablePairFloor (dschedule n) S ∧ S.chosen.card = n := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let active := timedScheduledAggregatePairBandActive F Kpair Kglobal Kinc
    Delta delta I Dcut Dschedule dschedule
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hInvAbs : AbsorberGreedyInvariant F A S₀ :=
    absorberGreedyInitialState_invariant F A fun C hC ↦
      absorberErdosForbidden_nonempty hC
  have hAbsSupport : L.SupportedOn
      (fun z ↦ AbsorberGreedyInvariant F A z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hInvAbs (by
        intro _i _hi S hS
        exact absorberGreedyKernel_supported hS)
  have hOutsideSupport : L.SupportedOn
      (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
    simpa only [L, active, F, S₀] using
      timedScheduledAggregatePairBandProcessLaw_supported_outsideLeavePairsAlive
        n F H X S₀ Kpair Kglobal Kinc Delta delta I Dcut
        Dschedule dschedule hInvAbs.1
        (by simpa only [F, S₀] using houtside₀) hsmallPair
  have hQsupport : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F A z.2 ∧ OutsideLeavePairsAlive H X z.2) := by
    intro z hmass
    exact ⟨hAbsSupport z hmass, hOutsideSupport z hmass⟩
  let epairR : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp
      (-thetaPair * aPair + thetaPair ^ 2 * (n : ℝ) * vPair))
  let epairNN : ℝ≥0 := ⟨epairR, by
    dsimp only [epairR]
    positivity⟩
  let epairTwoNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    (Fintype.card (PairOn V) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (pairTwoAwayThreatExtensionCoefficient q B : ℕ)
  let eglobalNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    envelopeTwoAwayTail q M sGlobal H X B Kglobal
  let eincNN : ℝ≥0 := (Fintype.card (PairOn V) : ℝ≥0) *
    aggregatePairTwoAwayTail q sInc Kinc
      ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2)
  let etotalNN : ℝ≥0 := totalTwoAwayExpectationEnvelope q M H X B /
    ((I + 1 : ℕ) : ℝ≥0)
  let eavailR : ℝ := Real.exp
    (-thetaAvail * aAvail + thetaAvail ^ 2 * (n : ℝ) * vAvail)
  let eavailNN : ℝ≥0 := ⟨eavailR, by
    dsimp only [eavailR]
    positivity⟩
  have hpairReal : (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) : ℝ) ≤
      epairR := by
    simpa only [F, S₀, active, L, epairR] using
      probability_timedScheduledAggregatePairBand_exists_pair_deviation_ge_le_exp
        n F S₀ qUpper qLower Kpair Kglobal Kinc Delta delta I Dcut JUpper
        Dschedule dschedule thetaPair aPair vPair hInvAbs.1 hdelta hsmallPair
        hqUpperLowerBound hqUpperNoninc hqLowerDeath hqLowerNoninc
        hqUpperDrift hqLowerDrift hvarianceUpper hvarianceLower
        hthetaPair hthetaUpper hthetaLower hvPair
  have hpairNN : L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) ≤ epairNN := by
    exact_mod_cast hpairReal
  have hpairTwoNN :
      L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤
        epairTwoNN := by
    simpa only [F, S₀, active, L, epairTwoNN] using
      (timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local
        (q := q) (n := n) (s := sPair) (D := Dcut) (K := Kpair)
        (B := B) (A := A) active hDcut
        (fun _i _S hactive ↦ hactive.1.1.2.2) hratio)
  have hglobalNN :
      L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤
        eglobalNN := by
    simpa only [F, S₀, active, L, eglobalNN] using
      (timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
        (q := q) (M := M) (n := n) (s := sGlobal) (D := Dcut)
        (K := Kglobal) (H := H) (X := X) (B := B) (A := A)
        active hA2 hDcut (fun _i _S hactive ↦ hactive.1.1.2.2) hratio)
  have hincNN : L.probability
      (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) ≤
        eincNN := by
    simpa only [F, S₀, active, L, eincNN] using
      (timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le_absorber
        (q := q) (n := n) (s := sInc) (D := Dcut) (K := Kinc)
        (B := B) (A := A) active hDcut
        (fun _i _S hactive ↦ hactive.1.1.2.2) hratio)
  have htotalNN : L.probability
      (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) ≤ etotalNN := by
    simpa only [F, S₀, active, L, etotalNN] using
      (timedStoppedAbsorberGreedy_probability_totalTwoAway_gt_le
        (q := q) (M := M) (n := n) (D := Dcut) (I := I)
        (H := H) (X := X) (B := B) (A := A) active hA2 hDcut
        (fun _i _S hactive ↦ hactive.1.1.2.2) hratio)
  have havailReal : (L.probability (fun z ↦
      aAvail ≤ averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I Dcut) z.1.1 z.2 -
        averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I Dcut) 0 S₀) : ℝ) ≤
      eavailR := by
    simpa only [F, S₀, active, L, eavailR] using
      probability_timedScheduledAggregatePairBand_availability_deficit_ge_le_exp
        n F S₀ Kpair Kglobal Kinc Delta delta I Dcut Dschedule dschedule
        thetaAvail aAvail vAvail hInvAbs.1 hDcut hvarianceAvail
        hthetaAvail hthetaAvailJump hvAvail
  have havailNN : L.probability (fun z ↦
      aAvail ≤ averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I Dcut) z.1.1 z.2 -
        averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I Dcut) 0 S₀) ≤ eavailNN := by
    exact_mod_cast havailReal
  have hinactiveNN : L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      epairNN + epairTwoNN + eglobalNN + eincNN + etotalNN + eavailNN := by
    simpa only [F, S₀, active, L] using
      probability_timedScheduledAggregatePairBand_not_active_le_sum
        n F S₀ qUpper qLower Kpair Kglobal Kinc Delta delta I Dcut
        Dschedule dschedule aPair aAvail epairNN epairTwoNN eglobalNN
        eincNN etotalNN eavailNN hInvAbs.1 hDcut
        (by simpa only [F, S₀] using havailabilityBuffer)
        (by simpa only [F, S₀] using hcap)
        (by simpa only [F, S₀] using htargetFloor)
        (by simpa only [F, S₀] using hscheduledAvailability)
        (by simpa only [F, S₀] using hscheduledPair)
        hpairNN hpairTwoNN hglobalNN hincNN htotalNN havailNN
  have hinactiveReal : (L.probability (fun z ↦ ¬ active z.1.1 z.2) : ℝ) ≤
      ((epairNN + epairTwoNN + eglobalNN + eincNN + etotalNN +
        eavailNN : ℝ≥0) : ℝ) := by
    exact_mod_cast hinactiveNN
  have hsmall' :
      ((epairNN + epairTwoNN + eglobalNN + eincNN + etotalNN +
        eavailNN : ℝ≥0) : ℝ) < 1 := by
    change (epairNN : ℝ) + (epairTwoNN : ℝ) + (eglobalNN : ℝ) +
      (eincNN : ℝ) + (etotalNN : ℝ) + (eavailNN : ℝ) < 1
    have hepair : (epairNN : ℝ) = epairR := rfl
    have heavail : (eavailNN : ℝ) = eavailR := rfl
    rw [hepair, heavail]
    simpa only [aggregateAveragedAbsorberPhaseFailure, epairNN, epairR,
      epairTwoNN, eglobalNN, eincNN, etotalNN, eavailNN, eavailR,
      NNReal.coe_mk] using hsmall
  obtain ⟨S, hSQ, _hInv, hpairCut, hpairFloor, hpairTwoCut,
      hglobalCut, hincCut, htotalCut, hDcutS, hDscheduleS,
      hdscheduleS, hcardS⟩ :=
    exists_timedScheduledAggregatePairBand_full_phase_of_not_active_bound
      (Q := fun S ↦ AbsorberGreedyInvariant F A S ∧
        OutsideLeavePairsAlive H X S)
      n F S₀ Kpair Kglobal Kinc Delta delta I Dcut Dschedule dschedule
      ((epairNN + epairTwoNN + eglobalNN + eincNN + etotalNN +
        eavailNN : ℝ≥0) : ℝ)
      hInvAbs.1 (by simpa only [F, S₀, active, L] using hQsupport)
      (by simpa only [F, S₀, active, L] using hinactiveReal) hsmall'
  exact ⟨S, hSQ.1, hSQ.2, hpairCut, hpairFloor, hpairTwoCut,
    hglobalCut, hincCut, htotalCut, hDcutS, hDscheduleS, hdscheduleS,
    by simpa [S₀, absorberGreedyInitialState] using hcardS⟩

end

end Erdos207
