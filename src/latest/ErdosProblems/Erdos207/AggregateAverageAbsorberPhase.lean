/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedAggregateAveragePairBandSuccess
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound
import ErdosProblems.Erdos207.TimedStoppedPairTwoAway
import ErdosProblems.Erdos207.AverageOutsidePairSurvival

/-! # The corrected six-event averaged absorber-greedy phase -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def aggregateAveragedAbsorberPhaseFailure
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M n sPair sGlobal sInc Kpair Kglobal Kinc I : ℕ)
    (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V)
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ) : ℝ :=
  (Fintype.card (PairOn V) : ℝ) *
      (2 * Real.exp
        (-thetaPair * aPair + thetaPair ^ 2 * (n : ℝ) * vPair)) +
    (((Fintype.card (TripleOn V) : ℝ≥0) *
      (Fintype.card (PairOn V) : ℝ≥0) *
        pairTwoAwayTail q sPair Kpair
          (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
    (((Fintype.card (TripleOn V) : ℝ≥0) *
      envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) +
    (((Fintype.card (PairOn V) : ℝ≥0) *
      aggregatePairTwoAwayTail q sInc Kinc
        ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) +
    ((totalTwoAwayExpectationEnvelope q M H X B /
      ((I + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    Real.exp
      (-thetaAvail * aAvail + thetaAvail ^ 2 * (n : ℝ) * vAvail)

theorem exists_aggregateAveragedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I D JUpper : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (houtside0 : OutsideLeavePairsAlive H X
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A))
    (hD : 0 < D)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (havailabilityBuffer : ∀ i, i ≤ n →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Delta I D + aAvail ≤
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
        Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
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
        Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
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
        Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
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
        Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
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
          averageAvailabilityLossRate Delta I D +
        2 * (averageAvailabilityLossRate Delta I D) ^ 2 ≤ vAvail)
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
        D ≤ S.available.card ∧ S.chosen.card = n := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S0 := absorberGreedyInitialState F A
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F) active S0
  have hInvAbs : AbsorberGreedyInvariant F A S0 :=
    absorberGreedyInitialState_invariant F A fun C hC =>
      absorberErdosForbidden_nonempty hC
  have hAbsSupport : L.SupportedOn
      (fun z => AbsorberGreedyInvariant F A z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ => greedyKernel F) active S0 hInvAbs (by
        intro _i _hi S hS
        exact absorberGreedyKernel_supported hS)
  have hOutsideSupport : L.SupportedOn
      (fun z => OutsideLeavePairsAlive H X z.2) := by
    simpa only [L, active] using
      timedAggregateAveragePairBandProcessLaw_supported_outsideLeavePairsAlive
        n F H X S0 Kpair Kglobal Kinc Delta delta I D hInvAbs.1
        (by simpa only [F, S0] using houtside0) hsmallPair
  have hQsupport : L.SupportedOn (fun z =>
      AbsorberGreedyInvariant F A z.2 ∧ OutsideLeavePairsAlive H X z.2) := by
    intro z hmass
    exact ⟨hAbsSupport z hmass, hOutsideSupport z hmass⟩
  let epair : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp
      (-thetaPair * aPair + thetaPair ^ 2 * (n : ℝ) * vPair))
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
  let eavail : ℝ := Real.exp
    (-thetaAvail * aAvail + thetaAvail ^ 2 * (n : ℝ) * vAvail)
  have hpairProb : (L.probability (fun z => ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)) : ℝ) ≤ epair := by
    simpa only [F, S0, active, L, epair] using
      probability_timedAggregateAveragePairBand_exists_pair_deviation_ge_le_exp
        n F S0 qUpper qLower Kpair Kglobal Kinc Delta delta I D JUpper
        thetaPair aPair vPair hInvAbs.1 hdelta hsmallPair
        hqUpperLowerBound hqUpperNoninc hqLowerDeath hqLowerNoninc
        hqUpperDrift hqLowerDrift hvarianceUpper hvarianceLower
        hthetaPair hthetaUpper hthetaLower hvPair
  have hpairTwoProb :
      (L.probability (fun z => ¬ HasPairTwoAwayCutoff F Kpair z.2) : ℝ) ≤
        (epairTwoNN : ℝ) := by
    have hraw :=
      timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local
        (q := q) (n := n) (s := sPair) (D := D) (K := Kpair)
        (B := B) (A := A) active hD
        (fun _i _S hactive => hactive.1.2.2) hratio
    have hrawReal :
        ((FiniteLaw.timedStoppedProcessLaw n
          (fun _ => greedyKernel (absorberErdosForbiddenConfigurationsOn q B))
          active (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A)).probability
          (fun z => ¬ HasPairTwoAwayCutoff
            (absorberErdosForbiddenConfigurationsOn q B) Kpair z.2) : ℝ) ≤
          (((Fintype.card (TripleOn V) : ℝ≥0) *
            (Fintype.card (PairOn V) : ℝ≥0) *
            pairTwoAwayTail q sPair Kpair
              (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) := by
      exact_mod_cast hraw
    simpa only [F, S0, L, epairTwoNN] using hrawReal
  have hglobalProb :
      (L.probability (fun z => ¬ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
        (eglobalNN : ℝ) := by
    have hraw := timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
      (q := q) (M := M) (n := n) (s := sGlobal) (D := D)
      (K := Kglobal) (H := H) (X := X) (B := B) (A := A)
      active hA2 hD (fun _i _S hactive => hactive.1.2.2) hratio
    exact_mod_cast hraw
  have hincProb :
      (L.probability
        (fun z => ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) : ℝ) ≤
        (eincNN : ℝ) := by
    have hraw :=
      timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le_absorber
        (q := q) (n := n) (s := sInc) (D := D) (K := Kinc)
        (B := B) (A := A) active hD
        (fun _i _S hactive => hactive.1.2.2) hratio
    have hrawReal :
        ((FiniteLaw.timedStoppedProcessLaw n
          (fun _ => greedyKernel (absorberErdosForbiddenConfigurationsOn q B))
          active (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A)).probability
          (fun z => ¬ HasPairStarTwoAwayIncidenceCutoff
            (absorberErdosForbiddenConfigurationsOn q B) Kinc z.2) : ℝ) ≤
          (((Fintype.card (PairOn V) : ℝ≥0) *
            aggregatePairTwoAwayTail q sInc Kinc
              ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
                (Fintype.card V + 1 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) := by
      exact_mod_cast hraw
    simpa only [F, S0, L, eincNN] using hrawReal
  have htotalProb :
      (L.probability
        (fun z => I < totalAvailableTwoAwayIncidences F z.2) : ℝ) ≤
        (etotalNN : ℝ) := by
    have hraw := timedStoppedAbsorberGreedy_probability_totalTwoAway_gt_le
      (q := q) (M := M) (n := n) (D := D) (I := I)
      (H := H) (X := X) (B := B) (A := A) active hA2 hD
      (fun _i _S hactive => hactive.1.2.2) hratio
    exact_mod_cast hraw
  have havailProb : (L.probability (fun z =>
      aAvail ≤ averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I D) z.1.1 z.2 -
        averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I D) 0 S0) : ℝ) ≤ eavail := by
    simpa only [F, S0, active, L, eavail] using
      probability_timedAggregateAveragePairBand_availability_deficit_ge_le_exp
        n F S0 Kpair Kglobal Kinc Delta delta I D thetaAvail aAvail vAvail
        hInvAbs.1 hD hvarianceAvail hthetaAvail hthetaAvailJump hvAvail
  have hsmall' : epair + (epairTwoNN : ℝ) + (eglobalNN : ℝ) +
      (eincNN : ℝ) + (etotalNN : ℝ) + eavail < 1 := by
    simpa only [aggregateAveragedAbsorberPhaseFailure, epair, epairTwoNN,
      eglobalNN, eincNN, etotalNN, eavail] using hsmall
  obtain ⟨S, hSQ, _hSInv, hpairCut, hpairFloor, hpairTwoCut,
      hglobalCut, hincCut, htotalCut, hfloorS, hcardS⟩ :=
    exists_timedAggregateAveragePairBand_full_phase_of_failure_bounds
      (Q := fun S => AbsorberGreedyInvariant F A S ∧
        OutsideLeavePairsAlive H X S)
      n F S0 qUpper qLower Kpair Kglobal Kinc Delta delta I D aPair aAvail
      epair (epairTwoNN : ℝ) (eglobalNN : ℝ) (eincNN : ℝ)
      (etotalNN : ℝ) eavail hInvAbs.1 hD hQsupport havailabilityBuffer
      hcap htargetFloor hpairProb hpairTwoProb hglobalProb hincProb
      htotalProb havailProb hsmall'
  exact ⟨S, hSQ.1, hSQ.2, hpairCut, hpairFloor, hpairTwoCut, hglobalCut,
    hincCut, htotalCut, hfloorS,
    by simpa [S0, absorberGreedyInitialState] using hcardS⟩

end

end Erdos207
