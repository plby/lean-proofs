/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedAveragePairBandSuccess
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound
import ErdosProblems.Erdos207.TimedStoppedPairTwoAway
import ErdosProblems.Erdos207.AverageOutsidePairSurvival

/-!
# A complete averaged absorber-greedy phase

This file instantiates all five failure estimates in the abstract averaged
pair-band extraction theorem.  The result is still parameterized by the
deterministic trajectory inequalities, but every probability term is now an
explicit expression furnished by the absorber localization bounds.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Scalar failure bound for one averaged absorber-greedy phase. -/
def averagedAbsorberPhaseFailure
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M n sPair sGlobal Kpair Kglobal I : ℕ)
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
    ((totalTwoAwayExpectationEnvelope q M H X B /
      ((I + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    Real.exp
      (-thetaAvail * aAvail + thetaAvail ^ 2 * (n : ℝ) * vAvail)

/-- All moment, concentration, and union-bound inputs assembled on the same
timed law. -/
theorem exists_averagedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal Kpair Kglobal Δ δ I D JUpper : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (houtside₀ : OutsideLeavePairsAlive H X
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A))
    (hD : 0 < D)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (havailabilityBuffer : ∀ i, i ≤ n →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Δ I D + aAvail ≤
        ((absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A).available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)
            P.1
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) -
            qUpper P 0) + aPair ≤ ((Δ + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)
            P.1
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) -
            qLower P 0) - aPair)
    (hδ : 1 ≤ δ) (hsmallPair : 3 + Kpair < δ)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤ qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(δ : ℝ) ≤ qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Δ δ I D i S → PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Δ δ I D i S → PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Δ + Kglobal : ℕ)))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Δ δ I D i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ vPair)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) S →
      timedAveragePairBandActive
        (absorberErdosForbiddenConfigurationsOn q B)
        Kpair Kglobal Δ δ I D i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ vPair)
    (hthetaPair : 0 < thetaPair)
    (hthetaUpper : thetaPair * (JUpper : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hvPair : 0 ≤ vPair)
    (hvarianceAvail :
      2 * ((3 * Δ + Kglobal : ℕ) : ℝ) *
          averageAvailabilityLossRate Δ I D +
        2 * (averageAvailabilityLossRate Δ I D) ^ 2 ≤ vAvail)
    (hthetaAvail : 0 < thetaAvail)
    (hthetaAvailJump :
      thetaAvail * ((3 * Δ + Kglobal : ℕ) : ℝ) ≤ 1)
    (hvAvail : 0 ≤ vAvail)
    (hsmall : averagedAbsorberPhaseFailure q M n sPair sGlobal
      Kpair Kglobal I H X B thetaPair aPair vPair
      thetaAvail aAvail vAvail < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        OutsideLeavePairsAlive H X S ∧
        HasAvailablePairCutoff Δ S ∧
        HasAvailablePairFloor δ S ∧
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        totalAvailableTwoAwayIncidences
          (absorberErdosForbiddenConfigurationsOn q B) S ≤ I ∧
        D ≤ S.available.card ∧
        S.chosen.card = n := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let active := timedAveragePairBandActive F Kpair Kglobal Δ δ I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
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
    simpa only [L, active] using
      timedAveragePairBandProcessLaw_supported_outsideLeavePairsAlive
        n F H X S₀ Kpair Kglobal Δ δ I D hInvAbs.1
          (by simpa only [F, S₀] using houtside₀) hsmallPair
  have hQsupport : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F A z.2 ∧
        OutsideLeavePairsAlive H X z.2) := by
    intro z hmass
    exact ⟨hAbsSupport z hmass, hOutsideSupport z hmass⟩
  let εpair : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp
      (-thetaPair * aPair + thetaPair ^ 2 * (n : ℝ) * vPair))
  let εpairTwoNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    (Fintype.card (PairOn V) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (pairTwoAwayThreatExtensionCoefficient q B : ℕ)
  let εglobalNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    envelopeTwoAwayTail q M sGlobal H X B Kglobal
  let εtotalNN : ℝ≥0 := totalTwoAwayExpectationEnvelope q M H X B /
    ((I + 1 : ℕ) : ℝ≥0)
  let εavail : ℝ := Real.exp
    (-thetaAvail * aAvail + thetaAvail ^ 2 * (n : ℝ) * vAvail)
  have hpairProb : (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) : ℝ) ≤ εpair := by
    simpa only [F, S₀, active, L, εpair] using
      probability_timedAveragePairBand_exists_pair_deviation_ge_le_exp
        n F S₀ qUpper qLower Kpair Kglobal Δ δ I D JUpper
        thetaPair aPair vPair hInvAbs.1 hD hδ hsmallPair
        hqUpperLowerBound hqUpperNoninc hqLowerDeath hqLowerNoninc
        hqUpperDrift hqLowerDrift hvarianceUpper hvarianceLower
        hthetaPair hthetaUpper hthetaLower hvPair
  have hpairTwoProb :
      (L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) : ℝ) ≤
        (εpairTwoNN : ℝ) := by
    have hraw :=
      timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local
        (q := q) (n := n) (s := sPair) (D := D) (K := Kpair)
        (B := B) (A := A) active hD
        (fun _i _S hactive ↦ hactive.2.2) hratio
    have hrawReal :
        ((FiniteLaw.timedStoppedProcessLaw n
            (fun _ ↦ greedyKernel
              (absorberErdosForbiddenConfigurationsOn q B)) active
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)).probability
            (fun z ↦ ¬ HasPairTwoAwayCutoff
              (absorberErdosForbiddenConfigurationsOn q B) Kpair z.2) : ℝ) ≤
          (((Fintype.card (TripleOn V) : ℝ≥0) *
            (Fintype.card (PairOn V) : ℝ≥0) *
              pairTwoAwayTail q sPair Kpair
                (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) := by
      exact_mod_cast hraw
    simpa only [F, S₀, L, εpairTwoNN] using hrawReal
  have hglobalProb :
      (L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
        (εglobalNN : ℝ) := by
    have hraw :=
      timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
        (q := q) (M := M) (n := n) (s := sGlobal) (D := D)
        (K := Kglobal) (H := H) (X := X) (B := B) (A := A)
        active hA2 hD
        (fun _i _S hactive ↦ hactive.2.2) hratio
    have hrawReal :
        ((FiniteLaw.timedStoppedProcessLaw n
            (fun _ ↦ greedyKernel
              (absorberErdosForbiddenConfigurationsOn q B)) active
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)).probability
            (fun z ↦ ¬ HasTwoAwayCutoff
              (absorberErdosForbiddenConfigurationsOn q B) Kglobal z.2) : ℝ) ≤
          (((Fintype.card (TripleOn V) : ℝ≥0) *
            envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) := by
      exact_mod_cast hraw
    simpa only [F, S₀, L, εglobalNN] using hrawReal
  have htotalProb :
      (L.probability
        (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) : ℝ) ≤
        (εtotalNN : ℝ) := by
    have hraw :=
      timedStoppedAbsorberGreedy_probability_totalTwoAway_gt_le
        (q := q) (M := M) (n := n) (D := D) (I := I)
        (H := H) (X := X) (B := B) (A := A) active hA2 hD
        (fun _i _S hactive ↦ hactive.2.2) hratio
    have hrawReal :
        ((FiniteLaw.timedStoppedProcessLaw n
            (fun _ ↦ greedyKernel
              (absorberErdosForbiddenConfigurationsOn q B)) active
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A)).probability
            (fun z ↦ I < totalAvailableTwoAwayIncidences
              (absorberErdosForbiddenConfigurationsOn q B) z.2) : ℝ) ≤
          ((totalTwoAwayExpectationEnvelope q M H X B /
            ((I + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      exact_mod_cast hraw
    simpa only [F, S₀, L, εtotalNN] using hrawReal
  have havailProb : (L.probability (fun z ↦
      aAvail ≤ averageAvailabilityDeficit
          (averageAvailabilityLossRate Δ I D) z.1.1 z.2 -
        averageAvailabilityDeficit
          (averageAvailabilityLossRate Δ I D) 0 S₀) : ℝ) ≤ εavail := by
    simpa only [F, S₀, active, L, εavail] using
      probability_timedAveragePairBand_availability_deficit_ge_le_exp
        n F S₀ Kpair Kglobal Δ δ I D thetaAvail aAvail vAvail
        hInvAbs.1 hD hvarianceAvail hthetaAvail hthetaAvailJump hvAvail
  have hsmall' :
      εpair + (εpairTwoNN : ℝ) + (εglobalNN : ℝ) +
        (εtotalNN : ℝ) + εavail < 1 := by
    simpa only [averagedAbsorberPhaseFailure, εpair, εpairTwoNN,
      εglobalNN, εtotalNN, εavail] using hsmall
  obtain ⟨S, hSQ, _hSInv, hpairCut, hpairFloor,
      hpairTwoCut, hglobalCut, htotalCut, hfloorS, hcardS⟩ :=
    exists_timedAveragePairBand_full_phase_of_failure_bounds
      (Q := fun S ↦ AbsorberGreedyInvariant F A S ∧
        OutsideLeavePairsAlive H X S)
      n F S₀ qUpper qLower Kpair Kglobal Δ δ I D aPair aAvail
      εpair (εpairTwoNN : ℝ) (εglobalNN : ℝ) (εtotalNN : ℝ) εavail
      hInvAbs.1 hD hQsupport havailabilityBuffer hcap htargetFloor
      hpairProb hpairTwoProb hglobalProb htotalProb havailProb hsmall'
  exact ⟨S, hSQ.1, hSQ.2, hpairCut, hpairFloor, hpairTwoCut, hglobalCut,
    htotalCut, hfloorS,
    by simpa [S₀, absorberGreedyInitialState] using hcardS⟩

end

end Erdos207
