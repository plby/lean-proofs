/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedSharpScheduledAggregatePairBand
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound
import ErdosProblems.Erdos207.TimedStoppedPairTwoAway
import ErdosProblems.Erdos207.AverageOutsidePairSurvival
import ErdosProblems.Erdos207.OuterOnlySharpScheduledFirstPassage
import ErdosProblems.Erdos207.ScaledTimedStoppedAbsorberTails

/-!
# Failure probability for the sharp scheduled absorber phase

The sharp scheduled process already has concentration estimates for its
pair trajectories.  This file combines those estimates with the four
standard absorber-envelope tails.  The resulting five-event union bound is
the quantitative input required by the sharp initial product law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The five failure terms for a sharp scheduled absorber-greedy phase. -/
def sharpScheduledAbsorberPhaseFailure
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M n sPair sGlobal sInc Kpair Kglobal Kinc I : ℕ)
    (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V)
    (scale : ℝ≥0)
    (thetaPair aPair vPair : ℝ) : ℝ≥0 :=
  ⟨(Fintype.card (PairOn V) : ℝ) *
      (2 * Real.exp
        (-thetaPair * aPair + thetaPair ^ 2 * (n : ℝ) * vPair)), by
      positivity⟩ +
    (Fintype.card (TripleOn V) : ℝ≥0) *
      (Fintype.card (PairOn V) : ℝ≥0) *
        pairTwoAwayTail q sPair Kpair
          (scale ^ q *
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ)) +
    (Fintype.card (TripleOn V) : ℝ≥0) *
      pairTwoAwayTail q sGlobal Kglobal
        (scale ^ q *
          (twoAwayThreatExtensionCoefficient q M H X B : ℕ)) +
    (Fintype.card (PairOn V) : ℝ≥0) *
      aggregatePairTwoAwayTail q sInc Kinc
        (scale ^ q *
          ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2)) +
    scaledTotalTwoAwayExpectationEnvelope q M H X B scale /
      ((I + 1 : ℕ) : ℝ≥0)

/-- The sharp scheduled stopped process leaves its active region with
probability at most the explicit five-event failure sum. -/
theorem probability_timedSharpScheduledAbsorber_not_active_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut
      JUpper : ℕ}
    {F : ForbiddenFamilyOn V} {H G : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V} {S₀ : GreedyStateOn V}
    (D d Mschedule u : ℕ → ℕ) (thetaPair aPair vPair : ℝ)
    (rate scale : ℝ≥0)
    (hF : F = absorberErdosForbiddenConfigurationsOn q B)
    (hS₀ : S₀ = absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) (outerOnlyAvailable U A))
    (hA2 : HasAbsorberLocalization q M H X B)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (htri : ConsistsOfTriangles G A)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallBase : 3 + Kpair < delta)
    (hDcutPos : 0 < Dcut)
    (hDpos : ∀ i, i ≤ n → 0 < D i)
    (hDgap : ∀ i, i < n → u i < D i)
    (hDcut : ∀ i, i ≤ n → Dcut ≤ D i)
    (hbaseCap : ∀ P : PairOn V, ∀ i, i ≤ n →
      sharpScheduledPairUpperTarget S₀ Mschedule d u P i + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hbaseFloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (delta : ℝ) ≤
        sharpScheduledPairLowerTarget S₀ D u Kinc P i - aPair)
    (hscheduledCap : ∀ P : PairOn V, ∀ i, i ≤ n →
      sharpScheduledPairUpperTarget S₀ Mschedule d u P i + aPair ≤
        ((u i + 1 : ℕ) : ℝ))
    (hscheduledFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1 S₀ →
        (d i : ℝ) ≤
          sharpScheduledPairLowerTarget S₀ D u Kinc P i - aPair)
    (hDschedule : ∀ i, i ≤ n →
      D i ≤ (Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * d i / 3)
    (hMschedule : ∀ i, i ≤ n →
      ((Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * u i) / 3 ≤ Mschedule i)
    (hdone : ∀ i, i < n → 1 ≤ d i)
    (hsmall : ∀ i, i < n → 3 + Kpair < d i)
    (hupperJump : ∀ i, i < n →
      sharpScheduledPairUpperRate (Mschedule i) (d i) (u i) ≤ JUpper)
    (hlowerDeath : ∀ i, i < n →
      sharpScheduledPairLowerRate (D i) (u i) Kinc ≤ d i)
    (hvarianceUpper : ∀ i, i < n →
      sharpScheduledPairUpperVariance (D i) (u i) Kpair Kglobal
        (sharpScheduledPairUpperRate (Mschedule i) (d i) (u i)) ≤ vPair)
    (hvarianceLower : ∀ i, i < n →
      sharpScheduledPairLowerVariance (D i) (u i) Kpair Kinc
        (sharpScheduledPairLowerRate (D i) (u i) Kinc) ≤ vPair)
    (htheta : 0 < thetaPair)
    (hthetaUpper : thetaPair * (JUpper : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ vPair)
    (hscale : 1 ≤ scale)
    (hscaleRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hratio : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ rate) :
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut D d Mschedule u
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      sharpScheduledAbsorberPhaseFailure q M n sPair sGlobal sInc
        Kpair Kglobal Kinc I H X B scale thetaPair aPair vPair := by
  classical
  dsimp only
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut D d Mschedule u
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let epairR : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp
      (-thetaPair * aPair + thetaPair ^ 2 * (n : ℝ) * vPair))
  let epair : ℝ≥0 := ⟨epairR, by dsimp only [epairR]; positivity⟩
  let epairTwo : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    (Fintype.card (PairOn V) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (scale ^ q *
          (pairTwoAwayThreatExtensionCoefficient q B : ℕ))
  let eglobal : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    pairTwoAwayTail q sGlobal Kglobal
      (scale ^ q *
        (twoAwayThreatExtensionCoefficient q M H X B : ℕ))
  let einc : ℝ≥0 := (Fintype.card (PairOn V) : ℝ≥0) *
    aggregatePairTwoAwayTail q sInc Kinc
      (scale ^ q *
        ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2))
  let etotal : ℝ≥0 := scaledTotalTwoAwayExpectationEnvelope q M H X B scale /
    ((I + 1 : ℕ) : ℝ≥0)
  have hpairReal : (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation
            (sharpScheduledPairUpperTarget S₀ Mschedule d u P) S₀ P.1
              z.1.1 z.2 -
          fixedPairUpperDeviation
            (sharpScheduledPairUpperTarget S₀ Mschedule d u P) S₀ P.1
              0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation
            (sharpScheduledPairLowerTarget S₀ D u Kinc P) S₀ P.1
              z.1.1 z.2 -
          fixedPairLowerDeviation
            (sharpScheduledPairLowerTarget S₀ D u Kinc P) S₀ P.1
              0 S₀)) : ℝ) ≤ epairR := by
    simpa only [L, active, epairR] using
      probability_timedSharpScheduledAggregatePairBand_exists_pair_deviation_le
        n F S₀ Kpair Kglobal Kinc Delta delta I Dcut JUpper D d Mschedule u
        thetaPair aPair vPair hAbs₀.1
        (fun i hi ↦ hDpos i (Nat.le_of_lt hi)) hDgap hdone hsmall hupperJump
        hlowerDeath hvarianceUpper hvarianceLower htheta hthetaUpper
        hthetaLower hv
  have hpair : L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation
            (sharpScheduledPairUpperTarget S₀ Mschedule d u P) S₀ P.1
              z.1.1 z.2 -
          fixedPairUpperDeviation
            (sharpScheduledPairUpperTarget S₀ Mschedule d u P) S₀ P.1
              0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation
            (sharpScheduledPairLowerTarget S₀ D u Kinc P) S₀ P.1
              z.1.1 z.2 -
          fixedPairLowerDeviation
            (sharpScheduledPairLowerTarget S₀ D u Kinc P) S₀ P.1
              0 S₀)) ≤ epair := by
    exact_mod_cast hpairReal
  have hpairTwo :
      L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤
        epairTwo := by
    simpa only [L, active, epairTwo, hF, hS₀] using
      (timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local_scaled
        (q := q) (n := n) (s := sPair) (D := Dcut) (K := Kpair)
        (B := B) active rate scale hscale hscaleRate hDcutPos
        (fun _i _S hact ↦ hact.1.1.1.1.2.2) hratio)
  have hglobal :
      L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤
        eglobal := by
    simpa only [L, active, eglobal, hF, hS₀] using
      (timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le_scaled
        (q := q) (M := M) (n := n) (s := sGlobal) (D := Dcut)
        (K := Kglobal) (H := H) (X := X) (B := B) active hA2
        rate scale hscale hscaleRate hDcutPos
        (fun _i _S hact ↦ hact.1.1.1.1.2.2) hratio)
  have hinc :
      L.probability
        (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) ≤
          einc := by
    simpa only [L, active, einc, hF, hS₀] using
      (timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le_scaled
        (q := q) (n := n) (s := sInc) (D := Dcut) (K := Kinc)
        (B := B) active rate scale hscale hscaleRate hDcutPos
        (fun _i _S hact ↦ hact.1.1.1.1.2.2) hratio)
  have htotal : L.probability
      (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) ≤ etotal := by
    simpa only [L, active, etotal, hF, hS₀] using
      (timedStoppedAbsorberGreedy_probability_totalTwoAway_gt_le_scaled
        (q := q) (M := M) (n := n) (D := Dcut) (I := I)
        (H := H) (X := X) (B := B) active hA2
        rate scale hscale hscaleRate hDcutPos
        (fun _i _S hact ↦ hact.1.1.1.1.2.2) hratio)
  have hsum := probability_timedSharpScheduledAggregatePairBand_not_active_le_sum_outerOnly
    n F G U A S₀ Kpair Kglobal Kinc Delta delta I Dcut D d Mschedule u
      aPair epair epairTwo eglobal einc etotal hAbs₀ htri houtside₀ hchosen₀
      hsmallBase hDpos hDcut hbaseCap hbaseFloor hscheduledCap
      hscheduledFloor hDschedule hMschedule hpair hpairTwo hglobal hinc htotal
  simpa only [L, active, sharpScheduledAbsorberPhaseFailure, epair,
    epairR, epairTwo, eglobal, einc, etotal] using hsum

end

end Erdos207
