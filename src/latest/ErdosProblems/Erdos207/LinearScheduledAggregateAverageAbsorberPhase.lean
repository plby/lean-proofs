/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RealFloorSchedules

/-!
# Explicit linear trajectories with real-floor survival schedules
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_linearScheduledAggregateAveragedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut
      JUpper d₀ : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
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
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V,
      PairAlive P.1
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) →
      (delta : ℝ) + aPair +
          (n : ℝ) * pairAggregateLowerLinearRate Delta Kinc Dcut ≤
        fixedPairAvailableCountReal
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A))
    (hinitialPairFloor : HasAvailablePairFloor d₀
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A))
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hupperJump :
      pairUpperLinearRate
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) delta Delta ≤
        (JUpper : ℝ))
    (hlowerDeath :
      pairAggregateLowerLinearRate Delta Kinc Dcut ≤ (delta : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dcut
          (pairUpperLinearRate
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) delta Delta) ≤
        vPair)
    (hvarianceLower :
      linearPairAggregateVarianceBudget Delta Kpair Kinc Dcut
          (pairAggregateLowerLinearRate Delta Kinc Dcut) ≤ vPair)
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
    let S₀ := absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A
    let availabilityRate := averageAvailabilityLossRate Delta I Dcut
    let pairRate := pairAggregateLowerLinearRate Delta Kinc Dcut
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
        Dcut ≤ S.available.card ∧
        realLinearFloorSchedule (S₀.available.card : ℝ)
          availabilityRate aAvail n ≤ S.available.card ∧
        HasAvailablePairFloor
          (realLinearFloorSchedule (d₀ : ℝ) pairRate aPair n) S ∧
        S.chosen.card = n := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let rUpper := pairUpperLinearRate S₀ delta Delta
  let rLower := pairAggregateLowerLinearRate Delta Kinc Dcut
  let availabilityRate := averageAvailabilityLossRate Delta I Dcut
  let qUpper := linearPairTarget S₀ rUpper
  let qLower := linearPairTarget S₀ rLower
  let Dschedule := realLinearFloorSchedule
    (S₀.available.card : ℝ) availabilityRate aAvail
  let dschedule := realLinearFloorSchedule (d₀ : ℝ) rLower aPair
  have hrUpper : 0 ≤ rUpper := pairUpperLinearRate_nonneg S₀ delta Delta
  have hrLower : 0 ≤ rLower :=
    pairAggregateLowerLinearRate_nonneg Delta Kinc Dcut
  apply exists_scheduledAggregateAveragedAbsorberGreedy_phase
    Dschedule dschedule qUpper qLower
    thetaPair aPair vPair thetaAvail aAvail vAvail hA2
    (by simpa only [F, S₀] using houtside₀) hDcut hratio
    (by simpa only [F, S₀] using havailabilityBuffer)
  · intro P i _hi
    have hmul : 0 ≤ (i : ℝ) * rUpper := mul_nonneg (by positivity) hrUpper
    simpa only [qUpper, linearPairTarget_zero, linearPairTarget, F, S₀] using
      (show fixedPairAvailableCountReal S₀ P.1 S₀ - (i : ℝ) * rUpper +
          (fixedPairAvailableCountReal S₀ P.1 S₀ -
            fixedPairAvailableCountReal S₀ P.1 S₀) + aPair ≤
          ((Delta + 1 : ℕ) : ℝ) by
        linarith [hinitialCap P])
  · intro P i hi halive₀
    have hiReal : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * rLower ≤ (n : ℝ) * rLower :=
      mul_le_mul_of_nonneg_right hiReal hrLower
    simp only [qLower, linearPairTarget_zero, linearPairTarget, F, S₀]
    linarith [hfinalFloor P (by simpa only [F, S₀] using halive₀)]
  · intro i S _hi htraj hdev
    exact availabilityDeficit_implies_realLinearFloorSchedule hdev
  · intro P i S _hi htraj halive hdev
    exact linearPairDeviation_implies_realLinearFloorSchedule
      htraj.2 halive (by simpa only [F, S₀] using hinitialPairFloor) hdev
  · exact hdelta
  · exact hsmallPair
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    simpa only [rUpper, F, S₀] using neg_le_neg hupperJump
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    linarith
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S₀ rLower P i]
    simpa only [rLower] using neg_le_neg hlowerDeath
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S₀ rLower P i]
    linarith
  · intro P i _hi S hS hactive halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Delta delta (fun _ ↦ Dcut) i S :=
      ⟨hactive.1.1, hactive.1.2.2⟩
    exact linearPairUpperTarget_drift_twoCutoffs hS hold halive
  · intro P i _hi S _hS hactive _halive
    exact linearPairAggregateLowerTarget_drift hactive hDcut (le_refl Dcut)
  · intro P i _hi S _hS hactive _halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Delta delta (fun _ ↦ Dcut) i S :=
      ⟨hactive.1.1, hactive.1.2.2⟩
    exact (linearPairTarget_variance_le_twoCutoffs rUpper hold hDcut
      (le_refl Dcut)).trans
        (by simpa only [rUpper, F, S₀] using hvarianceUpper)
  · intro P i _hi S _hS hactive _halive
    exact (linearPairTarget_aggregateVariance_le rLower hactive hDcut
      (le_refl Dcut)).trans (by simpa only [rLower] using hvarianceLower)
  · exact hthetaPair
  · exact hthetaUpper
  · exact hthetaLower
  · exact hvPair
  · exact hvarianceAvail
  · exact hthetaAvail
  · exact hthetaAvailJump
  · exact hvAvail
  · exact hsmall

end

end Erdos207
