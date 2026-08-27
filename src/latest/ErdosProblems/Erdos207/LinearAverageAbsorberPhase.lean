/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AverageAbsorberPhase
import ErdosProblems.Erdos207.LinearPairTrajectories

/-!
# Explicit linear trajectories for the averaged absorber phase

This file discharges every process-dependent drift and variance hypothesis of
`exists_averagedAbsorberGreedy_phase`.  The resulting interface contains only
initial-state bounds, scalar buffers, and the five-term failure inequality.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The five-event averaged phase with the concrete linear pair targets. -/
theorem exists_linearAveragedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal Kpair Kglobal Δ δ I D JUpper : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
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
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A)
          P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) + aPair ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V,
      PairAlive P.1
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A) →
      (δ : ℝ) + aPair +
          (n : ℝ) * pairLowerLinearRate Δ Kglobal D ≤
        fixedPairAvailableCountReal
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A)
          P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A))
    (hδ : 1 ≤ δ) (hsmallPair : 3 + Kpair < δ)
    (hupperJump :
      pairUpperLinearRate
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) δ Δ ≤
        (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ Kglobal D ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal D
          (pairUpperLinearRate
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) δ Δ) ≤
        vPair)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal D
          (pairLowerLinearRate Δ Kglobal D) ≤ vPair)
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
  let rUpper := pairUpperLinearRate S₀ δ Δ
  let rLower := pairLowerLinearRate Δ Kglobal D
  let qUpper := linearPairTarget S₀ rUpper
  let qLower := linearPairTarget S₀ rLower
  have hrUpper : 0 ≤ rUpper := pairUpperLinearRate_nonneg S₀ δ Δ
  have hrLower : 0 ≤ rLower := pairLowerLinearRate_nonneg Δ Kglobal D
  apply exists_averagedAbsorberGreedy_phase qUpper qLower
    thetaPair aPair vPair thetaAvail aAvail vAvail hA2
      (by simpa only [F, S₀] using houtside₀) hD hratio
      (by simpa only [F, S₀] using havailabilityBuffer)
  · intro P i _hi
    have hmul : 0 ≤ (i : ℝ) * rUpper :=
      mul_nonneg (by positivity) hrUpper
    simpa only [qUpper, linearPairTarget_zero, linearPairTarget, F, S₀]
      using (show
        fixedPairAvailableCountReal S₀ P.1 S₀ - (i : ℝ) * rUpper +
            (fixedPairAvailableCountReal S₀ P.1 S₀ -
              fixedPairAvailableCountReal S₀ P.1 S₀) + aPair ≤
          ((Δ + 1 : ℕ) : ℝ) by
        linarith [hinitialCap P])
  · intro P i hi halive₀
    have hiReal : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * rLower ≤ (n : ℝ) * rLower :=
      mul_le_mul_of_nonneg_right hiReal hrLower
    simp only [qLower, linearPairTarget_zero, linearPairTarget, F, S₀]
    linarith [hfinalFloor P (by simpa only [F, S₀] using halive₀)]
  · exact hδ
  · exact hsmallPair
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    simpa only [rUpper] using neg_le_neg hupperJump
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
        F Kpair Kglobal Δ δ (fun _ ↦ D) i S :=
      ⟨hactive.1, hactive.2.2⟩
    exact linearPairUpperTarget_drift_twoCutoffs hS hold halive
  · intro P i _hi S _hS hactive _halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ (fun _ ↦ D) i S :=
      ⟨hactive.1, hactive.2.2⟩
    exact linearPairLowerTarget_drift_twoCutoffs hold hD (le_refl D)
  · intro P i _hi S _hS hactive _halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ (fun _ ↦ D) i S :=
      ⟨hactive.1, hactive.2.2⟩
    exact (linearPairTarget_variance_le_twoCutoffs rUpper hold hD
      (le_refl D)).trans (by simpa only [rUpper, F, S₀] using hvarianceUpper)
  · intro P i _hi S _hS hactive _halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ (fun _ ↦ D) i S :=
      ⟨hactive.1, hactive.2.2⟩
    exact (linearPairTarget_variance_le_twoCutoffs rLower hold hD
      (le_refl D)).trans (by simpa only [rLower] using hvarianceLower)
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
