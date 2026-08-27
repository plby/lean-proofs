/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AggregateAverageAbsorberPhase
import ErdosProblems.Erdos207.LinearPairTrajectories

/-! # Explicit trajectories for the corrected averaged phase -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Uniform lower-envelope rate obtained from the additive aggregate drift. -/
def pairAggregateLowerLinearRate (Delta Kinc Dmin : ℕ) : ℝ :=
  ((Delta * (3 * Delta) + Kinc : ℕ) : ℝ) * (Dmin : ℝ)⁻¹

theorem pairAggregateLowerLinearRate_nonneg (Delta Kinc Dmin : ℕ) :
    0 ≤ pairAggregateLowerLinearRate Delta Kinc Dmin := by
  unfold pairAggregateLowerLinearRate
  positivity

theorem current_pairAggregateRate_le_pairAggregateLowerLinearRate
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {Kpair Kglobal Kinc Delta delta I D Dmin i : ℕ} {P : PairOn V}
    (hactive : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D i S)
    (hDminPos : 0 < Dmin) (hDmin : Dmin ≤ D) :
    (S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * Delta : ℕ) + Kinc) ≤
      pairAggregateLowerLinearRate Delta Kinc Dmin := by
  have hApos : 0 < S.available.card := card_pos.mpr hactive.1.1.1
  have hDminA : Dmin ≤ S.available.card := hDmin.trans hactive.1.2.2
  have hpairNat :
      (availableTrianglesContainingPair S P.1).card ≤ Delta :=
    hactive.1.1.2.1 P.1 P.2
  have hpairReal :
      ((availableTrianglesContainingPair S P.1).card : ℝ) ≤ (Delta : ℝ) := by
    exact_mod_cast hpairNat
  have hDminReal : (Dmin : ℝ) ≤ (S.available.card : ℝ) := by
    exact_mod_cast hDminA
  have hDminPosReal : (0 : ℝ) < (Dmin : ℝ) := by exact_mod_cast hDminPos
  have hAposReal : (0 : ℝ) < (S.available.card : ℝ) := by exact_mod_cast hApos
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (Dmin : ℝ)⁻¹ :=
    (inv_le_inv₀ hAposReal hDminPosReal).mpr hDminReal
  unfold pairAggregateLowerLinearRate
  push_cast
  calc
    (S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          (3 * Delta) + Kinc) ≤
        (Dmin : ℝ)⁻¹ * ((Delta : ℝ) * (3 * Delta) + Kinc) := by
      gcongr
    _ = ((Delta : ℝ) * (3 * Delta) + Kinc) * (Dmin : ℝ)⁻¹ := by ring

theorem linearPairAggregateLowerTarget_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S0 S : GreedyStateOn V}
    {Kpair Kglobal Kinc Delta delta I D Dmin i : ℕ} {P : PairOn V}
    (hactive : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D i S)
    (hDminPos : 0 < Dmin) (hDmin : Dmin ≤ D) :
    linearPairTarget S0 (pairAggregateLowerLinearRate Delta Kinc Dmin)
        P (i + 1) -
      linearPairTarget S0 (pairAggregateLowerLinearRate Delta Kinc Dmin)
        P i ≤
      -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * Delta : ℕ) + Kinc) := by
  rw [linearPairTarget_succ_sub]
  calc
    -pairAggregateLowerLinearRate Delta Kinc Dmin ≤
        -((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * Delta : ℕ) + Kinc)) :=
      neg_le_neg (current_pairAggregateRate_le_pairAggregateLowerLinearRate
        (P := P) hactive hDminPos hDmin)
    _ = -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          (3 * Delta : ℕ) + Kinc) := by ring

/-- Uniform lower-tail second-moment budget for the additive incidence law. -/
def linearPairAggregateVarianceBudget
    (Delta Kpair Kinc Dmin : ℕ) (r : ℝ) : ℝ :=
  2 * ((Dmin : ℝ)⁻¹ * (((3 + Kpair : ℕ) : ℝ) *
      (((Delta : ℝ) * (3 * Delta : ℕ)) + Kinc))) + 2 * r ^ 2

theorem linearPairTarget_aggregateVariance_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S0 S : GreedyStateOn V}
    {Kpair Kglobal Kinc Delta delta I D Dmin i : ℕ} {P : PairOn V}
    (r : ℝ)
    (hactive : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D i S)
    (hDminPos : 0 < Dmin) (hDmin : Dmin ≤ D) :
    2 * ((S.available.card : ℝ)⁻¹ *
        (((3 + Kpair : ℕ) : ℝ) *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * Delta : ℕ) + Kinc))) +
      2 * (linearPairTarget S0 r P (i + 1) -
        linearPairTarget S0 r P i) ^ 2 ≤
      linearPairAggregateVarianceBudget Delta Kpair Kinc Dmin r := by
  rw [linearPairTarget_succ_sub]
  have hApos : 0 < S.available.card := card_pos.mpr hactive.1.1.1
  have hDminA : Dmin ≤ S.available.card := hDmin.trans hactive.1.2.2
  have hpairNat :
      (availableTrianglesContainingPair S P.1).card ≤ Delta :=
    hactive.1.1.2.1 P.1 P.2
  have hpairReal :
      ((availableTrianglesContainingPair S P.1).card : ℝ) ≤ (Delta : ℝ) := by
    exact_mod_cast hpairNat
  have hDminReal : (Dmin : ℝ) ≤ (S.available.card : ℝ) := by
    exact_mod_cast hDminA
  have hDminPosReal : (0 : ℝ) < (Dmin : ℝ) := by exact_mod_cast hDminPos
  have hAposReal : (0 : ℝ) < (S.available.card : ℝ) := by exact_mod_cast hApos
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (Dmin : ℝ)⁻¹ :=
    (inv_le_inv₀ hAposReal hDminPosReal).mpr hDminReal
  unfold linearPairAggregateVarianceBudget
  push_cast
  have hmain :
      (S.available.card : ℝ)⁻¹ *
          ((3 + Kpair : ℝ) *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Delta) + Kinc)) ≤
        (Dmin : ℝ)⁻¹ *
          ((3 + Kpair : ℝ) * ((Delta : ℝ) * (3 * Delta) + Kinc)) := by
    gcongr
  nlinarith

/-- Six-event averaged phase with all pair trajectory obligations discharged. -/
theorem exists_linearAggregateAveragedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I D JUpper : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
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
          (n : ℝ) * pairAggregateLowerLinearRate Delta Kinc D ≤
        fixedPairAvailableCountReal
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A))
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hupperJump :
      pairUpperLinearRate
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B) A) delta Delta ≤
        (JUpper : ℝ))
    (hlowerDeath : pairAggregateLowerLinearRate Delta Kinc D ≤ (delta : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal D
          (pairUpperLinearRate
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B) A) delta Delta) ≤
        vPair)
    (hvarianceLower :
      linearPairAggregateVarianceBudget Delta Kpair Kinc D
          (pairAggregateLowerLinearRate Delta Kinc D) ≤ vPair)
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
  let rUpper := pairUpperLinearRate S0 delta Delta
  let rLower := pairAggregateLowerLinearRate Delta Kinc D
  let qUpper := linearPairTarget S0 rUpper
  let qLower := linearPairTarget S0 rLower
  have hrUpper : 0 ≤ rUpper := pairUpperLinearRate_nonneg S0 delta Delta
  have hrLower : 0 ≤ rLower :=
    pairAggregateLowerLinearRate_nonneg Delta Kinc D
  apply exists_aggregateAveragedAbsorberGreedy_phase qUpper qLower
    thetaPair aPair vPair thetaAvail aAvail vAvail hA2
    (by simpa only [F, S0] using houtside0) hD hratio
    (by simpa only [F, S0] using havailabilityBuffer)
  · intro P i _hi
    have hmul : 0 ≤ (i : ℝ) * rUpper := mul_nonneg (by positivity) hrUpper
    simpa only [qUpper, linearPairTarget_zero, linearPairTarget, F, S0] using
      (show fixedPairAvailableCountReal S0 P.1 S0 - (i : ℝ) * rUpper +
          (fixedPairAvailableCountReal S0 P.1 S0 -
            fixedPairAvailableCountReal S0 P.1 S0) + aPair ≤
          ((Delta + 1 : ℕ) : ℝ) by linarith [hinitialCap P])
  · intro P i hi halive0
    have hiReal : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * rLower ≤ (n : ℝ) * rLower :=
      mul_le_mul_of_nonneg_right hiReal hrLower
    simp only [qLower, linearPairTarget_zero, linearPairTarget, F, S0]
    linarith [hfinalFloor P (by simpa only [F, S0] using halive0)]
  · exact hdelta
  · exact hsmallPair
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S0 rUpper P i]
    simpa only [rUpper] using neg_le_neg hupperJump
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S0 rUpper P i]
    linarith
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S0 rLower P i]
    simpa only [rLower] using neg_le_neg hlowerDeath
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S0 rLower P i]
    linarith
  · intro P i _hi S hS hactive halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Delta delta (fun _ => D) i S :=
      ⟨hactive.1.1, hactive.1.2.2⟩
    exact linearPairUpperTarget_drift_twoCutoffs hS hold halive
  · intro P i _hi S _hS hactive _halive
    exact linearPairAggregateLowerTarget_drift hactive hD (le_refl D)
  · intro P i _hi S _hS hactive _halive
    have hold : timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Delta delta (fun _ => D) i S :=
      ⟨hactive.1.1, hactive.1.2.2⟩
    exact (linearPairTarget_variance_le_twoCutoffs rUpper hold hD
      (le_refl D)).trans (by simpa only [rUpper, F, S0] using hvarianceUpper)
  · intro P i _hi S _hS hactive _halive
    exact (linearPairTarget_aggregateVariance_le rLower hactive hD
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
