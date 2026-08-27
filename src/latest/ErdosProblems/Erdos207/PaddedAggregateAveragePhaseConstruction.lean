/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AggregateAverageAbsorberCoefficientBounds
import ErdosProblems.Erdos207.PaddedAveragePhaseConstruction

/-! # The corrected scalar averaged phase on the padded absorber -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def paddedAggregatePairVariance
    (delta Delta Kpair Kglobal Kinc D : ℕ) : ℝ :=
  max
    (linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal D
      (pairUpperRateBound delta Delta : ℕ))
    (linearPairAggregateVarianceBudget Delta Kpair Kinc D
      (pairAggregateLowerLinearRate Delta Kinc D))

lemma paddedAggregatePairVariance_nonneg
    (delta Delta Kpair Kglobal Kinc D : ℕ) :
    0 ≤ paddedAggregatePairVariance delta Delta Kpair Kglobal Kinc D := by
  unfold paddedAggregatePairVariance
  have hnonneg : 0 ≤
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal D
        (pairUpperRateBound delta Delta : ℕ) := by
    unfold linearPairVarianceBudgetTwoCutoffs
    positivity
  exact hnonneg.trans (le_max_left _ _)

lemma linearPairVarianceBudget_upper_le_paddedAggregate
    {V : Type*} [Fintype V] [DecidableEq V]
    (S0 : GreedyStateOn V) (delta Delta Kpair Kglobal Kinc D : ℕ) :
    linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal D
        (pairUpperLinearRate S0 delta Delta) ≤
      paddedAggregatePairVariance delta Delta Kpair Kglobal Kinc D := by
  have hrnonneg := pairUpperLinearRate_nonneg S0 delta Delta
  have hrle := pairUpperLinearRate_le_bound S0 delta Delta
  have hsquare : (pairUpperLinearRate S0 delta Delta) ^ 2 ≤
      ((pairUpperRateBound delta Delta : ℕ) : ℝ) ^ 2 := by nlinarith
  apply le_trans (b := linearPairVarianceBudgetTwoCutoffs
    Delta Kpair Kglobal D (pairUpperRateBound delta Delta : ℕ))
  · unfold linearPairVarianceBudgetTwoCutoffs
    linarith
  · exact le_max_left _ _

lemma linearPairAggregateVarianceBudget_lower_le_paddedAggregate
    (delta Delta Kpair Kglobal Kinc D : ℕ) :
    linearPairAggregateVarianceBudget Delta Kpair Kinc D
        (pairAggregateLowerLinearRate Delta Kinc D) ≤
      paddedAggregatePairVariance delta Delta Kpair Kglobal Kinc D :=
  le_max_right _ _

theorem exists_paddedAbsorber_linearAggregateAveragedPhase
    {q m n phaseSteps sPair sGlobal sInc Kpair Kglobal Kinc
      Delta delta I D L : ℕ}
    (aPair aAvail : ℝ)
    (hq : 4 ≤ q) (hm : 3 ≤ m)
    (hmC : m ≤ paddedAbsorberSize q m)
    (hfit : paddedAbsorberSize q m ≤ n)
    (hLpos : 0 < L)
    (hinitialBuffer : L + 3 * paddedAbsorberSize q m + 2 ≤ n)
    (havailabilityBuffer :
      (6 : ℝ) *
          ((D : ℝ) +
            (phaseSteps : ℝ) * averageAvailabilityLossRate Delta I D +
              aAvail) ≤
        (((n - paddedAbsorberSize q m) *
          (n - (paddedAbsorberSize q m + 1)) * L : ℕ) : ℝ))
    (hinitialCapScalar :
      (n : ℝ) + aPair ≤ ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloorScalar :
      (delta : ℝ) + aPair +
          (phaseSteps : ℝ) * pairAggregateLowerLinearRate Delta Kinc D ≤
        ((n - 2 - 3 * paddedAbsorberSize q m : ℕ) : ℝ))
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hD : 0 < D)
    (hlowerDeath : pairAggregateLowerLinearRate Delta Kinc D ≤ (delta : ℝ))
    (hratio : (phaseSteps : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (n + 1 : ℝ≥0)⁻¹)
    (hsmall : paddedAggregateAveragePhaseFailureUpper q
      (paddedAbsorberLocalization q) (paddedAbsorberSize q m)
      (paddedAbsorberBankSize q m) n phaseSteps sPair sGlobal sInc
      Kpair Kglobal Kinc I
      (paddedPairTheta delta Delta Kpair) aPair
      (paddedAggregatePairVariance delta Delta Kpair Kglobal Kinc D)
      (paddedAvailabilityTheta Delta Kglobal) aAvail
      (paddedAvailabilityVariance Delta Kglobal I D) < 1) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystem n, ∃ S : GreedyStateOn (Fin n),
        X.card = m ∧
        HasHighGirthAbsorptionBank q H X B ∧
        HasAbsorberLocalization q (paddedAbsorberLocalization q) H X B ∧
        BankPairsSupported H X B ∧
        AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B) S ∧
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
        D ≤ S.available.card ∧ S.chosen.card = phaseSteps := by
  obtain ⟨H, X, B, hXcard, hA1, hA2, hbank, hBsupport,
      hHsupport, hdegree, hBcard⟩ :=
    exists_paddedRealizableAbsorber (q := q) (n := n) (m := m) (by omega)
      (by simpa only [paddedAbsorberSize] using hfit)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A := outsideAvailableTriangles H B
  let S0 := absorberGreedyInitialState F A
  let thetaPair := paddedPairTheta delta Delta Kpair
  let vPair := paddedAggregatePairVariance
    delta Delta Kpair Kglobal Kinc D
  let thetaAvail := paddedAvailabilityTheta Delta Kglobal
  let vAvail := paddedAvailabilityVariance Delta Kglobal I D
  have hXthree : 3 ≤ X.card := by omega
  have hXbound : X.card ≤ paddedAbsorberSize q m := by omega
  have hlarge : 3 * paddedAbsorberSize q m + 3 ≤ n := by omega
  have houtside0 : OutsideLeavePairsAlive H X S0 := by
    dsimp only [S0, F, A]
    exact outsideLeavePairsAlive_initial hbank hdegree
      (by simpa only [paddedAbsorberSize] using hBsupport)
      (by simpa only [paddedAbsorberSize, Fintype.card_fin] using hlarge)
  have hglobal := initial_globalAvailability_lower
    (q := q) (L := L) hbank hdegree
      (by simpa only [paddedAbsorberSize] using hBsupport)
      hXbound (by simpa only [paddedAbsorberSize, Fintype.card_fin]
        using hinitialBuffer)
  have hglobalReal :
      ((((n - paddedAbsorberSize q m) *
          (n - (paddedAbsorberSize q m + 1)) * L : ℕ) : ℝ)) ≤
        6 * (S0.available.card : ℝ) := by
    exact_mod_cast (by
      simpa only [paddedAbsorberSize, Fintype.card_fin, S0, F, A]
        using hglobal)
  have hratenonneg : 0 ≤ averageAvailabilityLossRate Delta I D := by
    unfold averageAvailabilityLossRate
    positivity
  have hbuffer : ∀ i, i ≤ phaseSteps →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Delta I D + aAvail ≤
        (S0.available.card : ℝ) := by
    intro i hi
    have hiReal : (i : ℝ) ≤ (phaseSteps : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * averageAvailabilityLossRate Delta I D ≤
        (phaseSteps : ℝ) * averageAvailabilityLossRate Delta I D :=
      mul_le_mul_of_nonneg_right hiReal hratenonneg
    nlinarith [havailabilityBuffer, hglobalReal]
  have hinitialCap : ∀ P : PairOn (Fin n),
      fixedPairAvailableCountReal S0 P.1 S0 + aPair ≤
        ((Delta + 1 : ℕ) : ℝ) := by
    intro P
    have hcut := initial_hasAvailablePairCutoff_card F A P.1 P.2
    have hcount : fixedPairAvailableCountReal S0 P.1 S0 =
        (availableTrianglesContainingPair S0 P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    have hcutReal :
        ((availableTrianglesContainingPair S0 P.1).card : ℝ) ≤ (n : ℝ) := by
      simpa only [Fintype.card_fin] using (show
        ((availableTrianglesContainingPair S0 P.1).card : ℝ) ≤
          (Fintype.card (Fin n) : ℝ) by exact_mod_cast hcut)
    linarith
  have hfinalFloor : ∀ P : PairOn (Fin n), PairAlive P.1 S0 →
      (delta : ℝ) + aPair +
          (phaseSteps : ℝ) * pairAggregateLowerLinearRate Delta Kinc D ≤
        fixedPairAvailableCountReal S0 P.1 S0 := by
    intro P hPalive
    have hlocal := initialPairStar_lower_of_alive hq hA1 hXthree hbank hdegree
      (by simpa only [paddedAbsorberSize] using hBsupport) P hPalive
    have hnat : n - 2 - 3 * paddedAbsorberSize q m ≤
        (availableTrianglesContainingPair S0 P.1).card := by
      dsimp only [S0, F, A] at hlocal ⊢
      simp only [Fintype.card_fin] at hlocal
      unfold paddedAbsorberSize
      omega
    have hreal : ((n - 2 - 3 * paddedAbsorberSize q m : ℕ) : ℝ) ≤
        ((availableTrianglesContainingPair S0 P.1).card : ℝ) := by
      exact_mod_cast hnat
    have hcount : fixedPairAvailableCountReal S0 P.1 S0 =
        (availableTrianglesContainingPair S0 P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    linarith
  have hupperJump : pairUpperLinearRate S0 delta Delta ≤
      (pairUpperRateBound delta Delta : ℝ) :=
    pairUpperLinearRate_le_bound S0 delta Delta
  have hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal D
          (pairUpperLinearRate S0 delta Delta) ≤ vPair := by
    exact linearPairVarianceBudget_upper_le_paddedAggregate
      S0 delta Delta Kpair Kglobal Kinc D
  have hvarianceLower :
      linearPairAggregateVarianceBudget Delta Kpair Kinc D
          (pairAggregateLowerLinearRate Delta Kinc D) ≤ vPair := by
    exact linearPairAggregateVarianceBudget_lower_le_paddedAggregate
      delta Delta Kpair Kglobal Kinc D
  have hsmallActual : aggregateAveragedAbsorberPhaseFailure q
      (paddedAbsorberLocalization q) phaseSteps sPair sGlobal sInc
      Kpair Kglobal Kinc I H X B thetaPair aPair vPair
      thetaAvail aAvail vAvail < 1 := by
    apply (aggregateAveragedAbsorberPhaseFailure_le
      thetaPair aPair vPair thetaAvail aAvail vAvail
      (V := Fin n) (H := H) (X := X) (B := B)
      (c := paddedAbsorberSize q m) (b := paddedAbsorberBankSize q m)
      (phaseSteps := phaseSteps) (sPair := sPair) (sGlobal := sGlobal)
      (sInc := sInc) (Kpair := Kpair) (Kglobal := Kglobal)
      (Kinc := Kinc) (I := I) (n := n)
      (M := paddedAbsorberLocalization q) (q := q) (by simp) hHsupport
      (by simpa only [paddedAbsorberBankSize, paddedAbsorberSize] using
        hBcard)).trans_lt
    simpa only [thetaPair, vPair, thetaAvail, vAvail] using hsmall
  obtain ⟨S, hSAbs, houtside, hpair, hfloor, hpairTwo, hglobalTwo,
      hinc, htotal, havailable, hcard⟩ :=
    exists_linearAggregateAveragedAbsorberGreedy_phase
      thetaPair aPair vPair thetaAvail aAvail vAvail
      (by simpa only [paddedAbsorberLocalization] using hA2)
      (by simpa only [F, A, S0] using houtside0) hD
      (by simpa only [Fintype.card_fin] using hratio)
      (by simpa only [F, A, S0] using hbuffer)
      (by simpa only [F, A, S0] using hinitialCap)
      (by simpa only [F, A, S0] using hfinalFloor)
      hdelta hsmallPair hupperJump hlowerDeath hvarianceUpper hvarianceLower
      (paddedPairTheta_pos delta Delta Kpair)
      (paddedPairTheta_mul_upper_le_one delta Delta Kpair)
      (paddedPairTheta_mul_lower_le_one delta Delta Kpair)
      (paddedAggregatePairVariance_nonneg
        delta Delta Kpair Kglobal Kinc D)
      (by exact le_refl _)
      (paddedAvailabilityTheta_pos Delta Kglobal)
      (paddedAvailabilityTheta_mul_jump_le_one Delta Kglobal)
      (paddedAvailabilityVariance_nonneg Delta Kglobal I D)
      hsmallActual
  exact ⟨H, X, B, S, hXcard, hA1, hA2, hbank, hSAbs, houtside,
    hpair, hfloor, hpairTwo, hglobalTwo, hinc, htotal, havailable, hcard⟩

end

end Erdos207
