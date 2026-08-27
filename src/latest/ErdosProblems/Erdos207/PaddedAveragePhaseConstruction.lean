/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AverageAbsorberCoefficientBounds
import ErdosProblems.Erdos207.PaddedPairPhaseConstruction

/-!
# A scalar averaged phase on the padded absorber

This is the finite construction boundary for the long initial phase.  The
absorber is existentially embedded first; all later choices use uniform
natural-number coefficient bounds.  Both concentration parameters and both
variance budgets are fixed by explicit formulas.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A bounded-jump exponential parameter for total availability. -/
def paddedAvailabilityTheta (Δ Kglobal : ℕ) : ℝ :=
  (((3 * Δ + Kglobal + 1 : ℕ) : ℝ))⁻¹

/-- The exact scalar variance budget used for total availability. -/
def paddedAvailabilityVariance (Δ Kglobal I D : ℕ) : ℝ :=
  2 * ((3 * Δ + Kglobal : ℕ) : ℝ) *
      averageAvailabilityLossRate Δ I D +
    2 * (averageAvailabilityLossRate Δ I D) ^ 2

lemma paddedAvailabilityTheta_pos (Δ Kglobal : ℕ) :
    0 < paddedAvailabilityTheta Δ Kglobal := by
  unfold paddedAvailabilityTheta
  positivity

lemma paddedAvailabilityTheta_mul_jump_le_one (Δ Kglobal : ℕ) :
    paddedAvailabilityTheta Δ Kglobal *
        ((3 * Δ + Kglobal : ℕ) : ℝ) ≤ 1 := by
  unfold paddedAvailabilityTheta
  have hpos : (0 : ℝ) < (3 * Δ + Kglobal + 1 : ℕ) := by
    exact_mod_cast (show 0 < 3 * Δ + Kglobal + 1 by omega)
  rw [inv_mul_le_one₀ hpos]
  exact_mod_cast (show 3 * Δ + Kglobal ≤ 3 * Δ + Kglobal + 1 by omega)

lemma paddedAvailabilityVariance_nonneg (Δ Kglobal I D : ℕ) :
    0 ≤ paddedAvailabilityVariance Δ Kglobal I D := by
  unfold paddedAvailabilityVariance averageAvailabilityLossRate
  positivity

/-- The realizable padded absorber together with the scalar five-event
inequality produces a genuine full averaged phase. -/
theorem exists_paddedAbsorber_linearAveragedPhase
    {q m n phaseSteps sPair sGlobal Kpair Kglobal Δ δ I D L : ℕ}
    (aPair aAvail : ℝ)
    (hq : 4 ≤ q) (hm : 3 ≤ m)
    (hmC : m ≤ paddedAbsorberSize q m)
    (hfit : paddedAbsorberSize q m ≤ n)
    (hLpos : 0 < L)
    (hinitialBuffer :
      L + 3 * paddedAbsorberSize q m + 2 ≤ n)
    (havailabilityBuffer :
      (6 : ℝ) *
          ((D : ℝ) +
            (phaseSteps : ℝ) * averageAvailabilityLossRate Δ I D +
              aAvail) ≤
        (((n - paddedAbsorberSize q m) *
          (n - (paddedAbsorberSize q m + 1)) * L : ℕ) : ℝ))
    (hinitialCapScalar :
      (n : ℝ) + aPair ≤ ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloorScalar :
      (δ : ℝ) + aPair +
          (phaseSteps : ℝ) * pairLowerLinearRate Δ Kglobal D ≤
        ((n - 2 - 3 * paddedAbsorberSize q m : ℕ) : ℝ))
    (hδ : 1 ≤ δ) (hsmallPair : 3 + Kpair < δ)
    (hD : 0 < D)
    (hlowerDeath : pairLowerLinearRate Δ Kglobal D ≤ (δ : ℝ))
    (hratio : (phaseSteps : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (n + 1 : ℝ≥0)⁻¹)
    (hsmall : paddedAveragePhaseFailureUpper q
      (paddedAbsorberLocalization q) (paddedAbsorberSize q m)
      (paddedAbsorberBankSize q m) n phaseSteps sPair sGlobal
      Kpair Kglobal I
      (paddedPairTheta δ Δ Kpair) aPair
      (paddedPairVariance δ Δ Kpair Kglobal D)
      (paddedAvailabilityTheta Δ Kglobal) aAvail
      (paddedAvailabilityVariance Δ Kglobal I D) < 1) :
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
        HasAvailablePairCutoff Δ S ∧
        HasAvailablePairFloor δ S ∧
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        totalAvailableTwoAwayIncidences
          (absorberErdosForbiddenConfigurationsOn q B) S ≤ I ∧
        D ≤ S.available.card ∧
        S.chosen.card = phaseSteps := by
  obtain ⟨H, X, B, hXcard, hA1, hA2, hbank, hBsupport,
      hHsupport, hdegree, hBcard⟩ :=
    exists_paddedRealizableAbsorber (q := q) (n := n)
      (m := m) (by omega)
      (by simpa only [paddedAbsorberSize] using hfit)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A := outsideAvailableTriangles H B
  let S₀ := absorberGreedyInitialState F A
  let thetaPair := paddedPairTheta δ Δ Kpair
  let vPair := paddedPairVariance δ Δ Kpair Kglobal D
  let thetaAvail := paddedAvailabilityTheta Δ Kglobal
  let vAvail := paddedAvailabilityVariance Δ Kglobal I D
  have hXthree : 3 ≤ X.card := by omega
  have hXbound : X.card ≤ paddedAbsorberSize q m := by omega
  have hlarge : 3 * paddedAbsorberSize q m + 3 ≤ n := by omega
  have houtside₀ : OutsideLeavePairsAlive H X S₀ := by
    dsimp only [S₀, F, A]
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
        6 * (S₀.available.card : ℝ) := by
    exact_mod_cast (by
      simpa only [paddedAbsorberSize, Fintype.card_fin, S₀, F, A]
        using hglobal)
  have hratenonneg : 0 ≤ averageAvailabilityLossRate Δ I D := by
    unfold averageAvailabilityLossRate
    positivity
  have hbuffer : ∀ i, i ≤ phaseSteps →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Δ I D + aAvail ≤
        (S₀.available.card : ℝ) := by
    intro i hi
    have hiReal : (i : ℝ) ≤ (phaseSteps : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * averageAvailabilityLossRate Δ I D ≤
        (phaseSteps : ℝ) * averageAvailabilityLossRate Δ I D :=
      mul_le_mul_of_nonneg_right hiReal hratenonneg
    nlinarith [havailabilityBuffer, hglobalReal]
  have hinitialCap : ∀ P : PairOn (Fin n),
      fixedPairAvailableCountReal S₀ P.1 S₀ + aPair ≤
        ((Δ + 1 : ℕ) : ℝ) := by
    intro P
    have hcut := initial_hasAvailablePairCutoff_card F A P.1 P.2
    have hcount : fixedPairAvailableCountReal S₀ P.1 S₀ =
        (availableTrianglesContainingPair S₀ P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    have hcutReal :
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) ≤
          (n : ℝ) := by
      simpa only [Fintype.card_fin] using (show
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) ≤
          (Fintype.card (Fin n) : ℝ) by exact_mod_cast hcut)
    linarith
  have hfinalFloor : ∀ P : PairOn (Fin n), PairAlive P.1 S₀ →
      (δ : ℝ) + aPair +
          (phaseSteps : ℝ) * pairLowerLinearRate Δ Kglobal D ≤
        fixedPairAvailableCountReal S₀ P.1 S₀ := by
    intro P hPalive
    have hlocal := initialPairStar_lower_of_alive hq hA1 hXthree
      hbank hdegree
      (by simpa only [paddedAbsorberSize] using hBsupport) P hPalive
    have hnat : n - 2 - 3 * paddedAbsorberSize q m ≤
        (availableTrianglesContainingPair S₀ P.1).card := by
      dsimp only [S₀, F, A] at hlocal ⊢
      simp only [Fintype.card_fin] at hlocal
      unfold paddedAbsorberSize
      omega
    have hreal : ((n - 2 - 3 * paddedAbsorberSize q m : ℕ) : ℝ) ≤
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) := by
      exact_mod_cast hnat
    have hcount : fixedPairAvailableCountReal S₀ P.1 S₀ =
        (availableTrianglesContainingPair S₀ P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    linarith
  have hupperJump : pairUpperLinearRate S₀ δ Δ ≤
      (pairUpperRateBound δ Δ : ℝ) :=
    pairUpperLinearRate_le_bound S₀ δ Δ
  have hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal D
          (pairUpperLinearRate S₀ δ Δ) ≤ vPair := by
    exact linearPairVarianceBudget_upper_le_padded
      S₀ δ Δ Kpair Kglobal D
  have hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal D
          (pairLowerLinearRate Δ Kglobal D) ≤ vPair := by
    exact linearPairVarianceBudget_lower_le_padded
      δ Δ Kpair Kglobal D
  have hsmallActual : averagedAbsorberPhaseFailure q
      (paddedAbsorberLocalization q) phaseSteps sPair sGlobal
      Kpair Kglobal I H X B thetaPair aPair vPair
        thetaAvail aAvail vAvail < 1 := by
    apply (averagedAbsorberPhaseFailure_le
      thetaPair aPair vPair thetaAvail aAvail vAvail
      (V := Fin n) (H := H) (X := X) (B := B)
      (c := paddedAbsorberSize q m)
      (b := paddedAbsorberBankSize q m)
      (phaseSteps := phaseSteps) (sPair := sPair) (sGlobal := sGlobal)
      (Kpair := Kpair) (Kglobal := Kglobal) (I := I)
      (n := n) (M := paddedAbsorberLocalization q) (q := q)
      (by simp) hHsupport
      (by simpa only [paddedAbsorberBankSize, paddedAbsorberSize] using
        hBcard)).trans_lt
    simpa only [thetaPair, vPair, thetaAvail, vAvail] using hsmall
  obtain ⟨S, hSAbs, houtside, hpair, hfloor, hpairTwo, hglobalTwo,
      htotal, havailable, hcard⟩ :=
    exists_linearAveragedAbsorberGreedy_phase
      thetaPair aPair vPair thetaAvail aAvail vAvail
      (by simpa only [paddedAbsorberLocalization] using hA2)
      (by simpa only [F, A, S₀] using houtside₀) hD
      (by simpa only [Fintype.card_fin] using hratio)
      (by simpa only [F, A, S₀] using hbuffer)
      (by simpa only [F, A, S₀] using hinitialCap)
      (by simpa only [F, A, S₀] using hfinalFloor)
      hδ hsmallPair hupperJump hlowerDeath hvarianceUpper hvarianceLower
      (paddedPairTheta_pos δ Δ Kpair)
      (paddedPairTheta_mul_upper_le_one δ Δ Kpair)
      (paddedPairTheta_mul_lower_le_one δ Δ Kpair)
      (paddedPairVariance_nonneg δ Δ Kpair Kglobal D)
      (by exact le_refl _)
      (paddedAvailabilityTheta_pos Δ Kglobal)
      (paddedAvailabilityTheta_mul_jump_le_one Δ Kglobal)
      (paddedAvailabilityVariance_nonneg Δ Kglobal I D)
      hsmallActual
  exact ⟨H, X, B, S, hXcard, hA1, hA2, hbank, hSAbs, houtside,
    hpair, hfloor, hpairTwo, hglobalTwo, htotal, havailable, hcard⟩

end

end Erdos207
