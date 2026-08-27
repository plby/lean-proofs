/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PaddedPairPhase
import ErdosProblems.Erdos207.AbsorberCoefficientBounds

/-!
# Constructing the first padded two-cutoff phase

This file combines the realizable padded absorber with the scalar pair-phase
interface.  All choices made after the absorber is produced use uniform
coefficient bounds, so the hypotheses mention only natural-number parameters
and the advertised polynomial padding bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def paddedAbsorberSize (q m : ℕ) : ℕ :=
  highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156

def paddedAbsorberBankSize (q m : ℕ) : ℕ :=
  paddedAbsorberSize q m ^ 3

def paddedAbsorberLocalization (q : ℕ) : ℕ :=
  12 * (q + 2) ^ 2

/-- A crude integral upper bound for the upper linear pair rate. -/
def pairUpperRateBound (delta Delta : ℕ) : ℕ :=
  delta * (3 * delta - 2 - Delta)

/-- A theta which simultaneously satisfies both bounded-jump conditions. -/
def paddedPairTheta (delta Delta Kpair : ℕ) : ℝ :=
  (((pairUpperRateBound delta Delta + (3 + Kpair) + 1 : ℕ) : ℝ))⁻¹

/-- One scalar variance budget dominating both linear pair trajectories. -/
def paddedPairVariance
    (delta Delta Kpair Kglobal Dmin : ℕ) : ℝ :=
  max
    (linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
      (pairUpperRateBound delta Delta : ℕ))
    (linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
      (pairLowerLinearRate Delta Kglobal Dmin))

lemma pairUpperLinearRate_le_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (delta Delta : ℕ) :
    pairUpperLinearRate S₀ delta Delta ≤
      (pairUpperRateBound delta Delta : ℕ) := by
  have hinv : (S₀.available.card : ℝ)⁻¹ ≤ 1 := by
    by_cases hzero : S₀.available.card = 0
    · simp [hzero]
    · apply inv_le_one_of_one_le₀
      exact_mod_cast (show 1 ≤ S₀.available.card by omega)
  unfold pairUpperLinearRate pairUpperRateBound
  calc
    (delta : ℝ) * ((3 * delta - 2 - Delta : ℕ) : ℝ) *
          (S₀.available.card : ℝ)⁻¹ ≤
        (delta : ℝ) * ((3 * delta - 2 - Delta : ℕ) : ℝ) * 1 := by
      gcongr
    _ = ((delta * (3 * delta - 2 - Delta) : ℕ) : ℝ) := by
      push_cast
      ring

lemma paddedPairTheta_pos (delta Delta Kpair : ℕ) :
    0 < paddedPairTheta delta Delta Kpair := by
  unfold paddedPairTheta
  positivity

lemma paddedPairTheta_mul_upper_le_one (delta Delta Kpair : ℕ) :
    paddedPairTheta delta Delta Kpair *
        (pairUpperRateBound delta Delta : ℕ) ≤ 1 := by
  unfold paddedPairTheta
  have hpos : (0 : ℝ) <
      (pairUpperRateBound delta Delta + (3 + Kpair) + 1 : ℕ) := by
    exact_mod_cast (show 0 <
      pairUpperRateBound delta Delta + (3 + Kpair) + 1 by omega)
  rw [inv_mul_le_one₀ hpos]
  exact_mod_cast (show pairUpperRateBound delta Delta ≤
    pairUpperRateBound delta Delta + (3 + Kpair) + 1 by omega)

lemma paddedPairTheta_mul_lower_le_one (delta Delta Kpair : ℕ) :
    paddedPairTheta delta Delta Kpair * ((3 + Kpair : ℕ) : ℝ) ≤ 1 := by
  unfold paddedPairTheta
  have hpos : (0 : ℝ) <
      (pairUpperRateBound delta Delta + (3 + Kpair) + 1 : ℕ) := by
    exact_mod_cast (show 0 <
      pairUpperRateBound delta Delta + (3 + Kpair) + 1 by omega)
  rw [inv_mul_le_one₀ hpos]
  exact_mod_cast (show 3 + Kpair ≤
    pairUpperRateBound delta Delta + (3 + Kpair) + 1 by omega)

lemma paddedPairVariance_nonneg
    (delta Delta Kpair Kglobal Dmin : ℕ) :
    0 ≤ paddedPairVariance delta Delta Kpair Kglobal Dmin := by
  unfold paddedPairVariance
  have hnonneg : 0 ≤
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairUpperRateBound delta Delta : ℕ) := by
    unfold linearPairVarianceBudgetTwoCutoffs
    positivity
  exact hnonneg.trans (le_max_left _ _)

lemma linearPairVarianceBudget_upper_le_padded
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (delta Delta Kpair Kglobal Dmin : ℕ) :
    linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairUpperLinearRate S₀ delta Delta) ≤
      paddedPairVariance delta Delta Kpair Kglobal Dmin := by
  have hrnonneg := pairUpperLinearRate_nonneg S₀ delta Delta
  have hrle := pairUpperLinearRate_le_bound S₀ delta Delta
  have hsquare : (pairUpperLinearRate S₀ delta Delta) ^ 2 ≤
      ((pairUpperRateBound delta Delta : ℕ) : ℝ) ^ 2 := by
    nlinarith
  apply le_trans (b := linearPairVarianceBudgetTwoCutoffs
      Delta Kpair Kglobal Dmin (pairUpperRateBound delta Delta : ℕ))
  · unfold linearPairVarianceBudgetTwoCutoffs
    linarith
  · exact le_max_left _ _

lemma linearPairVarianceBudget_lower_le_padded
    (delta Delta Kpair Kglobal Dmin : ℕ) :
    linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairLowerLinearRate Delta Kglobal Dmin) ≤
      paddedPairVariance delta Delta Kpair Kglobal Dmin := by
  exact le_max_right _ _

/-- The realizable polynomial-size absorber and the scalar phase estimates
produce one genuine two-cutoff packing phase. -/
theorem exists_paddedAbsorber_linearScheduledPhaseTwoCutoffs
    {q m n phaseSteps sPair sGlobal Kpair Kglobal Delta delta
      Dmin D₀ L : ℕ} (a : ℝ)
    (hq : 4 ≤ q) (hm : 3 ≤ m)
    (hmC : m ≤ paddedAbsorberSize q m)
    (hfit : paddedAbsorberSize q m ≤ n)
    (hLpos : 0 < L)
    (hinitialBuffer :
      L + 3 * paddedAbsorberSize q m + 2 ≤ n)
    (hglobalFloor :
      6 * D₀ ≤ (n - paddedAbsorberSize q m) *
        (n - (paddedAbsorberSize q m + 1)) * L)
    (hinitialCapScalar :
      (n : ℝ) + a ≤ ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloorScalar :
      (delta : ℝ) + a +
          (phaseSteps : ℝ) *
            pairLowerLinearRate Delta Kglobal Dmin ≤
        ((n - 2 - 3 * paddedAbsorberSize q m : ℕ) : ℝ))
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hDminPos : 0 < Dmin)
    (hbuffer : phaseSteps * (3 * Delta + Kglobal) + Dmin ≤ D₀)
    (hlowerDeath :
      pairLowerLinearRate Delta Kglobal Dmin ≤ (delta : ℝ))
    (hratio : (phaseSteps : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (n + 1 : ℝ≥0)⁻¹)
    (hsmall : paddedPhaseFailureUpper q
      (paddedAbsorberLocalization q) (paddedAbsorberSize q m)
      (paddedAbsorberBankSize q m) n phaseSteps sPair sGlobal
      Kpair Kglobal (paddedPairTheta delta Delta Kpair) a
      (paddedPairVariance delta Delta Kpair Kglobal Dmin) < 1) :
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
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        linearAvailabilitySchedule D₀ (3 * Delta + Kglobal)
          phaseSteps phaseSteps ≤ S.available.card ∧
        S.chosen.card = phaseSteps := by
  obtain ⟨H, X, B, hXcard, hA1, hA2, hbank, hBsupport,
      hHsupport, hdegree, hBcard⟩ :=
    exists_paddedRealizableAbsorber (q := q) (n := n)
      (m := m) (by omega) (by simpa only [paddedAbsorberSize] using hfit)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  let S₀ := absorberGreedyInitialState
    (absorberErdosForbiddenConfigurationsOn q B)
    (outsideAvailableTriangles H B)
  let theta := paddedPairTheta delta Delta Kpair
  let variance := paddedPairVariance delta Delta Kpair Kglobal Dmin
  have hXthree : 3 ≤ X.card := by omega
  have hXbound : X.card ≤ paddedAbsorberSize q m := by omega
  have hupperJump : pairUpperLinearRate S₀ delta Delta ≤
      (pairUpperRateBound delta Delta : ℝ) :=
    pairUpperLinearRate_le_bound S₀ delta Delta
  have hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
          (pairUpperLinearRate S₀ delta Delta) ≤ variance := by
    exact linearPairVarianceBudget_upper_le_padded
      S₀ delta Delta Kpair Kglobal Dmin
  have hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
          (pairLowerLinearRate Delta Kglobal Dmin) ≤ variance := by
    exact linearPairVarianceBudget_lower_le_padded
      delta Delta Kpair Kglobal Dmin
  have hsmallActual :
      (Fintype.card (PairOn (Fin n)) : ℝ) *
          (2 * Real.exp
            (-theta * a + theta ^ 2 *
              (phaseSteps : ℝ) * variance)) +
        (((Fintype.card (TripleOn (Fin n)) : ℝ≥0) *
          (Fintype.card (PairOn (Fin n)) : ℝ≥0) *
          pairTwoAwayTail q sPair Kpair
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
        (((Fintype.card (TripleOn (Fin n)) : ℝ≥0) *
          envelopeTwoAwayTail q (paddedAbsorberLocalization q) sGlobal
            H X B Kglobal : ℝ≥0) : ℝ) < 1 := by
    apply (paddedPhaseFailure_le theta a variance
      (V := Fin n) (H := H) (X := X) (B := B)
      (c := paddedAbsorberSize q m)
      (b := paddedAbsorberBankSize q m)
      (phaseSteps := phaseSteps) (sPair := sPair) (sGlobal := sGlobal)
      (Kpair := Kpair) (Kglobal := Kglobal)
      (n := n)
      (M := paddedAbsorberLocalization q) (q := q)
      (by simp) hHsupport (by
        simpa only [paddedAbsorberBankSize, paddedAbsorberSize] using
          hBcard)).trans_lt
    simpa only [theta, variance] using hsmall
  obtain ⟨S, hSAbs, houtside, hSpair, hSglobal, hSfloor, hScard⟩ :=
    exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_of_absorberBounds
      theta a variance hq hA1
      (by simpa only [paddedAbsorberLocalization] using hA2)
      hbank hdegree
      (by simpa only [paddedAbsorberSize] using hBsupport)
      hXthree hXbound hLpos
      (by simpa only [paddedAbsorberSize, Fintype.card_fin] using
        hinitialBuffer)
      (by simpa only [paddedAbsorberSize, Fintype.card_fin] using
        hglobalFloor)
      (by simpa using hinitialCapScalar)
      (by simpa only [paddedAbsorberSize, Fintype.card_fin] using
        hfinalFloorScalar)
      hdelta hsmallPair hDminPos hbuffer hupperJump hlowerDeath
      hvarianceUpper hvarianceLower
      (paddedPairTheta_pos delta Delta Kpair)
      (paddedPairTheta_mul_upper_le_one delta Delta Kpair)
      (paddedPairTheta_mul_lower_le_one delta Delta Kpair)
      (paddedPairVariance_nonneg delta Delta Kpair Kglobal Dmin)
      (by simpa using hratio) hsmallActual
  exact ⟨H, X, B, S, hXcard, hA1, hA2, hbank, hSAbs, houtside,
    hSpair, hSglobal, hSfloor, hScard⟩

end

end Erdos207
