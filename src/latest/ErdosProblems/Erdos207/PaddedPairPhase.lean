/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OutsidePairSurvival
import ErdosProblems.Erdos207.InitialGlobalAvailability

/-!
# Scalar interface for the first padded-absorber pair phase

The exact initial local and global counts eliminate all pair-indexed initial
hypotheses from the scheduled phase theorem.  At this boundary the remaining
conditions are scalar inequalities plus the already constructed absorber
properties.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Structural absorber bounds and scalar phase inequalities imply a full
scheduled phase with outside-pair survival. -/
theorem exists_linearScheduledAbsorberGreedy_phase_of_absorberBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M phaseSteps s K Delta delta JUpper Dmin D₀ C L : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (theta a variance : ℝ)
    (hq : 4 ≤ q)
    (hA1 : HasHighGirthAbsorptionBank q H X B)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (hXthree : 3 ≤ X.card) (hXbound : X.card ≤ C)
    (hLpos : 0 < L)
    (hinitialBuffer : L + 3 * C + 2 ≤ Fintype.card V)
    (hglobalFloor :
      6 * D₀ ≤ (Fintype.card V - C) *
        (Fintype.card V - (C + 1)) * L)
    (hinitialCapScalar :
      (Fintype.card V : ℝ) + a ≤ ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloorScalar :
      (delta : ℝ) + a +
          (phaseSteps : ℝ) * pairLowerLinearRate Delta K Dmin ≤
        ((Fintype.card V - 2 - 3 * C : ℕ) : ℝ))
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + K < delta)
    (hDminPos : 0 < Dmin)
    (hbuffer : phaseSteps * (3 * Delta + K) + Dmin ≤ D₀)
    (hupperJump :
      pairUpperLinearRate
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)) delta Delta ≤
        (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Delta K Dmin ≤ (delta : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudget Delta K Dmin
        (pairUpperLinearRate
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)) delta Delta) ≤ variance)
    (hvarianceLower :
      linearPairVarianceBudget Delta K Dmin
        (pairLowerLinearRate Delta K Dmin) ≤ variance)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + K : ℕ) : ℝ) ≤ 1)
    (hvariance : 0 ≤ variance)
    (hratio : (phaseSteps : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp
            (-theta * a + theta ^ 2 *
              (phaseSteps : ℝ) * variance)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M s H X B K : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B) S ∧
        OutsideLeavePairsAlive H X S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) K S ∧
        linearAvailabilitySchedule D₀ (3 * Delta + K)
            phaseSteps phaseSteps ≤ S.available.card ∧
        S.chosen.card = phaseSteps := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A := outsideAvailableTriangles H B
  let S₀ := absorberGreedyInitialState F A
  have hglobal := initial_globalAvailability_lower
    (q := q) (L := L) hbank hdegree hsupport hXbound hinitialBuffer
  have hfloor₀ : D₀ ≤ S₀.available.card := by
    dsimp only [S₀, F, A]
    omega
  have hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Delta + 1 : ℕ) : ℝ) := by
    intro P
    have hcut := initial_hasAvailablePairCutoff_card F A P.1 P.2
    have hcount :
        fixedPairAvailableCountReal S₀ P.1 S₀ =
          (availableTrianglesContainingPair S₀ P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    have hcutReal :
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) ≤
          (Fintype.card V : ℝ) := by
      exact_mod_cast hcut
    linarith
  have hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (delta : ℝ) + a +
          (phaseSteps : ℝ) * pairLowerLinearRate Delta K Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀ := by
    intro P hPalive
    have hlocal := initialPairStar_lower_of_alive hq hA1 hXthree
      hbank hdegree hsupport P hPalive
    have hnat : Fintype.card V - 2 - 3 * C ≤
        (availableTrianglesContainingPair S₀ P.1).card := by
      dsimp only [S₀, F, A] at hlocal ⊢
      omega
    have hreal : ((Fintype.card V - 2 - 3 * C : ℕ) : ℝ) ≤
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) := by
      exact_mod_cast hnat
    have hcount :
        fixedPairAvailableCountReal S₀ P.1 S₀ =
          (availableTrianglesContainingPair S₀ P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    linarith
  have hlarge : 3 * C + 3 ≤ Fintype.card V := by omega
  exact exists_linearScheduledAbsorberGreedy_phase_with_outsidePairSurvival
    S₀ rfl rfl theta a variance hA2 hbank hdegree hsupport hlarge
    hdelta hsmallPair hDminPos hbuffer hfloor₀ hinitialCap hfinalFloor
    hupperJump hlowerDeath hvarianceUpper hvarianceLower htheta
    hthetaUpper hthetaLower hvariance hratio hsmall

/-! ## Scalar interface with separate pair-local and global cutoffs -/

/-- Structural absorber bounds and scalar inequalities imply a full
scheduled phase with a small pair-local cutoff and a separate global cutoff.
The local cutoff controls survival of leave pairs, while the global cutoff
controls total availability loss. -/
theorem exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_of_absorberBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M phaseSteps sPair sGlobal Kpair Kglobal Delta delta JUpper
      Dmin D₀ C L : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (theta a variance : ℝ)
    (hq : 4 ≤ q)
    (hA1 : HasHighGirthAbsorptionBank q H X B)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (hXthree : 3 ≤ X.card) (hXbound : X.card ≤ C)
    (hLpos : 0 < L)
    (hinitialBuffer : L + 3 * C + 2 ≤ Fintype.card V)
    (hglobalFloor :
      6 * D₀ ≤ (Fintype.card V - C) *
        (Fintype.card V - (C + 1)) * L)
    (hinitialCapScalar :
      (Fintype.card V : ℝ) + a ≤ ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloorScalar :
      (delta : ℝ) + a +
          (phaseSteps : ℝ) *
            pairLowerLinearRate Delta Kglobal Dmin ≤
        ((Fintype.card V - 2 - 3 * C : ℕ) : ℝ))
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hDminPos : 0 < Dmin)
    (hbuffer : phaseSteps * (3 * Delta + Kglobal) + Dmin ≤ D₀)
    (hupperJump :
      pairUpperLinearRate
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)) delta Delta ≤
        (JUpper : ℝ))
    (hlowerDeath :
      pairLowerLinearRate Delta Kglobal Dmin ≤ (delta : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairUpperLinearRate
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)) delta Delta) ≤ variance)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairLowerLinearRate Delta Kglobal Dmin) ≤ variance)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hvariance : 0 ≤ variance)
    (hratio : (phaseSteps : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp
            (-theta * a + theta ^ 2 *
              (phaseSteps : ℝ) * variance)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q sPair Kpair
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
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
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A := outsideAvailableTriangles H B
  let S₀ := absorberGreedyInitialState F A
  have hglobal := initial_globalAvailability_lower
    (q := q) (L := L) hbank hdegree hsupport hXbound hinitialBuffer
  have hfloor₀ : D₀ ≤ S₀.available.card := by
    dsimp only [S₀, F, A]
    omega
  have hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Delta + 1 : ℕ) : ℝ) := by
    intro P
    have hcut := initial_hasAvailablePairCutoff_card F A P.1 P.2
    have hcount :
        fixedPairAvailableCountReal S₀ P.1 S₀ =
          (availableTrianglesContainingPair S₀ P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    have hcutReal :
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) ≤
          (Fintype.card V : ℝ) := by
      exact_mod_cast hcut
    linarith
  have hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (delta : ℝ) + a +
          (phaseSteps : ℝ) *
            pairLowerLinearRate Delta Kglobal Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀ := by
    intro P hPalive
    have hlocal := initialPairStar_lower_of_alive hq hA1 hXthree
      hbank hdegree hsupport P hPalive
    have hnat : Fintype.card V - 2 - 3 * C ≤
        (availableTrianglesContainingPair S₀ P.1).card := by
      dsimp only [S₀, F, A] at hlocal ⊢
      omega
    have hreal : ((Fintype.card V - 2 - 3 * C : ℕ) : ℝ) ≤
        ((availableTrianglesContainingPair S₀ P.1).card : ℝ) := by
      exact_mod_cast hnat
    have hcount :
        fixedPairAvailableCountReal S₀ P.1 S₀ =
          (availableTrianglesContainingPair S₀ P.1).card :=
      fixedPairAvailableCountReal_eq_current Subset.rfl
    rw [hcount]
    linarith
  have hlarge : 3 * C + 3 ≤ Fintype.card V := by omega
  exact
    exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_with_outsidePairSurvival
      S₀ rfl rfl theta a variance hA2 hbank hdegree hsupport hlarge
      hdelta hsmallPair hDminPos hbuffer hfloor₀ hinitialCap hfinalFloor
      hupperJump hlowerDeath hvarianceUpper hvarianceLower htheta
      hthetaUpper hthetaLower hvariance hratio hsmall

end

end Erdos207
