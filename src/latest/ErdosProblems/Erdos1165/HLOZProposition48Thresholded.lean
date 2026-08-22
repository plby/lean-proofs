/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZProposition48Candidates
import ErdosProblems.Erdos1165.HLOZThresholdedShellScreening

/-!
# Correct path-level Proposition 4.8 overflow estimate

This specializes the thresholded random-total shell recurrence to the exact
Proposition 4.8 strip width, strip count, initial budget, and growth factor.
It yields the path-level per-band estimate consumed by the gap argument.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZProposition48Thresholded

open LazyDecomposition NearFavoriteShells NearFavoriteThresholded
open ScreeningInstantiation HLOZProposition48Candidates
open HLOZThresholdedShellScreening

noncomputable section

/-- The corrected Proposition 4.8 bound on one deficit band.  It has no
fixed-total or unthresholded-growth assumption. -/
theorem simpleRandomWalk_real_stoppedCandidateOverflow48_le_thresholded
    {Site : Type*}
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (balanced : ℕ → Set WalkPath)
    (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x))
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) simpleRandomWalk (balanced j) m)
    (productLaw : RandomTotalProductLaw simpleRandomWalk balanced
      (externalShellOccupancy o n externalThreshold distinguished
        totalLocalTime m (shellWidth48 m))
      (geometricShellThreshold (initialBudget48 m) shellGrowth48)
      shellGrowth48 (shellCount48 m beta)) :
    simpleRandomWalk.real
        (stoppedCandidateOverflow48 o n externalThreshold distinguished
          totalLocalTime m beta) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / initialBudget48 m).toReal +
        ∑ j ∈ Finset.range (shellCount48 m beta - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
            ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
              productLaw.fixedCost j total) := by
  refine (measureReal_mono
    (stoppedCandidateOverflow48_subset_totalOverflow o n externalThreshold
      distinguished totalLocalTime m beta hbudget)).trans ?_
  exact simpleRandomWalk_externalShell_totalOverflow_le_thresholded o n
    externalThreshold (initialBudget48 m) shellGrowth48
    (shellCount48 m beta) distinguished totalLocalTime m (shellWidth48 m)
    balanced q (by unfold initialBudget48; omega) hq hweightedOneSite
    balanceLaw productLaw

/-- ENNReal form used directly as a per-band `hprop48` input by the checked
gap union bound. -/
theorem simpleRandomWalk_stoppedCandidateOverflow48_le_thresholded
    {Site : Type*}
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (balanced : ℕ → Set WalkPath)
    (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x))
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) simpleRandomWalk (balanced j) m)
    (productLaw : RandomTotalProductLaw simpleRandomWalk balanced
      (externalShellOccupancy o n externalThreshold distinguished
        totalLocalTime m (shellWidth48 m))
      (geometricShellThreshold (initialBudget48 m) shellGrowth48)
      shellGrowth48 (shellCount48 m beta)) :
    simpleRandomWalk
        (stoppedCandidateOverflow48 o n externalThreshold distinguished
          totalLocalTime m beta) ≤
      ENNReal.ofReal
        ((q * (↑(n + 1) : ℝ≥0∞) / initialBudget48 m).toReal +
          ∑ j ∈ Finset.range (shellCount48 m beta - 1),
            ((((balanceLaw j).budget : ℝ≥0∞) *
                (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                  ENNReal.ofReal
                    (Real.exp (-17 * balanceRateScale m)))).toReal +
              ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
                productLaw.fixedCost j total)) := by
  apply simpleRandomWalk_stoppedCandidateOverflow48_le_of_real
  exact simpleRandomWalk_real_stoppedCandidateOverflow48_le_thresholded o n
    externalThreshold distinguished totalLocalTime m beta balanced q hq
    hbudget hweightedOneSite balanceLaw productLaw

/-- Eventual version with the deterministic HLOZ candidate-budget
comparison discharged. -/
theorem eventually_simpleRandomWalk_stoppedCandidateOverflow48_le_thresholded
    {Site : Type*}
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : ℕ → WalkPath → Finset Point)
    (totalLocalTime : ℕ → WalkPath → Point → ℕ)
    (beta : ℝ) (hbeta : kappaOne ≤ beta)
    (balanced : ℕ → ℕ → Set WalkPath)
    (q : ℕ → ℝ≥0∞) (hq : ∀ m, q m ≠ ∞)
    (hweightedOneSite : ∀ m x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q m * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x))
    (balanceLaw : ∀ m j,
      GeometricBalanceLaw (Site := Site) simpleRandomWalk (balanced m j) m)
    (productLaw : ∀ m,
      RandomTotalProductLaw simpleRandomWalk (balanced m)
        (externalShellOccupancy o n externalThreshold (distinguished m)
          (totalLocalTime m) m (shellWidth48 m))
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        shellGrowth48 (shellCount48 m beta)) :
    ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalk
          (stoppedCandidateOverflow48 o n externalThreshold (distinguished m)
            (totalLocalTime m) m beta) ≤
        ENNReal.ofReal
          ((q m * (↑(n + 1) : ℝ≥0∞) / initialBudget48 m).toReal +
            ∑ j ∈ Finset.range (shellCount48 m beta - 1),
              ((((balanceLaw m j).budget : ℝ≥0∞) *
                  (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                    ENNReal.ofReal
                      (Real.exp (-17 * balanceRateScale m)))).toReal +
                ∑ total ∈ Finset.range ((productLaw m).totalBound j + 1),
                  (productLaw m).fixedCost j total)) := by
  filter_upwards
      [eventually_geometricCandidateBudget48_le_candidateBudget48 hbeta]
      with m hbudget
  exact simpleRandomWalk_stoppedCandidateOverflow48_le_thresholded o n
    externalThreshold (distinguished m) (totalLocalTime m) m beta
    (balanced m) (q m) (hq m) hbudget (hweightedOneSite m)
    (balanceLaw m) (productLaw m)

end

end Erdos1165.HLOZProposition48Thresholded
