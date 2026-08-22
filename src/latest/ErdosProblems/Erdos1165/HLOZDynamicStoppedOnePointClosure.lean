/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.ExternalStoppedWeightedOnePoint
import ErdosProblems.Erdos1165.HLOZDynamicThresholdedScreening

/-!
# Dynamic Proposition 4.8 with the stopped one-point input closed

The stopped clock is used only in the large-local-time predicate.  The
visited set is overcounted by the oriented external range at the deterministic
HLOZ cap.  The checked stopped one-point theorem therefore supplies the
weighted one-site premise directly, with no stopped external-word
disintegration.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZDynamicStoppedOnePointClosure

open ExternalStoppedWeightedOnePoint ExternalWeightedOnePointCanonical
open ExternalThickCount ExternalProposition44
open HLOZDynamicThresholdedScreening HLOZProposition48Candidates
open HLOZThresholdedShellScreening NearFavoriteThresholded
open ScreeningInstantiation LazyDecomposition

noncomputable section

/-- The deterministic-cap range used to dominate a stopped candidate set. -/
noncomputable def stoppedCapVisitedSites (o : Orientation) (m : ℕ) :
    WalkPath → Finset Point :=
  fun s ↦ orientedExternalVisitedSites o s (hlozCutoff44 m)

/-- Proposition 4.8 at an arbitrary bounded stopping clock, after the
weighted one-site estimate and visit-cardinality estimate have both been
discharged.  The remaining `productLaw` is the literal random-total adjacent
shell product law. -/
theorem eventually_simpleRandomWalk_dynamicStoppedCandidateOverflow48_le
    (o : Orientation) {beta : ℝ} (hbeta : kappaOne ≤ beta) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (tau : WalkPath → ℕ) (threshold : ℕ)
        (distinguished : WalkPath → Finset Point)
        (totalLocalTime : WalkPath → Point → ℕ)
        (balanced : ℕ → Set WalkPath),
      hlozOnePointLevel44 m ≤ threshold →
      (∀ s, tau s ≤ hlozCutoff44 m) →
      (∀ x, MeasurableSet (stoppedOrientedLargeEvent o tau threshold x)) →
      ∀ (balanceLaw : ∀ j,
          GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m)
        (productLaw : RandomTotalProductLaw simpleRandomWalk balanced
          (dynamicShellOccupancy (stoppedCapVisitedSites o m)
            (stoppedOrientedLargeEvent o tau threshold) distinguished
            totalLocalTime m (shellWidth48 m))
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shellGrowth48 (shellCount48 m beta)),
      simpleRandomWalk
          (dynamicStoppedCandidateOverflow48 (stoppedCapVisitedSites o m)
            (stoppedOrientedLargeEvent o tau threshold) distinguished
            totalLocalTime m beta) ≤
        ENNReal.ofReal
          (((hlozOnePointRate44 m *
                ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) /
                initialBudget48 m).toReal) +
            ∑ j ∈ Finset.range (shellCount48 m beta - 1),
              ((((balanceLaw j).budget : ℝ≥0∞) *
                  (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                    ENNReal.ofReal
                      (Real.exp (-17 * balanceRateScale m)))).toReal +
                ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
                  productLaw.fixedCost j total)) := by
  filter_upwards
    [eventually_simpleRandomWalk_hloz_stoppedLarge_weightedOneSite44 o,
      eventually_geometricCandidateBudget48_le_candidateBudget48 hbeta] with
      m hone hbudget
  intro tau threshold distinguished totalLocalTime balanced hthreshold htau
    hlarge balanceLaw productLaw
  exact simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_thresholded
    (Site := Point) (stoppedCapVisitedSites o m)
    (stoppedOrientedLargeEvent o tau threshold) distinguished totalLocalTime
    m beta balanced (hlozOnePointRate44 m)
    ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞)
    (hlozOnePointRate44_ne_top m)
    ENNReal.coe_ne_top hbudget
    (fun x ↦ measurableSet_member_orientedExternalVisitedSites
      o (hlozCutoff44 m) x)
    hlarge (hone tau threshold hthreshold htau hlarge)
    (by
      simpa only [stoppedCapVisitedSites] using
        lintegral_orientedExternalVisitedSites_card_le o (hlozCutoff44 m))
    balanceLaw productLaw

end

end Erdos1165.HLOZDynamicStoppedOnePointClosure
