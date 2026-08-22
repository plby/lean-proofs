/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZProposition48Candidates

/-!
# Proposition 4.8 on the literal stopped finite product fibre

This is the finite-product companion to
`HLOZProposition48Candidates.simpleRandomWalk_real_stoppedCandidateOverflow48_le`.
It specializes the exact product-law adapter from
`HLOZStoppedSpatialScreening` to the checked Proposition 4.8 strip count,
width, initial budget, and growth factor.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.HLOZProposition48Product

open LazyDecomposition PathInsertion SpatialInsertionFiber
open PrefixConditionalLaw PreStoppingConditionalLaw
open NearFavoriteShells ScreeningInstantiation
open HLOZProposition48Candidates HLOZStoppedSpatialScreening

noncomputable section

/-- A Boolean event in the exact stopped product law has the Proposition 4.8
shell bound once it is identified with the concrete total-overflow predicate.
All local-CLT arithmetic is internal; the remaining quantitative assumptions
are the external one-point and stopped spatial balance/growth estimates. -/
theorem upperProductShellOverflowMass48_le
    {fiberOrientation : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock fiberOrientation) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (productEvent : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred productEvent]
    (shellOrientation : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m : ℕ) (beta : ℝ)
    (balanced : ℕ → Set WalkPath) (pairTotal successes : ℕ → ℕ)
    (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hsuccess : ∀ j < shellCount48 m beta - 1, 120 ≤ successes j)
    (hidentify : upperProductScreenMass x r D upper productEvent =
      simpleRandomWalk.real
        (totalOverflow
          (externalShellOccupancy shellOrientation n externalThreshold
            distinguished totalLocalTime m (shellWidth48 m))
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          (shellCount48 m beta)))
    (hweightedOneSite : ∀ y,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites
              shellOrientation s n)
            (ExternalThickCount.orientedLargeEvent shellOrientation n
              externalThreshold) y) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites
              shellOrientation s n) y))
    {balanceCost : ℕ → ℝ}
    (hspatialBalance : ∀ j < shellCount48 m beta - 1,
      simpleRandomWalk.real (balanced j)ᶜ ≤ balanceCost j)
    (hspatialGrowth : ∀ (j : ℕ) (hj : j < shellCount48 m beta - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure balanced
            (externalShellOccupancy shellOrientation n externalThreshold
              distinguished totalLocalTime m (shellWidth48 m))
            shellGrowth48 j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (SmallWindow.windowMass (successes j)
              (upperFailureWindow (successes j)
                (canonicalWindowWidth (successes j))))
            (SmallWindow.windowMass (successes j)
              (lowerFailureWindow (successes j)
                (canonicalWindowWidth (successes j))))
            (SmallWindow.windowMass_nonneg _ _)
            (SmallWindow.windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (SmallWindow.windowMass_nonneg _ _)
              (SmallWindow.windowMass_pos
                (canonicalWindowWidth_numeric (hsuccess j hj)).1
                (lowerFailureWindow_nonempty
                  (canonicalWindowWidth_numeric (hsuccess j hj)).2.1)))).real
          {a | a ≤ pairTotal j ∧
            shellGrowth48 * (pairTotal j - a) < a}) :
    upperProductScreenMass x r D upper productEvent ≤
      (q * (↑(n + 1) : ℝ≥0∞) / initialBudget48 m).toReal +
        ∑ j ∈ Finset.range (shellCount48 m beta - 1),
          (balanceCost j +
            (1 + adjacentLocalRatio (successes j)
                  (adjacentWindowRadius (canonicalWindowWidth (successes j)))
                  (adjacentWindowSeparation
                    (canonicalWindowWidth (successes j))) /
                (1 + adjacentLocalRatio (successes j)
                  (adjacentWindowRadius (canonicalWindowWidth (successes j)))
                  (adjacentWindowSeparation
                    (canonicalWindowWidth (successes j))))) ^ pairTotal j /
              (2 : ℝ) ^ growthCut shellGrowth48 (pairTotal j)) := by
  exact upperProductScreenMass_le_of_externalShellScreen x r D upper
    productEvent shellOrientation n externalThreshold (initialBudget48 m)
    shellGrowth48 (shellCount48 m beta) distinguished totalLocalTime m
    (shellWidth48 m) balanced pairTotal successes q
    (by unfold initialBudget48; omega) hq hsuccess hidentify
    hweightedOneSite hspatialBalance hspatialGrowth

end

end Erdos1165.HLOZProposition48Product
