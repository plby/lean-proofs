/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HeterogeneousProductTail
import ErdosProblems.Erdos1165.HLOZDynamicWeightedOnePoint

/-!
# Dynamic Proposition 4.8 with both analytic screens instantiated

This module combines the stopped retained-block weighted one-point theorem
with the heterogeneous exact-total product tail. The only remaining
probabilistic equalities are literal stopped disintegrations.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZDynamicProductClosure

open HeterogeneousProductTail HLOZDynamicThresholdedScreening
open HLOZDynamicWeightedOnePoint HLOZProposition48Candidates
open HLOZThresholdedShellScreening NearFavoriteThresholded
open ScreeningInstantiation

noncomputable section

/-- Dynamic-cutoff Proposition 4.8 after discharging both
`hweightedOneSite` and `RandomTotalProductLaw.product_bound` by their checked
finite laws. -/
theorem simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_closed
    {TraceIndex : Type*} [Countable TraceIndex]
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (balanced : ℕ → Set WalkPath)
    (q R : ℝ≥0∞) (hq : q ≠ ∞) (hR : R ≠ ∞)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta)
    (hvisited : ∀ x,
      MeasurableSet (ExternalThickCount.memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hvisitExpectation :
      ∫⁻ s, ((visited s).card : ℝ≥0∞) ∂simpleRandomWalk ≤ R)
    (weightedData : StoppedExternalBlocksDisintegration
      (Index := TraceIndex) visited large q)
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m)
    (totalBound : ℕ → ℕ)
    (Coordinate : ℕ → Type*) [∀ j, Fintype (Coordinate j)]
    [∀ j, DecidableEq (Coordinate j)]
    (State : ∀ j, Coordinate j → Type*)
    [∀ j c, Fintype (State j c)]
    (weight : ∀ j c, State j c → ℝ)
    (upper lower : ∀ j c, State j c → Prop)
    [∀ j c, DecidablePred (upper j c)]
    [∀ j c, DecidablePred (lower j c)]
    (C : ℕ → ℝ)
    (hpairBound : ∀ j < shellCount48 m beta - 1, ∀ s,
      s ∈ balanced j ∩
          thresholdedGrowthFailure
            (dynamicShellOccupancy visited large distinguished
              totalLocalTime m (shellWidth48 m))
            (geometricShellThreshold (initialBudget48 m) shellGrowth48)
            shellGrowth48 j →
        dynamicShellOccupancy visited large distinguished totalLocalTime
            m (shellWidth48 m) s j +
          dynamicShellOccupancy visited large distinguished totalLocalTime
            m (shellWidth48 m) s (j + 1) ≤ totalBound j)
    (hdisintegrate :
      ∀ j < shellCount48 m beta - 1, ∀ total < totalBound j + 1,
        simpleRandomWalk.real
            (fixedTotalThresholdedFailure balanced
              (dynamicShellOccupancy visited large distinguished
                totalLocalTime m (shellWidth48 m))
              (geometricShellThreshold (initialBudget48 m) shellGrowth48)
              shellGrowth48 j total) =
          ∑ ell : ∀ c, State j c,
            if fixedTotalUpperTail (upper j) (lower j) total
                (thresholdedGrowthCut
                  (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                  shellGrowth48 j total) ell then
              productPointMass (weight j) ell else 0)
    (hweight : ∀ j c v, 0 ≤ weight j c v)
    (hdisjoint : ∀ j c v, ¬ (upper j c v ∧ lower j c v))
    (hC : ∀ j, 0 ≤ C j)
    (hratio : ∀ j c,
      (∑ v, if upper j c v then weight j c v else 0) ≤
        C j * ∑ v, if lower j c v then weight j c v else 0) :
    simpleRandomWalk
        (dynamicStoppedCandidateOverflow48 visited large distinguished
          totalLocalTime m beta) ≤
      ENNReal.ofReal
        ((q * R / initialBudget48 m).toReal +
          ∑ j ∈ Finset.range (shellCount48 m beta - 1),
            ((((balanceLaw j).budget : ℝ≥0∞) *
                (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                  ENNReal.ofReal
                    (Real.exp (-17 * balanceRateScale m)))).toReal +
              ∑ total ∈ Finset.range (totalBound j + 1),
                exactPairTotalMass (weight j) (upper j) (lower j) total *
                    (1 + C j / (1 + C j)) ^ total /
                  (2 : ℝ) ^ thresholdedGrowthCut
                    (geometricShellThreshold
                      (initialBudget48 m) shellGrowth48)
                    shellGrowth48 j total)) := by
  let occupancy := dynamicShellOccupancy visited large distinguished
    totalLocalTime m (shellWidth48 m)
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  let productLaw : RandomTotalProductLaw simpleRandomWalk balanced occupancy
      threshold shellGrowth48 (shellCount48 m beta) :=
    randomTotalProductLawOfHeterogeneousProduct simpleRandomWalk balanced
      occupancy threshold shellGrowth48 (shellCount48 m beta) totalBound
      Coordinate State weight upper lower C hpairBound hdisintegrate hweight
      hdisjoint hC hratio
  simpa only [occupancy, threshold, productLaw,
    randomTotalProductLawOfHeterogeneousProduct] using
    simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_thresholded
      (Site := Point) visited large distinguished totalLocalTime m beta
      balanced q R hq hR hbudget hvisited hlarge
      (weighted_oneSite_of_stoppedExternalBlocksDisintegration
        visited large q weightedData)
      hvisitExpectation balanceLaw productLaw

/-- A no-cardinality-loss form of the dynamic bound.  Normalized coordinate
masses and a uniform envelope for each adjacent-band fixed-total cost replace
the entire random-total sum by that envelope, rather than by
`(totalBound j + 1)` times the envelope. -/
theorem simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_envelope
    {TraceIndex : Type*} [Countable TraceIndex]
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (balanced : ℕ → Set WalkPath)
    (q R : ℝ≥0∞) (hq : q ≠ ∞) (hR : R ≠ ∞)
    (hbudget : geometricCandidateBudget48 m beta ≤ candidateBudget48 m beta)
    (hvisited : ∀ x,
      MeasurableSet (ExternalThickCount.memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hvisitExpectation :
      ∫⁻ s, ((visited s).card : ℝ≥0∞) ∂simpleRandomWalk ≤ R)
    (weightedData : StoppedExternalBlocksDisintegration
      (Index := TraceIndex) visited large q)
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m)
    (totalBound : ℕ → ℕ)
    (Coordinate : ℕ → Type*) [∀ j, Fintype (Coordinate j)]
    [∀ j, DecidableEq (Coordinate j)]
    (State : ∀ j, Coordinate j → Type*) [∀ j c, Fintype (State j c)]
    (weight : ∀ j c, State j c → ℝ)
    (upper lower : ∀ j c, State j c → Prop)
    [∀ j c, DecidablePred (upper j c)]
    [∀ j c, DecidablePred (lower j c)]
    (C envelope : ℕ → ℝ)
    (hpairBound : ∀ j < shellCount48 m beta - 1, ∀ s,
      s ∈ balanced j ∩
          thresholdedGrowthFailure
            (dynamicShellOccupancy visited large distinguished
              totalLocalTime m (shellWidth48 m))
            (geometricShellThreshold (initialBudget48 m) shellGrowth48)
            shellGrowth48 j →
        dynamicShellOccupancy visited large distinguished totalLocalTime
            m (shellWidth48 m) s j +
          dynamicShellOccupancy visited large distinguished totalLocalTime
            m (shellWidth48 m) s (j + 1) ≤ totalBound j)
    (hdisintegrate :
      ∀ j < shellCount48 m beta - 1, ∀ total < totalBound j + 1,
        simpleRandomWalk.real
            (fixedTotalThresholdedFailure balanced
              (dynamicShellOccupancy visited large distinguished
                totalLocalTime m (shellWidth48 m))
              (geometricShellThreshold (initialBudget48 m) shellGrowth48)
              shellGrowth48 j total) =
          ∑ ell : ∀ c, State j c,
            if fixedTotalUpperTail (upper j) (lower j) total
                (thresholdedGrowthCut
                  (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                  shellGrowth48 j total) ell then
              productPointMass (weight j) ell else 0)
    (hweight : ∀ j c v, 0 ≤ weight j c v)
    (hnorm : ∀ j c, (∑ v, weight j c v) ≤ 1)
    (hdisjoint : ∀ j c v, ¬ (upper j c v ∧ lower j c v))
    (hC : ∀ j, 0 ≤ C j)
    (hratio : ∀ j c,
      (∑ v, if upper j c v then weight j c v else 0) ≤
        C j * ∑ v, if lower j c v then weight j c v else 0)
    (henvelope_nonneg : ∀ j, 0 ≤ envelope j)
    (henvelope : ∀ j < shellCount48 m beta - 1,
      ∀ total < totalBound j + 1,
        (1 + C j / (1 + C j)) ^ total /
            (2 : ℝ) ^ thresholdedGrowthCut
              (geometricShellThreshold (initialBudget48 m) shellGrowth48)
              shellGrowth48 j total ≤ envelope j) :
    simpleRandomWalk
        (dynamicStoppedCandidateOverflow48 visited large distinguished
          totalLocalTime m beta) ≤
      ENNReal.ofReal
        ((q * R / initialBudget48 m).toReal +
          ∑ j ∈ Finset.range (shellCount48 m beta - 1),
            ((((balanceLaw j).budget : ℝ≥0∞) *
                (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                  ENNReal.ofReal
                    (Real.exp (-17 * balanceRateScale m)))).toReal +
              envelope j)) := by
  refine (simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_closed
    visited large distinguished totalLocalTime m beta balanced q R hq hR
    hbudget hvisited hlarge hvisitExpectation weightedData balanceLaw
    totalBound Coordinate State weight upper lower C hpairBound hdisintegrate
    hweight hdisjoint hC hratio).trans ?_
  apply ENNReal.ofReal_mono
  have hsum :
      (∑ j ∈ Finset.range (shellCount48 m beta - 1),
        ((((balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          ∑ total ∈ Finset.range (totalBound j + 1),
            exactPairTotalMass (weight j) (upper j) (lower j) total *
              (1 + C j / (1 + C j)) ^ total /
                (2 : ℝ) ^ thresholdedGrowthCut
                  (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                  shellGrowth48 j total)) ≤
        ∑ j ∈ Finset.range (shellCount48 m beta - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            envelope j) := by
    apply Finset.sum_le_sum
    intro j hj
    have htotals := sum_exactPairTotalMass_mul_cost_le
      (weight j) (upper j) (lower j) (hweight j) (hnorm j) (totalBound j)
      (fun total ↦
        (1 + C j / (1 + C j)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut
            (geometricShellThreshold (initialBudget48 m) shellGrowth48)
            shellGrowth48 j total)
      (henvelope_nonneg j) (henvelope j (Finset.mem_range.mp hj))
    let balanceCost := ((((balanceLaw j).budget : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal)
    calc
      balanceCost +
          ∑ total ∈ Finset.range (totalBound j + 1),
            exactPairTotalMass (weight j) (upper j) (lower j) total *
              (1 + C j / (1 + C j)) ^ total /
                (2 : ℝ) ^ thresholdedGrowthCut
                  (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                  shellGrowth48 j total =
          (∑ total ∈ Finset.range (totalBound j + 1),
            exactPairTotalMass (weight j) (upper j) (lower j) total *
              ((1 + C j / (1 + C j)) ^ total /
                (2 : ℝ) ^ thresholdedGrowthCut
                  (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                  shellGrowth48 j total)) + balanceCost := by
            rw [add_comm]
            congr 1
            apply Finset.sum_congr rfl
            intro total _
            simp only [div_eq_mul_inv, mul_assoc]
      _ ≤ envelope j + balanceCost := add_le_add_left htotals balanceCost
      _ = balanceCost + envelope j := add_comm _ _
  let baseCost := (q * R / initialBudget48 m).toReal
  calc
    baseCost +
        ∑ j ∈ Finset.range (shellCount48 m beta - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            ∑ total ∈ Finset.range (totalBound j + 1),
              exactPairTotalMass (weight j) (upper j) (lower j) total *
                (1 + C j / (1 + C j)) ^ total /
                  (2 : ℝ) ^ thresholdedGrowthCut
                    (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                    shellGrowth48 j total) =
        (∑ j ∈ Finset.range (shellCount48 m beta - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            ∑ total ∈ Finset.range (totalBound j + 1),
              exactPairTotalMass (weight j) (upper j) (lower j) total *
                (1 + C j / (1 + C j)) ^ total /
                  (2 : ℝ) ^ thresholdedGrowthCut
                    (geometricShellThreshold (initialBudget48 m) shellGrowth48)
                    shellGrowth48 j total)) + baseCost := add_comm _ _
    _ ≤ (∑ j ∈ Finset.range (shellCount48 m beta - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            envelope j)) + baseCost := add_le_add_left hsum baseCost
    _ = baseCost +
        ∑ j ∈ Finset.range (shellCount48 m beta - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            envelope j) := add_comm _ _

end

end Erdos1165.HLOZDynamicProductClosure
