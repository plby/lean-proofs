/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.NearFavoriteThresholded
import ErdosProblems.Erdos1165.ScreeningInstantiation

/-!
# Correct thresholded, random-total HLOZ shell screening

This module replaces the two invalid hypotheses of the first shell adapter:

* balancedness is derived from the checked two-sided geometric
  moderate-deviation theorem, leaving only literal one-site insertion-law
  comparisons;
* adjacent growth is decomposed over the actual adjacent-pair total.  Each
  exact-total term is identified with an explicit product mass and bounded
  there, rather than comparing the whole event with a binomial law having a
  globally fixed sample size.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1165.HLOZThresholdedShellScreening

open Balancedness NearFavoriteShells NearFavoriteThresholded
open ScreeningInstantiation

noncomputable section

/-! ## Balancedness from literal one-site insertion laws -/

/-- Data which reduce one interface's balancedness complement to finitely
many one-site lower/upper deviations under the explicit geometric insertion
law.  These are strictly one-site law comparisons, not a bound on the union
or on the shell transition. -/
structure GeometricBalanceLaw {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (balanced : Set Omega) (m : ℕ) where
  sites : Finset Site
  lowerBad : Site → Set Omega
  upperBad : Site → Set Omega
  budget : ℕ
  successes : Site → ℕ
  identify : balancedᶜ =
    Screening.someCandidateBad sites
      (Balancedness.twoSidedBad lowerBad upperBad)
  m_pos : 0 < m
  card_le : sites.card ≤ budget
  successes_pos : ∀ x ∈ sites, 0 < successes x
  successes_le : ∀ x ∈ sites, successes x ≤ m
  deviation_le : ∀ x ∈ sites,
    geometricDeviation m ≤ successes x
  lower_law : ∀ x ∈ sites,
    mu (lowerBad x) ≤ ENNReal.ofReal
      ((GeometricChernoff.geometric15Vector (successes x)).real
        {g | GeometricChernoff.geometricSum g ≤
          (successes x : ℝ) / 15 - geometricDeviation m})
  upper_law : ∀ x ∈ sites,
    mu (upperBad x) ≤ ENNReal.ofReal
      ((GeometricChernoff.geometric15Vector (successes x)).real
        {g | (successes x : ℝ) / 15 + geometricDeviation m ≤
          GeometricChernoff.geometricSum g})

/-- The checked geometric Chernoff calculation discharges the balancedness
union estimate from the preceding one-site laws. -/
theorem measureReal_compl_le_of_geometricBalanceLaw
    {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (balanced : Set Omega) (m : ℕ)
    (law : GeometricBalanceLaw (Site := Site) mu balanced m) :
    mu.real balancedᶜ ≤
      ((law.budget : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal := by
  rw [law.identify]
  apply ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
  exact measure_someGeometricImbalance_le mu law.sites law.lowerBad
    law.upperBad law.budget m law.successes law.m_pos law.card_le
    law.successes_pos law.successes_le law.deviation_le law.lower_law
    law.upper_law

/-! ## Exact-total stopped product disintegration -/

/-- The valid spatial input at an adjacent interface.  The pair total is
bounded on the finite capped fibre, and each exact-total event is first
identified with a finite product mass and only then estimated. -/
structure RandomTotalProductLaw {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ)
    (G shellCount : ℕ) where
  totalBound : ℕ → ℕ
  productMass : ℕ → ℕ → ℝ
  fixedCost : ℕ → ℕ → ℝ
  pair_bound : ∀ j < shellCount - 1, ∀ omega,
    omega ∈ balanced j ∩
        thresholdedGrowthFailure occupancy threshold G j →
      occupancy omega j + occupancy omega (j + 1) ≤ totalBound j
  disintegrate : ∀ j < shellCount - 1, ∀ total < totalBound j + 1,
    mu.real (fixedTotalThresholdedFailure balanced occupancy threshold
      G j total) = productMass j total
  product_bound : ∀ j < shellCount - 1, ∀ total < totalBound j + 1,
    productMass j total ≤ fixedCost j total

/-- Correct finite shell recurrence: balancedness comes from the literal
one-site geometric laws and growth comes from the literal exact-total product
disintegration. -/
theorem measureReal_totalOverflow_le_of_geometricBalance_and_randomTotalProduct
    {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount m : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) mu (balanced j) m)
    (productLaw : RandomTotalProductLaw mu balanced occupancy threshold
      G shellCount)
    {baseCost : ℝ}
    (hbase : mu.real (shellOverflow occupancy threshold 0) ≤ baseCost) :
    mu.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        ((((balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
          ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
            productLaw.fixedCost j total) := by
  apply measureReal_totalOverflow_le_of_fixedTotalDecomposition
    (baseCost := baseCost)
    (balanceCost := fun j ↦
      (((balanceLaw j).budget : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal)
    (fixedCost := productLaw.fixedCost) mu balanced occupancy threshold G
    shellCount productLaw.totalBound hstep productLaw.pair_bound hbase
  · intro j hj
    exact measureReal_compl_le_of_geometricBalanceLaw mu (balanced j) m
      (balanceLaw j)
  · intro j hj total htotal
    rw [productLaw.disintegrate j hj total htotal]
    exact productLaw.product_bound j hj total htotal

/-! ## Canonical planar-walk specialization -/

/-- Canonical stopped-prefix shell theorem with all deterministic and
arithmetic inputs discharged.  The remaining inputs are only:

* `hweightedOneSite`, the external-chain one-point estimate;
* `balanceLaw.lower_law`/`upper_law`, literal one-site stopped insertion laws;
* `productLaw.disintegrate`, the exact stopped-fibre/product identity;
* `productLaw.product_bound`, a finite product-mass estimate on an exact
  adjacent-pair-total fibre.

In particular there is no `hspatialBalance`, no unthresholded growth event,
and no globally fixed adjacent-pair total. -/
theorem simpleRandomWalk_externalShell_totalOverflow_le_thresholded
    {Site : Type*}
    (o : LazyDecomposition.Orientation)
    (n externalThreshold J G shellCount : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m shellWidth : ℕ)
    (balanced : ℕ → Set WalkPath)
    (q : ℝ≥0∞) (hJ : 0 < J) (hq : q ≠ ∞)
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
        totalLocalTime m shellWidth)
      (geometricShellThreshold J G) G shellCount) :
    simpleRandomWalk.real
        (totalOverflow
          (externalShellOccupancy o n externalThreshold distinguished
            totalLocalTime m shellWidth)
          (geometricShellThreshold J G) shellCount) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / J).toReal +
        ∑ j ∈ Finset.range (shellCount - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
            ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
              productLaw.fixedCost j total) := by
  let occupancy := externalShellOccupancy o n externalThreshold distinguished
    totalLocalTime m shellWidth
  have hstep : ∀ j, j + 1 < shellCount →
      G * geometricShellThreshold J G j ≤
        geometricShellThreshold J G (j + 1) := by
    intro j hj
    exact (geometricShellThreshold_step J G j).le
  have hbase : simpleRandomWalk.real
      (shellOverflow occupancy (geometricShellThreshold J G) 0) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / J).toReal := by
    simpa only [occupancy] using
      simpleRandomWalk_real_externalShellOverflow_zero_le o n externalThreshold
        J G distinguished totalLocalTime m shellWidth q hJ hq hweightedOneSite
  exact measureReal_totalOverflow_le_of_geometricBalance_and_randomTotalProduct
    simpleRandomWalk balanced occupancy (geometricShellThreshold J G)
    G shellCount m hstep balanceLaw productLaw hbase

end

end Erdos1165.HLOZThresholdedShellScreening
