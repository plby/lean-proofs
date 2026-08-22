/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZLowScaleCandidateOverflow
import ErdosProblems.Erdos1165.HeterogeneousProductTail
import ErdosProblems.Erdos1165.TilingStoppedProductDisintegration

/-!
# Literal product-law input for the low-scale HLOZ bands

This is the adapter between the all-six stopped-coordinate calculation and
the random-total law consumed by the low-scale candidate screen.  Its only
path-space equality is `fixedTotal_disintegrate`: the exact mass of one
fixed-total thresholded event is the displayed finite product sum.  The
quantitative upper bound is then proved by `HeterogeneousProductTail`.

For the state-dependent tilings, `Coordinate j` is instantiated by the
finite away-domino coordinates furnished by
`TilingStoppedProductDisintegration`; the local equality is obtained from
`tilingStoppedAcceptedGeometricMass_eq_screenMass_mul_of_marginals`.  Thus
this interface neither fixes a physical creation time nor assumes the
candidate-overflow inequality it is used to prove.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZLowScaleProductInstantiation

open HeterogeneousProductTail HLOZLowScaleCandidateOverflow
open HLOZDynamicStoppedOnePointClosure HLOZDynamicThresholdedScreening
open HLOZLazyOverflow HLOZGapRandomClockScreen
open ExternalStoppedWeightedOnePoint
open HLOZProposition48Candidates HLOZThresholdedShellScreening
open NearFavoriteThresholded ScreeningInstantiation
open LazyDecomposition

noncomputable section

/-- The concrete dynamic shell occupancy for one deterministic-cap
random-clock band. -/
noncomputable def bandOccupancy (m cutoff : ℕ) (band : RandomClockBand) :
    WalkPath → ℕ → ℕ :=
  dynamicShellOccupancy (stoppedCapVisitedSites band.orientation m)
    (stoppedOrientedLargeEvent band.orientation
      (pathTruncatedLevelTime m band.oldRank cutoff)
      band.externalThreshold)
    (randomClockDistinguishedSites m cutoff band)
    (randomClockTotalLocalTime m cutoff band)
    m (shellWidth48 m)

/-- Explicit heterogeneous finite-product data for one band.  In the
all-six tiling application, the coordinate and state types are the finite
away-domino totals in a stopped retained-trace fibre. -/
structure HeterogeneousBandProductData
    (m cutoff : ℕ) (band : RandomClockBand) where
  balanced : ℕ → Set WalkPath
  balanceLaw : ∀ j,
    GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m
  totalBound : ℕ → ℕ
  Coordinate : ℕ → Type
  coordinateFintype : ∀ j, Fintype (Coordinate j)
  coordinateDecidableEq : ∀ j, DecidableEq (Coordinate j)
  State : ∀ j, Coordinate j → Type
  stateFintype : ∀ j c, Fintype (State j c)
  weight : ∀ j c, State j c → ℝ
  upper : ∀ j c, State j c → Prop
  lower : ∀ j c, State j c → Prop
  upperDecidable : ∀ j c, DecidablePred (upper j c)
  lowerDecidable : ∀ j c, DecidablePred (lower j c)
  ratioConstant : ℕ → ℝ
  pair_bound : ∀ j < shellCount48 m band.beta - 1, ∀ s,
    s ∈ balanced j ∩
        thresholdedGrowthFailure (bandOccupancy m cutoff band)
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shellGrowth48 j →
      bandOccupancy m cutoff band s j +
        bandOccupancy m cutoff band s (j + 1) ≤ totalBound j
  fixedTotal_disintegrate :
    ∀ j < shellCount48 m band.beta - 1,
      ∀ total < totalBound j + 1,
        simpleRandomWalk.real
            (fixedTotalThresholdedFailure balanced
              (bandOccupancy m cutoff band)
              (geometricShellThreshold (initialBudget48 m) shellGrowth48)
              shellGrowth48 j total) =
          ∑ ell : ∀ c, State j c,
            if fixedTotalUpperTail (upper j) (lower j) total
                (thresholdedGrowthCut
                  (geometricShellThreshold
                    (initialBudget48 m) shellGrowth48)
                  shellGrowth48 j total) ell then
              productPointMass (weight j) ell else 0
  weight_nonneg : ∀ j c v, 0 ≤ weight j c v
  upper_lower_disjoint : ∀ j c v, ¬ (upper j c v ∧ lower j c v)
  ratioConstant_nonneg : ∀ j, 0 ≤ ratioConstant j
  window_ratio : ∀ j c,
    (∑ v, if upper j c v then weight j c v else 0) ≤
      ratioConstant j *
        ∑ v, if lower j c v then weight j c v else 0

/-- The checked heterogeneous product-tail theorem turns the preceding
literal data into the precise band screen used by Proposition 4.8. -/
def bandProductScreenOfHeterogeneousData
    {m cutoff : ℕ} {band : RandomClockBand}
    (data : HeterogeneousBandProductData m cutoff band) :
    BandProductScreen m cutoff band := by
  letI (j : ℕ) : Fintype (data.Coordinate j) := data.coordinateFintype j
  letI (j : ℕ) : DecidableEq (data.Coordinate j) :=
    data.coordinateDecidableEq j
  letI (j : ℕ) (c : data.Coordinate j) : Fintype (data.State j c) :=
    data.stateFintype j c
  letI (j : ℕ) (c : data.Coordinate j) : DecidablePred (data.upper j c) :=
    data.upperDecidable j c
  letI (j : ℕ) (c : data.Coordinate j) : DecidablePred (data.lower j c) :=
    data.lowerDecidable j c
  refine
    { balanced := data.balanced
      balanceLaw := data.balanceLaw
      productLaw := ?_ }
  exact randomTotalProductLawOfHeterogeneousProduct simpleRandomWalk
      data.balanced (bandOccupancy m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48)
      shellGrowth48 (shellCount48 m band.beta) data.totalBound
      data.Coordinate data.State data.weight data.upper data.lower
      data.ratioConstant data.pair_bound data.fixedTotal_disintegrate
      data.weight_nonneg data.upper_lower_disjoint
      data.ratioConstant_nonneg data.window_ratio

/-- Per-band candidate overflow with the heterogeneous product estimate
fully instantiated.  The canonical stopped one-point theorem is consumed by
the underlying low-scale bound. -/
theorem simpleRandomWalk_randomClockDominatingBandOverflow_le_of_heterogeneous
    {m cutoff : ℕ} {band : RandomClockBand}
    (hone : CanonicalStoppedOnePointAt m)
    (hbudget : CandidateBudgetArithmeticAt m)
    (hcutoff : cutoff ≤ ExternalProposition44.hlozCutoff44 m)
    (hthreshold : ExternalProposition44.hlozOnePointLevel44 m ≤
      band.externalThreshold)
    (hbeta : kappaOne ≤ band.beta)
    (data : HeterogeneousBandProductData m cutoff band) :
    simpleRandomWalk (randomClockDominatingBandOverflow m cutoff band) ≤
      bandOverflowCoefficient
        (bandProductScreenOfHeterogeneousData data) := by
  exact simpleRandomWalk_randomClockDominatingBandOverflow_le
    hone hbudget hcutoff hthreshold hbeta
      (bandProductScreenOfHeterogeneousData data)

/-- Finite actual random-clock overflow after the heterogeneous product-tail
constructor has discharged every product upper bound. -/
theorem eventually_simpleRandomWalk_randomClockCandidateOverflow_le_sum_of_heterogeneous
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hcutoff : ∀ᶠ m : ℕ in Filter.atTop,
      cutoff m ≤ ExternalProposition44.hlozCutoff44 m)
    (hthreshold : ∀ᶠ m : ℕ in Filter.atTop,
      ∀ band ∈ bands m,
        ExternalProposition44.hlozOnePointLevel44 m ≤
          band.externalThreshold)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band,
      HeterogeneousBandProductData m (cutoff m) band) :
    ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalk
          (HLOZGapEstimate.candidateOverflow (bands m)
            (randomClockBandSites m (cutoff m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        ∑ band ∈ bands m,
          bandOverflowCoefficient
            (bandProductScreenOfHeterogeneousData (data m band)) := by
  exact eventually_simpleRandomWalk_randomClockCandidateOverflow_le_sum
    cutoff bands hcutoff hthreshold hbeta
      (fun m band ↦ bandProductScreenOfHeterogeneousData (data m band))

end

end Erdos1165.HLOZLowScaleProductInstantiation
