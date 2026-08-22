/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure
import ErdosProblems.Erdos1165.TilingCappedMarginalization

/-!
# Factored marginal input for the all-six random-total product tail

`TilingCappedMarginalization` derives the normalized stopped-coordinate
product identity from pointwise distinguished/away factorization.  This file
connects that derived certificate to the heterogeneous random-total estimate
used by `HLOZAllSixBandProductClosure`.  Consequently a consumer supplies no
marginal-sum identity: only the literal factorization, the screened predicate
identification, and the one-coordinate analytic inequalities remain.
-/

open Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZAllSixFactoredProductClosure

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open TilingCappedMarginalization TilingStoppedProductDisintegration
open TilingLazyDecomposition TilingSpatialInsertionFiber
open NearFavoriteThresholded VariableStoppedTracePartition
open TilingVariableStoppedTracePartition

noncomputable section

/-- A pointwise-factored stopped fibre together with exactly the numerical
data needed by the heterogeneous random-total upper-tail estimate.  The
coordinate point mass below is the literal capped geometric away-total mass.
-/
structure TilingFactoredRandomTotalTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) (K : ℝ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalThresholdedUpperTail
        (upperWindow z cap) (lowerWindow z cap) threshold G j bound ell
  coordinate_nonneg : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap))
    (v : Fin (factored.upper z cap b)),
      0 ≤ coordinateMass
        (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap)
          (factored.distinguished z cap))
        (factored.upper z cap) b v
  coordinate_sum_le_one : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      (∑ v : Fin (factored.upper z cap b),
        coordinateMass
          (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap)
            (factored.distinguished z cap))
          (factored.upper z cap) b v) ≤ 1
  upper_lower_disjoint : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap))
    (v : Fin (factored.upper z cap b)),
      ¬(upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      (∑ v : Fin (factored.upper z cap b),
        if upperWindow z cap b v then
          coordinateMass
            (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap)
              (factored.distinguished z cap))
            (factored.upper z cap) b v else 0) ≤
        ratioConstant z cap *
          ∑ v : Fin (factored.upper z cap b),
            if lowerWindow z cap b v then
              coordinateMass
                (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
                  (factored.start z cap) (factored.retained z cap)
                  (factored.distinguished z cap))
                (factored.upper z cap) b v else 0
  cost_nonneg : 0 ≤ K
  envelope : ∀ z cap total, total < bound + 1 →
    (1 + ratioConstant z cap / (1 + ratioConstant z cap)) ^ total /
        (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K

/-- The factored spatial data automatically provides the raw normalized
coordinate identity; the remaining numerical fields are transported
definitionally to the checked random-total tail certificate. -/
noncomputable def randomTotalTailSpecOfFactoredData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingFactoredRandomTotalTailData piece next
      threshold G j bound K) :
    TilingRandomTotalProductTailSpec piece next threshold G j bound K := by
  classical
  let raw := tilingStoppedCoordinateProductSpecOfFactoredData data.factored
  exact {
    raw := raw
    upperWindow := data.upperWindow
    lowerWindow := data.lowerWindow
    upperDecidable := data.upperDecidable
    lowerDecidable := data.lowerDecidable
    accepts_iff := data.accepts_iff
    coordinate_nonneg := data.coordinate_nonneg
    coordinate_sum_le_one := data.coordinate_sum_le_one
    upper_lower_disjoint := data.upper_lower_disjoint
    ratioConstant := data.ratioConstant
    ratioConstant_nonneg := data.ratioConstant_nonneg
    window_ratio := data.window_ratio
    cost_nonneg := data.cost_nonneg
    envelope := data.envelope }

/-- Direct factored constructor for one adjacent-shell all-six interface. -/
structure TilingFactoredInterfaceProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingFactoredRandomTotalTailData
    (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next
    threshold G j bound K

/-- Forget only the now-proved marginalization layer. -/
noncomputable def interfaceProductDataOfFactoredData
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingFactoredInterfaceProductData t m k next
      threshold G j bound K) :
    TilingInterfaceProductData t m k next threshold G j bound K where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  tail := randomTotalTailSpecOfFactoredData data.tail

/-- Countable trace summation and the heterogeneous finite-product estimate
from literal pointwise stopped-coordinate factorization. -/
theorem simpleRandomWalk_real_interface_le_of_factoredTilingProduct
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingFactoredInterfaceProductData t m k next
      threshold G j bound K) :
    simpleRandomWalk.real next ≤ K :=
  simpleRandomWalk_real_interface_le_of_tilingProduct
    (interfaceProductDataOfFactoredData data)

/-- Positive-tail all-six data whose every adjacent interface is presented
by literal pointwise stopped-coordinate factorization. -/
structure AllSixFactoredBandProductData
    (t : DominoTiling) (m cutoff : ℕ)
    (band : HLOZGapRandomClockScreen.RandomClockBand) where
  lawStart : ℕ
  balanced : ℕ → Set WalkPath
  balanceLaw : lawStart ≤ m → 0 < m → ∀ shell,
    HLOZThresholdedShellScreening.GeometricBalanceLaw
      (Site := Point) simpleRandomWalk (balanced shell) m
  interfaceCost : ℕ → ℝ
  interfaceCost_nonneg : ∀ shell, 0 ≤ interfaceCost shell
  totalBound : ℕ → ℕ
  product : lawStart ≤ m → 0 < m →
    ∀ shell, shell < HLOZProposition48Candidates.shellCount48 m band.beta - 1 →
      TilingFactoredInterfaceProductData t m band.oldRank
        (balanced shell ∩ NearFavoriteThresholded.thresholdedGrowthFailure
          (tilingBandOccupancy t m cutoff band)
          (ScreeningInstantiation.geometricShellThreshold
            (HLOZProposition48Candidates.initialBudget48 m)
            HLOZProposition48Candidates.shellGrowth48)
          HLOZProposition48Candidates.shellGrowth48 shell)
        (ScreeningInstantiation.geometricShellThreshold
          (HLOZProposition48Candidates.initialBudget48 m)
          HLOZProposition48Candidates.shellGrowth48)
        HLOZProposition48Candidates.shellGrowth48 shell
        (totalBound shell) (interfaceCost shell)

/-- Marginalization is discharged once, uniformly over all adjacent shell
interfaces, producing the exact input expected by the all-six endgame. -/
noncomputable def allSixBandProductDataOfFactoredData
    {t : DominoTiling} {m cutoff : ℕ}
    {band : HLOZGapRandomClockScreen.RandomClockBand}
    (data : AllSixFactoredBandProductData t m cutoff band) :
    AllSixBandProductData t m cutoff band where
  lawStart := data.lawStart
  balanced := data.balanced
  balanceLaw := data.balanceLaw
  interfaceCost := data.interfaceCost
  interfaceCost_nonneg := data.interfaceCost_nonneg
  totalBound := data.totalBound
  product := by
    intro hstart hm shell hshell
    exact interfaceProductDataOfFactoredData
      (data.product hstart hm shell hshell)

/-- Exact per-band overflow from factored all-six stopped-coordinate data.
No normalized marginal or product-disintegration equality is a premise. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_factoredProductData
    {t : DominoTiling} {m cutoff : ℕ}
    {band : HLOZGapRandomClockScreen.RandomClockBand}
    (hbudget : HLOZLowScaleCandidateOverflow.CandidateBudgetArithmeticAt m)
    (hbeta : ScreeningInstantiation.kappaOne ≤ band.beta)
    (onePoint : TilingStoppedExternalOnePointData t m cutoff band)
    (data : AllSixFactoredBandProductData t m cutoff band)
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk
        {s | HLOZProposition48Candidates.candidateBudget48 m band.beta <
          (HLOZTilingGapRandomClockScreen.tilingRandomClockBandSites
            t m cutoff s band).card} ≤
      tilingBandInterfaceOverflowCoefficient
        (tilingBandInterfaceScreenOfProductData
          (allSixBandProductDataOfFactoredData data) hstart hm) :=
  simpleRandomWalk_tilingRandomClockBandOverflow_le_of_productData
    hbudget hbeta onePoint (allSixBandProductDataOfFactoredData data)
      hstart hm

end

end Erdos1165.HLOZAllSixFactoredProductClosure
