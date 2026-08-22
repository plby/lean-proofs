/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixExactCoordinateProductClosure
import ErdosProblems.Erdos1165.HLOZAllSixStoppedOnePointInstantiation
import ErdosProblems.Erdos1165.TilingAwayNegativeBinomial

/-!
# Local-CLT constructor for the all-six stopped product tail

This file derives the normalized one-coordinate window comparison directly
from the literal tiling-away negative-binomial law.  Thus the product datum
below does not assume a coordinate probability inequality.
-/

open Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZAllSixLocalCLTProductClosure

open FiniteDominoProductLaw
open HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure
open TilingAwayNegativeBinomial TilingCappedMarginalization
open TilingSpatialInsertionFiber NearFavoriteThresholded
open ScreeningInstantiation NegativeBinomialLocalCLT
open HLOZGapRandomClockScreen HLOZProposition48Candidates
open HLOZAllSixStoppedOnePointInstantiation

noncomputable section

/-- Literal factored stopped-fibre data with canonical finite windows.  All
fields are deterministic window or final-envelope facts; the normalized
window probability comparison is a conclusion of the constructor below. -/
structure TilingLocalCLTRandomTotalTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) (K : ℝ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (_b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)), Finset ℕ
  lowerWindow : ∀ z cap
    (_b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)), Finset ℕ
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalThresholdedUpperTail
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ upperWindow z cap b)
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ lowerWindow z cap b)
        threshold G j bound ell
  windows_disjoint : ∀ z cap b,
    Disjoint (upperWindow z cap b) (lowerWindow z cap b)
  upper_lt_truncation : ∀ z cap b v,
    v ∈ upperWindow z cap b → v < factored.upper z cap b
  lower_lt_truncation : ∀ z cap b v,
    v ∈ lowerWindow z cap b → v < factored.upper z cap b
  upper_le_cap : ∀ z cap b v, v ∈ upperWindow z cap b → v ≤ cap
  lower_le_cap : ∀ z cap b v, v ∈ lowerWindow z cap b → v ≤ cap
  coordinate_count_pos : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
    0 < Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
      (factored.start z cap) (factored.retained z cap) b.1)
  deviationRadius : ∀ z cap,
    TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap) → ℝ
  windowSeparation : ∀ z cap,
    TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap) → ℝ
  deviationRadius_nonneg : ∀ z cap b, 0 ≤ deviationRadius z cap b
  windowSeparation_nonneg : ∀ z cap b, 0 ≤ windowSeparation z cap b
  moderate : ∀ z cap b,
    deviationRadius z cap b ≤
      (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
        (factored.start z cap) (factored.retained z cap) b.1) : ℝ) / 30
  lower_nonempty : ∀ z cap b, (lowerWindow z cap b).Nonempty
  window_card : ∀ z cap b,
    (upperWindow z cap b).card ≤ (lowerWindow z cap b).card
  upper_deviation : ∀ z cap b v, v ∈ upperWindow z cap b →
    |deviation (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
      (factored.start z cap) (factored.retained z cap) b.1)) v| ≤
        deviationRadius z cap b
  lower_deviation : ∀ z cap b v, v ∈ lowerWindow z cap b →
    |deviation (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
      (factored.start z cap) (factored.retained z cap) b.1)) v| ≤
        deviationRadius z cap b
  pair_deviation : ∀ z cap b u, u ∈ upperWindow z cap b →
    ∀ l, l ∈ lowerWindow z cap b →
      |deviation (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) u -
        deviation (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) l| ≤
        windowSeparation z cap b
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  localRatio_le : ∀ z cap b,
    adjacentLocalRatio
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1))
        (deviationRadius z cap b) (windowSeparation z cap b) ≤
      ratioConstant z cap
  cost_nonneg : 0 ≤ K
  envelope : ∀ z cap total, total < bound + 1 →
    (1 + ratioConstant z cap / (1 + ratioConstant z cap)) ^ total /
        (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K

/-- The literal negative-binomial local CLT supplies the normalized
one-coordinate comparison required by the exact-coordinate product law. -/
noncomputable def exactCoordinateTailDataOfLocalCLTData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingLocalCLTRandomTotalTailData piece next
      threshold G j bound K) :
    TilingExactCoordinateRandomTotalTailData piece next
      threshold G j bound K where
  factored := data.factored
  upperWindow := fun z cap b v ↦ (v : ℕ) ∈ data.upperWindow z cap b
  lowerWindow := fun z cap b v ↦ (v : ℕ) ∈ data.lowerWindow z cap b
  upperDecidable := fun z cap b v ↦
    Finset.decidableMem v.val (data.upperWindow z cap b)
  lowerDecidable := fun z cap b v ↦
    Finset.decidableMem v.val (data.lowerWindow z cap b)
  accepts_iff := data.accepts_iff
  upper_lower_disjoint := by
    intro z cap b v hv
    exact Finset.disjoint_left.mp (data.windows_disjoint z cap b) hv.1 hv.2
  ratioConstant := data.ratioConstant
  ratioConstant_nonneg := data.ratioConstant_nonneg
  window_ratio := by
    intro z cap b
    calc
      (∑ v : Fin (data.factored.upper z cap b),
          if (v : ℕ) ∈ data.upperWindow z cap b then
            coordinateMass
              (tilingAwayPointMass (cap := cap) (data.factored.tiling z cap)
                (data.factored.start z cap) (data.factored.retained z cap)
                (data.factored.distinguished z cap))
              (data.factored.upper z cap) b v else 0) ≤
          adjacentLocalRatio
              (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
                (data.factored.start z cap) (data.factored.retained z cap) b.1))
              (data.deviationRadius z cap b)
              (data.windowSeparation z cap b) *
            ∑ v : Fin (data.factored.upper z cap b),
              if (v : ℕ) ∈ data.lowerWindow z cap b then
                coordinateMass
                  (tilingAwayPointMass (cap := cap)
                    (data.factored.tiling z cap) (data.factored.start z cap)
                    (data.factored.retained z cap)
                    (data.factored.distinguished z cap))
                  (data.factored.upper z cap) b v else 0 := by
        exact tilingAway_coordinateMass_window_ratio_of_localCLT
          (data.factored.tiling z cap) (data.factored.start z cap)
          (data.factored.retained z cap) (data.factored.distinguished z cap)
          (data.factored.upper z cap) b (data.upperWindow z cap b)
          (data.lowerWindow z cap b) (data.upper_lt_truncation z cap b)
          (data.lower_lt_truncation z cap b) (data.upper_le_cap z cap b)
          (data.lower_le_cap z cap b) (data.coordinate_count_pos z cap b)
          (data.deviationRadius_nonneg z cap b)
          (data.windowSeparation_nonneg z cap b) (data.moderate z cap b)
          (data.lower_nonempty z cap b) (data.window_card z cap b)
          (data.upper_deviation z cap b) (data.lower_deviation z cap b)
          (data.pair_deviation z cap b)
      _ ≤ data.ratioConstant z cap *
            ∑ v : Fin (data.factored.upper z cap b),
              if (v : ℕ) ∈ data.lowerWindow z cap b then
                coordinateMass
                  (tilingAwayPointMass (cap := cap)
                    (data.factored.tiling z cap) (data.factored.start z cap)
                    (data.factored.retained z cap)
                    (data.factored.distinguished z cap))
                  (data.factored.upper z cap) b v else 0 := by
        apply mul_le_mul_of_nonneg_right (data.localRatio_le z cap b)
        apply Finset.sum_nonneg
        intro v _
        split
        · apply coordinateMass_nonneg_of_pointMass_nonneg
          intro b' ell
          exact tilingAwayExactTotalMass_nonneg
            (data.factored.tiling z cap) (data.factored.start z cap)
            (data.factored.retained z cap) (data.factored.distinguished z cap)
            b' ell
        · exact le_rfl
  cost_nonneg := data.cost_nonneg
  envelope := data.envelope

/-- One adjacent-shell product interface in which the coordinate window
comparison is specified only through the negative-binomial local-CLT
hypotheses. -/
structure TilingLocalCLTInterfaceProductData
    (t : TilingLazyDecomposition.DominoTiling) (m k : ℕ)
    (next : Set WalkPath) (threshold : ℕ → ℕ)
    (G j bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ VariableStoppedTracePartition.thresholdReachStage m k
  tail : TilingLocalCLTRandomTotalTailData
    (TilingVariableStoppedTracePartition.favoriteTilingStagePiece t m k
      (VariableStoppedTracePartition.thresholdReachStage m k))
    next threshold G j bound K

/-- Insert the checked negative-binomial local-CLT comparison into one
adjacent-shell interface. -/
noncomputable def exactCoordinateInterfaceDataOfLocalCLTData
    {t : TilingLazyDecomposition.DominoTiling} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ}
    {G j bound : ℕ} {K : ℝ}
    (data : TilingLocalCLTInterfaceProductData t m k next
      threshold G j bound K) :
    TilingExactCoordinateInterfaceProductData t m k next
      threshold G j bound K where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  tail := exactCoordinateTailDataOfLocalCLTData data.tail

/-- Positive-tail all-six product data whose coordinate comparison is
entirely supplied by explicit finite-window local-CLT hypotheses. -/
structure AllSixLocalCLTBandProductData
    (t : TilingLazyDecomposition.DominoTiling) (m cutoff : ℕ)
    (band : RandomClockBand) where
  lawStart : ℕ
  balanced : ℕ → Set WalkPath
  balanceLaw : lawStart ≤ m → 0 < m → ∀ shell,
    HLOZThresholdedShellScreening.GeometricBalanceLaw
      (Site := Point) simpleRandomWalk (balanced shell) m
  interfaceCost : ℕ → ℝ
  interfaceCost_nonneg : ∀ shell, 0 ≤ interfaceCost shell
  totalBound : ℕ → ℕ
  product : lawStart ≤ m → 0 < m →
    ∀ shell, shell < shellCount48 m band.beta - 1 →
      TilingLocalCLTInterfaceProductData t m band.oldRank
        (balanced shell ∩ NearFavoriteThresholded.thresholdedGrowthFailure
          (HLOZAllSixBandProductClosure.tilingBandOccupancy t m cutoff band)
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shellGrowth48 shell)
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        shellGrowth48 shell (totalBound shell) (interfaceCost shell)

/-- Insert all local-CLT coordinate comparisons, leaving the checked
all-six exact-coordinate product datum. -/
noncomputable def allSixExactCoordinateDataOfLocalCLTData
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (data : AllSixLocalCLTBandProductData t m cutoff band) :
    AllSixExactCoordinateBandProductData t m cutoff band where
  lawStart := data.lawStart
  balanced := data.balanced
  balanceLaw := data.balanceLaw
  interfaceCost := data.interfaceCost
  interfaceCost_nonneg := data.interfaceCost_nonneg
  totalBound := data.totalBound
  product := by
    intro hstart hm shell hshell
    exact exactCoordinateInterfaceDataOfLocalCLTData
      (data.product hstart hm shell hshell)

/-- The finite-band stopped Proposition 4.8 estimate with the external
endpoint-chain theorem, coordinate normalization, and the local-CLT window
comparison all discharged. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_localCLTData
    (t : TilingLazyDecomposition.DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hcutoff : ∀ᶠ m : ℕ in Filter.atTop,
      cutoff m ≤ ExternalProposition44.hlozCutoff44 m)
    (hphase : ∀ m band, band ∈ bands m → band.vertexPhase = false)
    (hthreshold : ∀ᶠ m : ℕ in Filter.atTop, ∀ band ∈ bands m,
      ExternalProposition44.hlozOnePointLevel44 m + 1 ≤
        band.externalThreshold)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band,
      AllSixLocalCLTBandProductData t m (cutoff m) band)
    (hstart : ∀ᶠ m : ℕ in Filter.atTop, ∀ band ∈ bands m,
      (data m band).lawStart ≤ m) :
    ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalk
          (HLOZTilingGapRandomClockScreen.tilingRandomClockCandidateOverflow
            t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          HLOZAllSixBandProductClosure.allSixBandOverflowCoefficient
            (HLOZAllSixFactoredProductClosure.allSixBandProductDataOfFactoredData
              (allSixFactoredBandProductDataOfExactCoordinateData
                (allSixExactCoordinateDataOfLocalCLTData (data m band)))) :=
  eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_exactProductData
    t cutoff bands hcutoff hphase hthreshold hbeta
      (fun m band ↦ allSixExactCoordinateDataOfLocalCLTData (data m band))
      hstart

end

end Erdos1165.HLOZAllSixLocalCLTProductClosure
