/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixFactoredProductClosure

/-!
# Exact coordinate probabilities for all-six stopped product screening

The point mass in `TilingCappedMarginalization` is a literal finite sum of
nonnegative geometric masses.  Its zero-total atom is strictly positive.
This file uses those two facts to prove, rather than assume, the coordinate
probability hypotheses of the heterogeneous product estimate.
-/

open Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZAllSixExactCoordinateProductClosure

open FiniteDominoProductLaw
open HLOZAllSixBandProductClosure HLOZAllSixFactoredProductClosure
open TilingCappedMarginalization TilingLazyDecomposition
open NearFavoriteThresholded TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

/-- A normalized coordinate mass is nonnegative whenever its raw point
mass is nonnegative. -/
theorem coordinateMass_nonneg_of_pointMass_nonneg
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (hpoint : ∀ b ell, 0 ≤ pointMass b ell)
    (b : Domino) (v : Fin (upper b)) :
    0 ≤ coordinateMass pointMass upper b v := by
  rw [coordinateMass, if_pos v.isLt]
  apply div_nonneg
  · exact hpoint b v
  · exact Finset.sum_nonneg fun j _ ↦ hpoint b j

/-- The literal normalized away-total mass has total mass exactly one.
The positivity of `upper` puts the strictly positive zero-total atom inside
the normalizing sum. -/
theorem sum_coordinateMass_eq_one_of_zero_pos
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (hpoint : ∀ b ell, 0 ≤ pointMass b ell)
    (hupper : ∀ b, 0 < upper b) (hzero : ∀ b, 0 < pointMass b 0)
    (b : Domino) :
    (∑ v : Fin (upper b), coordinateMass pointMass upper b v) = 1 := by
  classical
  let v0 : Fin (upper b) := ⟨0, hupper b⟩
  have hden_pos : 0 < ∑ v : Fin (upper b), pointMass b v := by
    have hv0 : 0 < pointMass b v0 := by
      simpa [v0] using hzero b
    exact hv0.trans_le (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun v : Fin (upper b) ↦ pointMass b (v : ℕ))
      (fun v _ ↦ hpoint b v) (Finset.mem_univ v0))
  rw [show (∑ v : Fin (upper b), coordinateMass
      pointMass upper b v) =
      ∑ v : Fin (upper b), pointMass b v /
        ∑ j : Fin (upper b), pointMass b j by
    apply Finset.sum_congr rfl
    intro v _
    rw [coordinateMass, if_pos v.isLt]]
  rw [← Finset.sum_div, div_self (ne_of_gt hden_pos)]

/-- Factored stopped-fibre data with only the genuinely analytic
one-coordinate inputs.  Coordinate nonnegativity and normalization are not
fields: they follow from the literal geometric point mass. -/
structure TilingExactCoordinateRandomTotalTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) (K : ℝ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalThresholdedUpperTail
        (upperWindow z cap) (lowerWindow z cap) threshold G j bound ell
  upper_lower_disjoint : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap))
    (v : Fin (factored.upper z cap b)),
      ¬(upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
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

/-- Insert the two exact coordinate-probability proofs. -/
noncomputable def factoredRandomTotalTailDataOfExactCoordinateData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingExactCoordinateRandomTotalTailData piece next
      threshold G j bound K) :
    TilingFactoredRandomTotalTailData piece next threshold G j bound K where
  factored := data.factored
  upperWindow := data.upperWindow
  lowerWindow := data.lowerWindow
  upperDecidable := data.upperDecidable
  lowerDecidable := data.lowerDecidable
  accepts_iff := data.accepts_iff
  coordinate_nonneg := by
    intro z cap b v
    apply coordinateMass_nonneg_of_pointMass_nonneg
    intro b' ell
    exact tilingAwayExactTotalMass_nonneg
      (data.factored.tiling z cap) (data.factored.start z cap)
      (data.factored.retained z cap) (data.factored.distinguished z cap)
      b' ell
  coordinate_sum_le_one := by
    intro z cap b
    apply (sum_coordinateMass_eq_one_of_zero_pos
      (tilingAwayPointMass (cap := cap) (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap))
      (data.factored.upper z cap) ?_ (data.factored.upper_pos z cap) ?_ b).le
    · intro b' ell
      exact tilingAwayExactTotalMass_nonneg
        (data.factored.tiling z cap) (data.factored.start z cap)
        (data.factored.retained z cap) (data.factored.distinguished z cap)
        b' ell
    · intro b'
      exact tilingAwayExactTotalMass_zero_pos
        (data.factored.tiling z cap) (data.factored.start z cap)
        (data.factored.retained z cap) (data.factored.distinguished z cap) b'
  upper_lower_disjoint := data.upper_lower_disjoint
  ratioConstant := data.ratioConstant
  ratioConstant_nonneg := data.ratioConstant_nonneg
  window_ratio := data.window_ratio
  cost_nonneg := data.cost_nonneg
  envelope := data.envelope

/-- One adjacent-shell interface with exact coordinate probabilities. -/
structure TilingExactCoordinateInterfaceProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingExactCoordinateRandomTotalTailData
    (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next
    threshold G j bound K

/-- Forget the two exact coordinate-probability lemmas after proving them. -/
noncomputable def factoredInterfaceProductDataOfExactCoordinateData
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingExactCoordinateInterfaceProductData t m k next
      threshold G j bound K) :
    TilingFactoredInterfaceProductData t m k next threshold G j bound K where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  tail := factoredRandomTotalTailDataOfExactCoordinateData data.tail

/-- Positive-tail all-six data in which normalization of every literal
away-coordinate law is derived automatically. -/
structure AllSixExactCoordinateBandProductData
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
      TilingExactCoordinateInterfaceProductData t m band.oldRank
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

/-- Convert exact-coordinate all-six data to the already checked factored
product endgame. -/
noncomputable def allSixFactoredBandProductDataOfExactCoordinateData
    {t : DominoTiling} {m cutoff : ℕ}
    {band : HLOZGapRandomClockScreen.RandomClockBand}
    (data : AllSixExactCoordinateBandProductData t m cutoff band) :
    AllSixFactoredBandProductData t m cutoff band where
  lawStart := data.lawStart
  balanced := data.balanced
  balanceLaw := data.balanceLaw
  interfaceCost := data.interfaceCost
  interfaceCost_nonneg := data.interfaceCost_nonneg
  totalBound := data.totalBound
  product := by
    intro hstart hm shell hshell
    exact factoredInterfaceProductDataOfExactCoordinateData
      (data.product hstart hm shell hshell)

/-- Per-band candidate-overflow estimate from exact coordinate data. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_exactCoordinateProductData
    {t : DominoTiling} {m cutoff : ℕ}
    {band : HLOZGapRandomClockScreen.RandomClockBand}
    (hbudget : HLOZLowScaleCandidateOverflow.CandidateBudgetArithmeticAt m)
    (hbeta : ScreeningInstantiation.kappaOne ≤ band.beta)
    (onePoint : TilingStoppedExternalOnePointData t m cutoff band)
    (data : AllSixExactCoordinateBandProductData t m cutoff band)
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk
        {s | HLOZProposition48Candidates.candidateBudget48 m band.beta <
          (HLOZTilingGapRandomClockScreen.tilingRandomClockBandSites
            t m cutoff s band).card} ≤
      tilingBandInterfaceOverflowCoefficient
        (tilingBandInterfaceScreenOfProductData
          (allSixBandProductDataOfFactoredData
            (allSixFactoredBandProductDataOfExactCoordinateData data))
          hstart hm) :=
  simpleRandomWalk_tilingRandomClockBandOverflow_le_of_factoredProductData
    hbudget hbeta onePoint
      (allSixFactoredBandProductDataOfExactCoordinateData data) hstart hm

end

end Erdos1165.HLOZAllSixExactCoordinateProductClosure
