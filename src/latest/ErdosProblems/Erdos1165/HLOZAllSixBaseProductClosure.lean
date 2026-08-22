/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixExactCoordinateProductClosure
import ErdosProblems.Erdos1165.HLOZSharpProductNumerics
import ErdosProblems.Erdos1165.TilingValidTraceCappedStageAdapter

/-!
# Product screening of the initial HLOZ shell

The adjacent-shell product screen cannot control the initial shell: that
event has a fixed count threshold, but no preceding shell with which to form
a growth ratio.  Applying the stopped one-point estimate and Markov's
inequality at this point loses the exponential product structure.

This file gives the initial shell its own finite product screen.  Inside each
stopped trace fibre we condition on the *actual* number of coordinates in the
two comparison windows and apply the heterogeneous fixed-total estimate with
the fixed cut.  Exact totals are then summed without a cardinality loss.  The
resulting product cost replaces the former Tonelli--Markov first term in the
shell recurrence.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZAllSixBaseProductClosure

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure HLOZAllSixFactoredProductClosure
open HLOZAllSixExactCoordinateProductClosure HLOZSharpProductNumerics
open HLOZDynamicThresholdedScreening HLOZThresholdedShellScreening
open HLOZGapEstimate HLOZGapRandomClockScreen HLOZLowScaleCandidateOverflow
open HLOZProposition48Candidates HLOZTilingGapRandomClockScreen
open NearFavoriteShells NearFavoriteThresholded ScreeningInstantiation
open TilingCappedMarginalization TilingLazyDecomposition
open TilingStoppedProductDisintegration TilingVariableStoppedTracePartition
open VariableStoppedTracePartition
open HLOZTraceCappedProductScreening
open TilingValidTraceCappedStageAdapter

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

/-! ## Summable target cost -/

/-- The fixed-cut shell-zero cost at the same explicit logarithmic rate as
the sharp adjacent-interface product estimate. -/
noncomputable def sharpBaseProductCost (m : ℕ) : ℝ :=
  Real.exp
    (-sharpProductRate * ((initialBudget48 m + 1 : ℕ) : ℝ))

lemma sharpBaseProductCost_pos (m : ℕ) : 0 < sharpBaseProductCost m := by
  unfold sharpBaseProductCost
  positivity

lemma sharpBaseProductCost_nonneg (m : ℕ) :
    0 ≤ sharpBaseProductCost m := (sharpBaseProductCost_pos m).le

/-- The integer shell-zero cut pays at least one full `log(m)^2` exponent. -/
theorem sharpBaseProductCost_le_exp_neg_log_sq (m : ℕ) :
    sharpBaseProductCost m ≤
      Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
  unfold sharpBaseProductCost
  rw [Real.exp_le_exp]
  have hceil : Real.log (m : ℝ) ^ 2 ≤
      (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) :=
    Nat.le_ceil (Real.log (m : ℝ) ^ 2)
  have hbudget : Real.log (m : ℝ) ^ 2 ≤
      ((initialBudget48 m + 1 : ℕ) : ℝ) := by
    unfold initialBudget48
    push_cast
    linarith
  nlinarith [sharpProductRate_pos]

/-- In particular the sharp base-product costs form a summable real
sequence. -/
theorem summable_sharpBaseProductCost : Summable sharpBaseProductCost := by
  let r := sharpProductRate
  have hr : 0 < r := sharpProductRate_pos
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have htarget : Summable
      (fun m : ℕ ↦ Real.exp (-r * Real.log (m : ℝ) ^ 2)) := by
    apply Summable.of_norm_bounded_eventually hpoly
    have hlarge : ∀ᶠ m : ℕ in cofinite,
        2 / r ≤ Real.log (m : ℝ) := by
      simpa only [Nat.cofinite_eq_atTop] using
        hlog.eventually (eventually_ge_atTop (2 / r))
    have hmpos : ∀ᶠ m : ℕ in cofinite, 0 < m := by
      simpa only [Nat.cofinite_eq_atTop] using (eventually_gt_atTop 0)
    filter_upwards [hlarge, hmpos] with m hlogm hmpos
    have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    have hexponent : -r * Real.log (m : ℝ) ^ 2 ≤
        Real.log (m : ℝ) * (-2) := by
      have hrMul : 2 ≤ r * Real.log (m : ℝ) := by
        calc
          2 = r * (2 / r) := by field_simp
          _ ≤ r * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlogm hr.le
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.rpow_def_of_pos (by exact_mod_cast hmpos)]
    exact Real.exp_le_exp.mpr hexponent
  apply Summable.of_nonneg_of_le
    (fun m ↦ sharpBaseProductCost_nonneg m)
    (fun m ↦ sharpBaseProductCost_le_exp_neg_log_sq m)
    htarget

/-- A fixed-cut upper tail, partitioned by the actual number of coordinates
in the two comparison windows. -/
def randomTotalFixedCutUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ) (ell : ∀ c, State c) : Prop :=
  let total := (pairSupport upper lower ell).card
  total < bound + 1 ∧ cut ≤ upperCount upper ell

/-- The exact pair-total moment retained before the final fixed-cut Chernoff
division. -/
def boundedPairMoment
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (C : ℝ) (bound : ℕ) : ℝ :=
  ∑ total ∈ Finset.range (bound + 1),
    exactPairTotalMass weight upper lower total *
      (1 + C / (1 + C)) ^ total

instance instDecidablePredRandomTotalFixedCutUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ) :
    DecidablePred (randomTotalFixedCutUpperTail upper lower cut bound) :=
  fun ell ↦ by
    unfold randomTotalFixedCutUpperTail
    infer_instance

/-- Disintegrate the aggregate fixed-cut screen over its genuine pair total. -/
theorem sum_randomTotalFixedCutUpperTail_eq_sum_fixedTotal
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ) :
    (∑ ell : ∀ c, State c,
        if randomTotalFixedCutUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) =
      ∑ total ∈ Finset.range (bound + 1),
        ∑ ell : ∀ c, State c,
          if fixedTotalUpperTail upper lower total cut ell then
            productPointMass weight ell else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hbound : (pairSupport upper lower ell).card < bound + 1
  · have hmem : (pairSupport upper lower ell).card ∈
        Finset.range (bound + 1) := Finset.mem_range.mpr hbound
    rw [Finset.sum_eq_single (pairSupport upper lower ell).card]
    · by_cases hcut : cut ≤ upperCount upper ell <;>
        simp [randomTotalFixedCutUpperTail, fixedTotalUpperTail, hbound, hcut]
    · intro total _ hne
      have hcard : (pairSupport upper lower ell).card ≠ total := Ne.symm hne
      simp [fixedTotalUpperTail, hcard]
    · exact fun hnot ↦ (hnot hmem).elim
  · have hout : (pairSupport upper lower ell).card ∉
        Finset.range (bound + 1) := by simpa using hbound
    rw [Finset.sum_eq_zero]
    · simp [randomTotalFixedCutUpperTail, hbound]
    · intro total htotal
      have hne : (pairSupport upper lower ell).card ≠ total := by
        intro heq
        apply hout
        simpa [heq] using htotal
      simp [fixedTotalUpperTail, hne]

/-- Heterogeneous fixed-cut product bound after summing the actual pair
total.  The envelope is uniform only over totals which really occur in the
bounded product screen. -/
theorem randomTotalFixedCutUpperTail_product_bound
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (henvelope : ∀ total < bound + 1,
      (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut ≤ K) :
    (∑ ell : ∀ c, State c,
        if randomTotalFixedCutUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) ≤ K := by
  rw [sum_randomTotalFixedCutUpperTail_eq_sum_fixedTotal]
  calc
    (∑ total ∈ Finset.range (bound + 1),
      ∑ ell : ∀ c, State c,
        if fixedTotalUpperTail upper lower total cut ell then
          productPointMass weight ell else 0) ≤
        ∑ total ∈ Finset.range (bound + 1),
          exactPairTotalMass weight upper lower total *
            ((1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut) := by
      apply Finset.sum_le_sum
      intro total _
      simpa only [mul_div_assoc] using
        (fixedTotalUpperTail_product_bound weight upper lower hweight
          hdisjoint hC hratio total cut)
    _ ≤ K := sum_exactPairTotalMass_mul_cost_le weight upper lower
      hweight hnorm bound
      (fun total ↦ (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut)
      hK henvelope

/-- The sharper pre-envelope statement.  This exposes exactly the weighted
pair-total mass which must be cancelled by the literal negative-binomial
law in a shell-zero application. -/
theorem randomTotalFixedCutUpperTail_le_pairMoment
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0) :
    (∑ ell : ∀ c, State c,
        if randomTotalFixedCutUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) ≤
      boundedPairMoment weight upper lower C bound / (2 : ℝ) ^ cut := by
  unfold boundedPairMoment
  rw [sum_randomTotalFixedCutUpperTail_eq_sum_fixedTotal]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro total _
  simpa only [mul_div_assoc] using
    (fixedTotalUpperTail_product_bound weight upper lower hweight
      hdisjoint hC hratio total cut)

/-- A direct cancellation form of the fixed-cut estimate.  It separates the
probabilistic task (the exact pair-moment inequality) from the elementary
Chernoff division by `2^cut`. -/
theorem randomTotalFixedCutUpperTail_product_bound_of_pairMoment
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (hpairMoment :
      boundedPairMoment weight upper lower C bound ≤
        K * (2 : ℝ) ^ cut) :
    (∑ ell : ∀ c, State c,
        if randomTotalFixedCutUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) ≤ K := by
  refine (randomTotalFixedCutUpperTail_le_pairMoment weight upper lower
    cut bound hweight hdisjoint hC hratio).trans ?_
  rw [div_le_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ cut)]
  simpa only [mul_comm K] using hpairMoment

/-! ## Literal stopped-coordinate base tail -/

/-- A literal all-six stopped-coordinate law whose accepted vectors are the
random-total fixed-cut upper tail. -/
structure TilingRandomTotalFixedCutTailSpec {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  raw : TilingStoppedCoordinateProductSpec piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      Fin (raw.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      Fin (raw.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ell,
    raw.accepts z cap ell = true ↔
      randomTotalFixedCutUpperTail
        (upperWindow z cap) (lowerWindow z cap) cut bound ell
  coordinate_nonneg : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap))
    (v : Fin (raw.upper z cap b)),
      0 ≤ coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v
  coordinate_sum_le_one : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      (∑ v : Fin (raw.upper z cap b),
        coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v) ≤ 1
  upper_lower_disjoint : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap))
    (v : Fin (raw.upper z cap b)),
      ¬(upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      (∑ v : Fin (raw.upper z cap b), if upperWindow z cap b v then
          coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v else 0) ≤
        ratioConstant z cap *
          ∑ v : Fin (raw.upper z cap b), if lowerWindow z cap b v then
            coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v else 0
  cost_nonneg : 0 ≤ K
  envelope : ∀ z cap total, total < bound + 1 →
    (1 + ratioConstant z cap / (1 + ratioConstant z cap)) ^ total /
        (2 : ℝ) ^ cut ≤ K

/-- Pointwise-factored shell-zero data.  The coordinate masses are the
literal capped tiling-away negative-binomial masses; their nonnegativity and
normalization are therefore conclusions rather than fields. -/
structure TilingFactoredRandomTotalFixedCutTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalFixedCutUpperTail
        (upperWindow z cap) (lowerWindow z cap) cut bound ell
  upper_lower_disjoint : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap))
    (v : Fin (factored.upper z cap b)),
      ¬(upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      (∑ v : Fin (factored.upper z cap b), if upperWindow z cap b v then
          coordinateMass
            (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap)
              (factored.distinguished z cap))
            (factored.upper z cap) b v else 0) ≤
        ratioConstant z cap *
          ∑ v : Fin (factored.upper z cap b), if lowerWindow z cap b v then
            coordinateMass
              (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
                (factored.start z cap) (factored.retained z cap)
                (factored.distinguished z cap))
              (factored.upper z cap) b v else 0
  cost_nonneg : 0 ≤ K
  envelope : ∀ z cap total, total < bound + 1 →
    (1 + ratioConstant z cap / (1 + ratioConstant z cap)) ^ total /
        (2 : ℝ) ^ cut ≤ K

/-- Insert the exact normalization of every literal negative-binomial
coordinate into the fixed-cut product tail. -/
noncomputable def fixedCutTailSpecOfFactoredData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingFactoredRandomTotalFixedCutTailData
      piece next cut bound K) :
    TilingRandomTotalFixedCutTailSpec piece next cut bound K where
  raw := tilingStoppedCoordinateProductSpecOfFactoredData data.factored
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

/-- Fixed-cut stopped-coordinate data using the exact aggregate pair moment
instead of a stronger uniform-in-total envelope. -/
structure TilingRandomTotalFixedCutPairMomentTailSpec {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  raw : TilingStoppedCoordinateProductSpec piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      Fin (raw.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      Fin (raw.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ell,
    raw.accepts z cap ell = true ↔
      randomTotalFixedCutUpperTail
        (upperWindow z cap) (lowerWindow z cap) cut bound ell
  coordinate_nonneg : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap))
    (v : Fin (raw.upper z cap b)),
      0 ≤ coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v
  upper_lower_disjoint : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap))
    (v : Fin (raw.upper z cap b)),
      ¬(upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      (∑ v : Fin (raw.upper z cap b), if upperWindow z cap b v then
          coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v else 0) ≤
        ratioConstant z cap *
          ∑ v : Fin (raw.upper z cap b), if lowerWindow z cap b v then
            coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v else 0
  cost_nonneg : 0 ≤ K
  pairMoment_bound : ∀ z cap,
    boundedPairMoment
      (fun (b : TilingCappedMarginalization.TilingAwayDomino
          (raw.tiling z cap) (raw.start z cap)
          (raw.retained z cap) (raw.distinguished z cap))
        (v : Fin (raw.upper z cap b)) ↦
          coordinateMass (raw.pointMass z cap) (raw.upper z cap) b (v : ℕ))
      (upperWindow z cap) (lowerWindow z cap) (ratioConstant z cap) bound ≤
        K * (2 : ℝ) ^ cut

/-- The exact pair-moment identity is sufficient for the stopped-coordinate
product bound; no per-total relaxation is made. -/
def tilingStoppedCoordinateProductSpecOfFixedCutPairMomentTail
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingRandomTotalFixedCutPairMomentTailSpec
      piece next cut bound K) :
    TilingStoppedCoordinateProductSpec piece next (ENNReal.ofReal K) := by
  letI (z : index) (cap : ℕ)
      (b : TilingCappedMarginalization.TilingAwayDomino
        (data.raw.tiling z cap) (data.raw.start z cap)
        (data.raw.retained z cap) (data.raw.distinguished z cap)) :
      DecidablePred (data.upperWindow z cap b) := data.upperDecidable z cap b
  letI (z : index) (cap : ℕ)
      (b : TilingCappedMarginalization.TilingAwayDomino
        (data.raw.tiling z cap) (data.raw.start z cap)
        (data.raw.retained z cap) (data.raw.distinguished z cap)) :
      DecidablePred (data.lowerWindow z cap b) := data.lowerDecidable z cap b
  refine { data.raw with product_bound := ?_ }
  intro z cap
  rw [screenMass_eq_product]
  calc
    (∑ ell,
      if data.raw.accepts z cap ell = true then
        ∏ b, coordinateMass (data.raw.pointMass z cap)
          (data.raw.upper z cap) b (ell b)
      else 0) =
        ∑ ell,
          if randomTotalFixedCutUpperTail
              (data.upperWindow z cap) (data.lowerWindow z cap) cut bound ell
          then
            productPointMass
              (fun (b : TilingCappedMarginalization.TilingAwayDomino
                  (data.raw.tiling z cap) (data.raw.start z cap)
                  (data.raw.retained z cap) (data.raw.distinguished z cap))
                (v : Fin (data.raw.upper z cap b)) ↦
                  coordinateMass (data.raw.pointMass z cap)
                    (data.raw.upper z cap) b (v : ℕ)) ell
          else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [productPointMass]
      exact if_congr (data.accepts_iff z cap ell) rfl rfl
    _ ≤ K := randomTotalFixedCutUpperTail_product_bound_of_pairMoment
      (fun (b : TilingCappedMarginalization.TilingAwayDomino
          (data.raw.tiling z cap) (data.raw.start z cap)
          (data.raw.retained z cap) (data.raw.distinguished z cap))
        (v : Fin (data.raw.upper z cap b)) ↦
          coordinateMass (data.raw.pointMass z cap)
            (data.raw.upper z cap) b (v : ℕ))
      (data.upperWindow z cap) (data.lowerWindow z cap) cut bound
      (data.coordinate_nonneg z cap) (data.upper_lower_disjoint z cap)
      (data.ratioConstant_nonneg z cap) (data.window_ratio z cap)
      (data.pairMoment_bound z cap)
    _ = (ENNReal.ofReal K).toReal := by
      rw [ENNReal.toReal_ofReal data.cost_nonneg]

/-- Literal factored version of the aggregate pair-moment tail. -/
structure TilingFactoredRandomTotalFixedCutPairMomentTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      Fin (factored.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalFixedCutUpperTail
        (upperWindow z cap) (lowerWindow z cap) cut bound ell
  upper_lower_disjoint : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap))
    (v : Fin (factored.upper z cap b)),
      ¬(upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingCappedMarginalization.TilingAwayDomino
      (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
      (∑ v : Fin (factored.upper z cap b), if upperWindow z cap b v then
          coordinateMass
            (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap)
              (factored.distinguished z cap))
            (factored.upper z cap) b v else 0) ≤
        ratioConstant z cap *
          ∑ v : Fin (factored.upper z cap b), if lowerWindow z cap b v then
            coordinateMass
              (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
                (factored.start z cap) (factored.retained z cap)
                (factored.distinguished z cap))
              (factored.upper z cap) b v else 0
  cost_nonneg : 0 ≤ K
  pairMoment_bound : ∀ z cap,
    boundedPairMoment
      (fun (b : TilingCappedMarginalization.TilingAwayDomino
          (factored.tiling z cap) (factored.start z cap)
          (factored.retained z cap) (factored.distinguished z cap))
        (v : Fin (factored.upper z cap b)) ↦
          coordinateMass
            (tilingAwayPointMass (cap := cap) (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap)
              (factored.distinguished z cap))
            (factored.upper z cap) b (v : ℕ))
      (upperWindow z cap) (lowerWindow z cap) (ratioConstant z cap) bound ≤
        K * (2 : ℝ) ^ cut

/-- Exact normalization and nonnegativity of the literal negative-binomial
masses leave only the aggregate pair-moment bound. -/
noncomputable def fixedCutPairMomentTailSpecOfFactoredData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingFactoredRandomTotalFixedCutPairMomentTailData
      piece next cut bound K) :
    TilingRandomTotalFixedCutPairMomentTailSpec piece next cut bound K where
  raw := tilingStoppedCoordinateProductSpecOfFactoredData data.factored
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
  upper_lower_disjoint := data.upper_lower_disjoint
  ratioConstant := data.ratioConstant
  ratioConstant_nonneg := data.ratioConstant_nonneg
  window_ratio := data.window_ratio
  cost_nonneg := data.cost_nonneg
  pairMoment_bound := data.pairMoment_bound

/-- Replace the unit bound on the literal stopped-coordinate law by the
checked fixed-cut random-total estimate. -/
def tilingStoppedCoordinateProductSpecOfFixedCutTail
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingRandomTotalFixedCutTailSpec piece next cut bound K) :
    TilingStoppedCoordinateProductSpec piece next (ENNReal.ofReal K) := by
  letI (z : index) (cap : ℕ)
      (b : TilingCappedMarginalization.TilingAwayDomino
        (data.raw.tiling z cap) (data.raw.start z cap)
        (data.raw.retained z cap) (data.raw.distinguished z cap)) :
      DecidablePred (data.upperWindow z cap b) := data.upperDecidable z cap b
  letI (z : index) (cap : ℕ)
      (b : TilingCappedMarginalization.TilingAwayDomino
        (data.raw.tiling z cap) (data.raw.start z cap)
        (data.raw.retained z cap) (data.raw.distinguished z cap)) :
      DecidablePred (data.lowerWindow z cap b) := data.lowerDecidable z cap b
  refine { data.raw with product_bound := ?_ }
  intro z cap
  rw [screenMass_eq_product]
  calc
    (∑ ell,
      if data.raw.accepts z cap ell = true then
        ∏ b, coordinateMass (data.raw.pointMass z cap)
          (data.raw.upper z cap) b (ell b)
      else 0) =
        ∑ ell,
          if randomTotalFixedCutUpperTail
              (data.upperWindow z cap) (data.lowerWindow z cap) cut bound ell
          then
            productPointMass
              (fun (b : TilingCappedMarginalization.TilingAwayDomino
                  (data.raw.tiling z cap)
                  (data.raw.start z cap) (data.raw.retained z cap)
                  (data.raw.distinguished z cap))
                (v : Fin (data.raw.upper z cap b)) ↦
                  coordinateMass (data.raw.pointMass z cap)
                    (data.raw.upper z cap) b (v : ℕ)) ell
          else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [productPointMass]
      exact if_congr (data.accepts_iff z cap ell) rfl rfl
    _ ≤ K := randomTotalFixedCutUpperTail_product_bound
      (fun (b : TilingCappedMarginalization.TilingAwayDomino
          (data.raw.tiling z cap)
          (data.raw.start z cap) (data.raw.retained z cap)
          (data.raw.distinguished z cap))
        (v : Fin (data.raw.upper z cap b)) ↦
          coordinateMass (data.raw.pointMass z cap)
            (data.raw.upper z cap) b (v : ℕ))
      (data.upperWindow z cap) (data.lowerWindow z cap) cut bound
      (data.coordinate_nonneg z cap) (data.coordinate_sum_le_one z cap)
      (data.upper_lower_disjoint z cap)
      (data.ratioConstant_nonneg z cap) data.cost_nonneg
      (data.window_ratio z cap) (data.envelope z cap)
    _ = (ENNReal.ofReal K).toReal := by
      rw [ENNReal.toReal_ofReal data.cost_nonneg]

/-- One all-six trace screen for an arbitrary fixed-cut base event.  Only
non-null favorite trace codes are indexed; the target event is intersected
with the canonical-walk support inside the coordinate law. -/
structure TilingFixedCutBaseProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingRandomTotalFixedCutTailSpec
    (validFavoriteTilingStagePiece t m k (thresholdReachStage m k))
    (next ∩ validStepWalk) cut bound K

/-- Valid-support base data before exact away-coordinate normalization is
inserted. -/
structure TilingFactoredFixedCutBaseProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingFactoredRandomTotalFixedCutTailData
    (validFavoriteTilingStagePiece t m k (thresholdReachStage m k))
    (next ∩ validStepWalk) cut bound K

/-- Normalize the literal tiling-away negative-binomial masses on every
non-null stopped trace. -/
noncomputable def tilingFixedCutBaseProductDataOfFactoredData
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingFactoredFixedCutBaseProductData
      t m k next cut bound K) :
    TilingFixedCutBaseProductData t m k next cut bound K where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  tail := fixedCutTailSpecOfFactoredData data.tail

/-- Valid-support base data whose sharp product bound is supplied by the
exact aggregate pair moment. -/
structure TilingFixedCutPairMomentBaseProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingRandomTotalFixedCutPairMomentTailSpec
    (validFavoriteTilingStagePiece t m k (thresholdReachStage m k))
    (next ∩ validStepWalk) cut bound K

/-- Literal factored form of the aggregate-pair-moment base screen. -/
structure TilingFactoredFixedCutPairMomentBaseProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (cut bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingFactoredRandomTotalFixedCutPairMomentTailData
    (validFavoriteTilingStagePiece t m k (thresholdReachStage m k))
    (next ∩ validStepWalk) cut bound K

noncomputable def tilingFixedCutPairMomentBaseProductDataOfFactoredData
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingFactoredFixedCutPairMomentBaseProductData
      t m k next cut bound K) :
    TilingFixedCutPairMomentBaseProductData t m k next cut bound K where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  tail := fixedCutPairMomentTailSpecOfFactoredData data.tail

/-- Countable stopped traces preserve the sharp fixed-cut product cost. -/
theorem simpleRandomWalk_real_base_le_of_tilingProduct
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingFixedCutBaseProductData t m k next cut bound K) :
    simpleRandomWalk.real next ≤ K := by
  let spec := tilingStoppedCoordinateProductSpecOfFixedCutTail data.tail
  have htransition : simpleRandomWalk next ≤
      ENNReal.ofReal K * simpleRandomWalk (thresholdReachStage m k) :=
    transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
      t m k (thresholdReachStage m k) next (ENNReal.ofReal K)
      (measurableSet_thresholdReachStage m k) data.measurable_next
      (fun _ hs ↦ hs) data.next_subset_stage ENNReal.ofReal_ne_top spec
  have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (thresholdReachStage m k))
  have hmeasure : simpleRandomWalk next ≤ ENNReal.ofReal K := by
    calc
      simpleRandomWalk next ≤
          ENNReal.ofReal K * simpleRandomWalk (thresholdReachStage m k) :=
        htransition
      _ ≤ ENNReal.ofReal K * 1 := by gcongr
      _ = ENNReal.ofReal K := mul_one _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa only [Measure.real, ENNReal.toReal_ofReal data.tail.cost_nonneg]
    using hreal

/-- Countable valid stopped traces preserve the aggregate pair-moment cost. -/
theorem simpleRandomWalk_real_base_le_of_pairMomentTilingProduct
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut bound : ℕ} {K : ℝ}
    (data : TilingFixedCutPairMomentBaseProductData
      t m k next cut bound K) :
    simpleRandomWalk.real next ≤ K := by
  let spec :=
    tilingStoppedCoordinateProductSpecOfFixedCutPairMomentTail data.tail
  have htransition : simpleRandomWalk next ≤
      ENNReal.ofReal K * simpleRandomWalk (thresholdReachStage m k) :=
    transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
      t m k (thresholdReachStage m k) next (ENNReal.ofReal K)
      (measurableSet_thresholdReachStage m k) data.measurable_next
      (fun _ hs ↦ hs) data.next_subset_stage ENNReal.ofReal_ne_top spec
  have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (thresholdReachStage m k))
  have hmeasure : simpleRandomWalk next ≤ ENNReal.ofReal K := by
    calc
      simpleRandomWalk next ≤
          ENNReal.ofReal K * simpleRandomWalk (thresholdReachStage m k) :=
        htransition
      _ ≤ ENNReal.ofReal K * 1 := by gcongr
      _ = ENNReal.ofReal K := mul_one _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa only [Measure.real, ENNReal.toReal_ofReal data.tail.cost_nonneg]
    using hreal

/-! ## Trace-weighted shell-zero product law -/

/-- The sound shell-zero interface keeps a separate finite-product cost on
each retained external trace and sums that cost against the trace's actual
mass.  This retains the rare-external-trace factor which a uniform
conditional bound would discard. -/
structure TilingWeightedFixedCutPairMomentBaseProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (cut : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  traceCost : ValidFavoriteTilingTraceCode t → ℝ
  traceCost_nonneg : ∀ z, 0 ≤ traceCost z
  totalBound : ValidFavoriteTilingTraceCode t → ℕ
  tail : ∀ z, TilingRandomTotalFixedCutPairMomentTailSpec
    (fun _ : Unit ↦ validFavoriteTilingStagePiece t m k
      (thresholdReachStage m k) z)
    (validFavoriteTilingStagePiece t m k (thresholdReachStage m k) z ∩ next)
    cut (totalBound z) (traceCost z)
  weightedTraceCost_le :
    ∑' z : ValidFavoriteTilingTraceCode t,
      ENNReal.ofReal (traceCost z) *
        simpleRandomWalk
          (validFavoriteTilingStagePiece t m k
            (thresholdReachStage m k) z) ≤ ENNReal.ofReal K
  cost_nonneg : 0 ≤ K

/-- Literal factored form of the trace-weighted law.  Every trace keeps its
own exact pair-moment cost before the external trace masses are summed. -/
structure TilingWeightedFactoredFixedCutPairMomentBaseProductData
    (t : DominoTiling) (m k : ℕ) (next : Set WalkPath)
    (cut : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  traceCost : ValidFavoriteTilingTraceCode t → ℝ
  traceCost_nonneg : ∀ z, 0 ≤ traceCost z
  totalBound : ValidFavoriteTilingTraceCode t → ℕ
  tail : ∀ z, TilingFactoredRandomTotalFixedCutPairMomentTailData
    (fun _ : Unit ↦ validFavoriteTilingStagePiece t m k
      (thresholdReachStage m k) z)
    (validFavoriteTilingStagePiece t m k (thresholdReachStage m k) z ∩ next)
    cut (totalBound z) (traceCost z)
  weightedTraceCost_le :
    ∑' z : ValidFavoriteTilingTraceCode t,
      ENNReal.ofReal (traceCost z) *
        simpleRandomWalk
          (validFavoriteTilingStagePiece t m k
            (thresholdReachStage m k) z) ≤ ENNReal.ofReal K
  cost_nonneg : 0 ≤ K

noncomputable def weightedFixedCutPairMomentBaseProductDataOfFactoredData
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut : ℕ} {K : ℝ}
    (data : TilingWeightedFactoredFixedCutPairMomentBaseProductData
      t m k next cut K) :
    TilingWeightedFixedCutPairMomentBaseProductData t m k next cut K where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  traceCost := data.traceCost
  traceCost_nonneg := data.traceCost_nonneg
  totalBound := data.totalBound
  tail := fun z ↦ fixedCutPairMomentTailSpecOfFactoredData (data.tail z)
  weightedTraceCost_le := data.weightedTraceCost_le
  cost_nonneg := data.cost_nonneg

/-- One trace's exact finite product law, with its own trace-dependent cost. -/
theorem simpleRandomWalk_validTrace_inter_le
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut : ℕ} {K : ℝ}
    (data : TilingWeightedFixedCutPairMomentBaseProductData
      t m k next cut K)
    (z : ValidFavoriteTilingTraceCode t) :
    simpleRandomWalk
        (validFavoriteTilingStagePiece t m k (thresholdReachStage m k) z ∩
          next) ≤
      ENNReal.ofReal (data.traceCost z) *
        simpleRandomWalk
          (validFavoriteTilingStagePiece t m k
            (thresholdReachStage m k) z) := by
  let piece := validFavoriteTilingStagePiece t m k
    (thresholdReachStage m k) z
  let target := piece ∩ next
  let spec :=
    tilingStoppedCoordinateProductSpecOfFixedCutPairMomentTail (data.tail z)
  let screen : @TraceCappedProductScreening Unit inferInstance
      piece target (ENNReal.ofReal (data.traceCost z)) :=
    { piece := fun _ ↦ piece
      measurable_piece := fun _ ↦
        measurableSet_validFavoriteTilingStagePiece t m k
          (measurableSet_thresholdReachStage m k) z
      disjoint_piece := by
        intro a b hab
        cases a
        cases b
        exact (hab rfl).elim
      union_piece := by
        ext s
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨u, hs⟩
          exact hs
        · intro hs
          exact ⟨(), hs⟩
      next_subset_stage := inter_subset_left
      certificate :=
        cappedProductScreenCertificateOfTilingStoppedCoordinateProductSpec spec }
  exact @transition_measure_le_of_traceCappedProductScreening Unit
    inferInstance piece target
    ((measurableSet_validFavoriteTilingStagePiece t m k
      (measurableSet_thresholdReachStage m k) z).inter data.measurable_next)
    (ENNReal.ofReal (data.traceCost z)) ENNReal.ofReal_ne_top screen

/-- Sum trace-dependent product costs against their actual external trace
masses.  The invalid `Option.none` support is removed only through its proved
simple-random-walk nullity. -/
theorem simpleRandomWalk_real_base_le_of_weightedPairMomentTilingProduct
    {t : DominoTiling} {m k : ℕ} {next : Set WalkPath}
    {cut : ℕ} {K : ℝ}
    (data : TilingWeightedFixedCutPairMomentBaseProductData
      t m k next cut K) :
    simpleRandomWalk.real next ≤ K := by
  let piece : ValidFavoriteTilingTraceCode t → Set WalkPath :=
    fun z ↦ validFavoriteTilingStagePiece t m k
      (thresholdReachStage m k) z
  have hunion : next ∩ validStepWalk = ⋃ z, piece z ∩ next := by
    rw [← iUnion_inter]
    rw [iUnion_validFavoriteTilingStagePiece t m k
      (fun _ hs ↦ hs)]
    ext s
    simp only [Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨⟨data.next_subset_stage hs.1, hs.2⟩, hs.1⟩
    · intro hs
      exact ⟨hs.2, hs.1.2⟩
  have hmeasure : simpleRandomWalk next ≤ ENNReal.ofReal K := by
    calc
      simpleRandomWalk next = simpleRandomWalk (next ∩ validStepWalk) :=
        (simpleRandomWalk_inter_validStepWalk next data.measurable_next).symm
      _ = simpleRandomWalk (⋃ z, piece z ∩ next) := congrArg _ hunion
      _ ≤ ∑' z, simpleRandomWalk (piece z ∩ next) := measure_iUnion_le _
      _ ≤ ∑' z, ENNReal.ofReal (data.traceCost z) *
          simpleRandomWalk (piece z) :=
        ENNReal.tsum_le_tsum fun z ↦
          simpleRandomWalk_validTrace_inter_le data z
      _ ≤ ENNReal.ofReal K := data.weightedTraceCost_le
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa only [Measure.real, ENNReal.toReal_ofReal data.cost_nonneg] using hreal

/-! ## Product-screened shell recurrence -/

/-- Existing adjacent-interface product data together with a literal
fixed-cut product screen for the initial shell overflow. -/
structure AllSixBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixBandProductData t m cutoff band
  baseCost : ℝ
  baseBound : ℕ
  base : TilingFixedCutBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) baseBound baseCost

/-- Literal factored all-six data for both the fixed-cut initial shell and
all adjacent interfaces. -/
structure AllSixFactoredBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixFactoredBandProductData t m cutoff band
  baseCost : ℝ
  baseBound : ℕ
  base : TilingFactoredFixedCutBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) baseBound baseCost

/-- Insert exact capped marginalization into the whole sharp all-six band
package. -/
noncomputable def allSixBaseProductBandDataOfFactoredData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixFactoredBaseProductBandData t m cutoff band) :
    AllSixBaseProductBandData t m cutoff band where
  interfaces := allSixBandProductDataOfFactoredData data.interfaces
  baseCost := data.baseCost
  baseBound := data.baseBound
  base := tilingFixedCutBaseProductDataOfFactoredData data.base

/-- The sharp specialization fixes the first-shell cost to the explicit
summable logarithmic envelope.  Thus neither a base probability estimate nor
an arbitrary base coefficient is exposed to downstream users. -/
structure AllSixSharpBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixBandProductData t m cutoff band
  baseBound : ℕ
  base : TilingFixedCutBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) baseBound (sharpBaseProductCost m)

/-- Forget only that the base coefficient has been fixed to the sharp
summable value. -/
noncomputable def baseProductBandDataOfSharpData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSharpBaseProductBandData t m cutoff band) :
    AllSixBaseProductBandData t m cutoff band where
  interfaces := data.interfaces
  baseCost := sharpBaseProductCost m
  baseBound := data.baseBound
  base := data.base

/-- Fully literal factored version of the sharp shell-zero package. -/
structure AllSixSharpFactoredBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixFactoredBandProductData t m cutoff band
  baseBound : ℕ
  base : TilingFactoredFixedCutBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) baseBound (sharpBaseProductCost m)

/-- Normalize every literal capped negative-binomial coordinate in the sharp
package. -/
noncomputable def allSixSharpBaseProductBandDataOfFactoredData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSharpFactoredBaseProductBandData t m cutoff band) :
    AllSixSharpBaseProductBandData t m cutoff band where
  interfaces := allSixBandProductDataOfFactoredData data.interfaces
  baseBound := data.baseBound
  base := tilingFixedCutBaseProductDataOfFactoredData data.base

/-- Sharp all-six data using the exact aggregate pair-moment cancellation in
the initial shell. -/
structure AllSixSharpPairMomentBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixBandProductData t m cutoff band
  baseBound : ℕ
  base : TilingFixedCutPairMomentBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) baseBound (sharpBaseProductCost m)

/-- Literal factored version of the sharp aggregate pair-moment package. -/
structure AllSixSharpFactoredPairMomentBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixFactoredBandProductData t m cutoff band
  baseBound : ℕ
  base : TilingFactoredFixedCutPairMomentBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) baseBound (sharpBaseProductCost m)

noncomputable def allSixSharpPairMomentBaseProductBandDataOfFactoredData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSharpFactoredPairMomentBaseProductBandData
      t m cutoff band) :
    AllSixSharpPairMomentBaseProductBandData t m cutoff band where
  interfaces := allSixBandProductDataOfFactoredData data.interfaces
  baseBound := data.baseBound
  base := tilingFixedCutPairMomentBaseProductDataOfFactoredData data.base

/-- Sound sharp shell-zero data: the product cost remains trace-dependent
until it is integrated against the retained external-trace mass. -/
structure AllSixTraceWeightedSharpBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixBandProductData t m cutoff band
  base : TilingWeightedFixedCutPairMomentBaseProductData t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) (sharpBaseProductCost m)

/-- Literal factored form of the trace-weighted sharp all-six package. -/
structure AllSixTraceWeightedSharpFactoredBaseProductBandData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixFactoredBandProductData t m cutoff band
  base : TilingWeightedFactoredFixedCutPairMomentBaseProductData
    t m band.oldRank
    (shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0)
    (initialBudget48 m + 1) (sharpBaseProductCost m)

noncomputable def allSixTraceWeightedSharpBaseProductBandDataOfFactoredData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixTraceWeightedSharpFactoredBaseProductBandData
      t m cutoff band) :
    AllSixTraceWeightedSharpBaseProductBandData t m cutoff band where
  interfaces := allSixBandProductDataOfFactoredData data.interfaces
  base := weightedFixedCutPairMomentBaseProductDataOfFactoredData data.base

/-- The coefficient in which the nonsummable one-point/Tonelli first term is
replaced by the exact stopped-coordinate product cost. -/
noncomputable def tilingBandBaseProductOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixBaseProductBandData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  ENNReal.ofReal
    (data.baseCost +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((data.interfaces.balanceLaw hstart hm j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          data.interfaces.interfaceCost j))

/-- The exact state-dependent band overflow with the initial shell screened
by the same finite all-six stopped product law as the adjacent interfaces. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_baseProductData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (data : AllSixBaseProductBandData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ≤
      tilingBandBaseProductOverflowCoefficient data hstart hm := by
  let occupancy := tilingBandOccupancy t m cutoff band
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  have hbase : simpleRandomWalk.real (shellOverflow occupancy threshold 0) ≤
      data.baseCost := by
    simpa only [occupancy, threshold] using
      simpleRandomWalk_real_base_le_of_tilingProduct data.base
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 * threshold j ≤ threshold (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (initialBudget48 m)
      shellGrowth48 j).le
  let screen := tilingBandInterfaceScreenOfProductData data.interfaces hstart hm
  have htotal :=
    measureReal_totalOverflow_le_of_geometricBalance_and_interfaceProduct
      simpleRandomWalk screen.balanced occupancy threshold shellGrowth48
      (shellCount48 m band.beta) m hstep screen.balanceLaw
      screen.interfaceLaw hbase
  have hreal : simpleRandomWalk.real
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card} ≤
      data.baseCost +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((data.interfaces.balanceLaw hstart hm j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            data.interfaces.interfaceCost j) := by
    apply (measureReal_mono ?_).trans htotal
    rw [tilingRandomClockBandOverflow_eq_dynamic]
    exact dynamicStoppedCandidateOverflow48_subset_totalOverflow
      (tilingRandomClockVisitedSites t m cutoff band)
      (tilingRandomClockExternalLargeEvent t m cutoff band)
      (tilingRandomClockDistinguishedSites t m cutoff band)
      (tilingRandomClockTotalLocalTime m cutoff band) m band.beta
      (hbudget band.beta hbeta)
  rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card})]
  exact ENNReal.ofReal_mono hreal

/-- Totalized sharp coefficient; only the finite prefix before the product
law starts is assigned the trivial value one. -/
noncomputable def allSixBaseProductOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixBaseProductBandData t m cutoff band) : ℝ≥0∞ :=
  if htail : data.interfaces.lawStart ≤ m ∧ 0 < m then
    tilingBandBaseProductOverflowCoefficient data htail.1 htail.2
  else 1

/-- Totalized coefficient for the sharp specialization.  Its initial term is
definitionally `sharpBaseProductCost m`, hence is summable. -/
noncomputable def allSixSharpBaseProductOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSharpBaseProductBandData t m cutoff band) : ℝ≥0∞ :=
  allSixBaseProductOverflowCoefficient (baseProductBandDataOfSharpData data)

/-- Per-band candidate overflow with the summable shell-zero coefficient and
no stopped one-point premise. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_sharpBaseProductData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (data : AllSixSharpBaseProductBandData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ≤
      allSixSharpBaseProductOverflowCoefficient data := by
  rw [allSixSharpBaseProductOverflowCoefficient,
    allSixBaseProductOverflowCoefficient,
    dif_pos ⟨hstart, hm⟩]
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_baseProductData
    hbudget hbeta (baseProductBandDataOfSharpData data) hstart hm

/-- Coefficient for the exact pair-moment variant. -/
noncomputable def tilingBandSharpPairMomentOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSharpPairMomentBaseProductBandData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  ENNReal.ofReal
    (sharpBaseProductCost m +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((data.interfaces.balanceLaw hstart hm j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          data.interfaces.interfaceCost j))

/-- Totalized exact-pair-moment coefficient. -/
noncomputable def allSixSharpPairMomentOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSharpPairMomentBaseProductBandData t m cutoff band) : ℝ≥0∞ :=
  if htail : data.interfaces.lawStart ≤ m ∧ 0 < m then
    tilingBandSharpPairMomentOverflowCoefficient data htail.1 htail.2
  else 1

/-- The strongest shell-zero closure: the first term follows from the exact
weighted pair-total identity in every valid stopped trace. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_sharpPairMomentData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (data : AllSixSharpPairMomentBaseProductBandData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ≤
      allSixSharpPairMomentOverflowCoefficient data := by
  rw [allSixSharpPairMomentOverflowCoefficient,
    dif_pos ⟨hstart, hm⟩]
  let occupancy := tilingBandOccupancy t m cutoff band
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  have hbase : simpleRandomWalk.real (shellOverflow occupancy threshold 0) ≤
      sharpBaseProductCost m := by
    simpa only [occupancy, threshold] using
      simpleRandomWalk_real_base_le_of_pairMomentTilingProduct data.base
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 * threshold j ≤ threshold (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (initialBudget48 m)
      shellGrowth48 j).le
  let screen := tilingBandInterfaceScreenOfProductData data.interfaces hstart hm
  have htotal :=
    measureReal_totalOverflow_le_of_geometricBalance_and_interfaceProduct
      simpleRandomWalk screen.balanced occupancy threshold shellGrowth48
      (shellCount48 m band.beta) m hstep screen.balanceLaw
      screen.interfaceLaw hbase
  have hreal : simpleRandomWalk.real
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card} ≤
      sharpBaseProductCost m +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((data.interfaces.balanceLaw hstart hm j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            data.interfaces.interfaceCost j) := by
    apply (measureReal_mono ?_).trans htotal
    rw [tilingRandomClockBandOverflow_eq_dynamic]
    exact dynamicStoppedCandidateOverflow48_subset_totalOverflow
      (tilingRandomClockVisitedSites t m cutoff band)
      (tilingRandomClockExternalLargeEvent t m cutoff band)
      (tilingRandomClockDistinguishedSites t m cutoff band)
      (tilingRandomClockTotalLocalTime m cutoff band) m band.beta
      (hbudget band.beta hbeta)
  rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card})]
  exact ENNReal.ofReal_mono hreal

/-- Finite union of all-six bands with a product-screened initial shell. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_baseProductData
    (t : DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band, AllSixBaseProductBandData t m (cutoff m) band)
    (hstart : ∀ᶠ m : ℕ in atTop, ∀ band ∈ bands m,
      (data m band).interfaces.lawStart ≤ m) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          allSixBaseProductOverflowCoefficient (data m band) := by
  filter_upwards [eventually_candidateBudgetArithmeticAt, hstart,
      eventually_ge_atTop (1 : ℕ)] with m hbudget hstartM hm
  unfold tilingRandomClockCandidateOverflow candidateOverflow
  refine (Screening.measure_someCandidateBad_le_sum simpleRandomWalk
    (bands m) (fun band ↦
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m (cutoff m) s band).card})).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  rw [allSixBaseProductOverflowCoefficient,
    dif_pos ⟨hstartM band hband, hm⟩]
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_baseProductData
    hbudget (hbeta m band hband) (data m band) (hstartM band hband) hm

end

end Erdos1165.HLOZAllSixBaseProductClosure
