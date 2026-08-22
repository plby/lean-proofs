/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZLazyOverflowClosure
import ErdosProblems.Erdos1165.HLOZGapBetaNumerics

/-!
# Concrete stopped lazy laws from all-six variable-time product fibres

The sole spatial datum in this file is a family of
`TilingStoppedCoordinateProductSpec`s.  Each such specification contains
exact capped stopped-cylinder masses and an equality of finite coordinate
products.  It contains neither a physical creation time nor the target path
probability inequality.

The constructor first turns these data into literal trace certificates and
then into the six `GeometricBalanceLaw`s required by the lazy split.  The
remaining estimate is numerical: their budgets are all one, so the full cost
is twelve copies of `exp (-17 * balanceRateScale m)`, which is eventually
smaller than `exp (-c * log(m)^2)`.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZStoppedLazyLawClosure

open HLOZLazyOverflow HLOZLazyOverflowClosure HLOZGapBetaNumerics
open HLOZPathEvents ScreeningInstantiation LazyDecomposition
open TilingStoppedProductDisintegration TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

/-- The one remaining all-six input.  The finite prefix before `lawStart` is
irrelevant to every eventual statement and is bounded by one in
`stoppedLazyOverflowCost`. -/
structure StoppedLazyTilingProductFamily (cap : ℕ → ℕ) where
  lawStart : ℕ
  deviation_le : ∀ m, lawStart ≤ m →
    geometricDeviation m ≤ m
  tiling : Orientation → Fin 3 → TilingLazyDecomposition.DominoTiling
  evenSpec : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece (tiling .even k) m (k + 1)
        (thresholdReachStage m (k + 1)))
      (stoppedLazyOverflowEvent .even m (k + 1) (cap m))
      (stoppedLazyGeometricUpperCost m)
  shiftedSpec : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece (tiling .shifted k) m (k + 1)
        (thresholdReachStage m (k + 1)))
      (stoppedLazyOverflowEvent .shifted m (k + 1) (cap m))
      (stoppedLazyGeometricUpperCost m)

/-- Construct all six actual stopped lazy balance laws. -/
def stoppedLazyLawFamilyOfTilingProductFamily
    {cap : ℕ → ℕ} (data : StoppedLazyTilingProductFamily cap) :
    StoppedLazyLawFamily cap where
  lawStart := data.lawStart
  evenLaw m hstart hm k :=
    stoppedLazyBalanceLawOfTraceScreen hm (data.deviation_le m hstart)
      (stoppedLazyTraceScreenOfTilingCoordinateSpec
        (data.tiling .even k) .even m (k + 1) (cap m)
        (data.evenSpec m hstart hm k))
  shiftedLaw m hstart hm k :=
    stoppedLazyBalanceLawOfTraceScreen hm (data.deviation_le m hstart)
      (stoppedLazyTraceScreenOfTilingCoordinateSpec
        (data.tiling .shifted k) .shifted m (k + 1) (cap m)
        (data.shiftedSpec m hstart hm k))

/-- The literal cost of the constructed family is a fixed multiplicity of
the checked one-site moderate-deviation cost. -/
theorem stoppedLazyOverflowCost_of_tilingProductFamily
    {cap : ℕ → ℕ} (data : StoppedLazyTilingProductFamily cap)
    {m : ℕ} (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    stoppedLazyOverflowCost
        (stoppedLazyLawFamilyOfTilingProductFamily data) m =
      (12 : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) := by
  simp [stoppedLazyOverflowCost, hstart, hm, stoppedLazyBalanceCost,
    stoppedLazyLawFamilyOfTilingProductFamily,
    stoppedLazyBalanceLawOfTraceScreen]
  ring

/-- Every product family has the required logarithmic-square lazy-overflow
rate.  This is the requested eventual bound for the literal
`stoppedLazyOverflowCost`, with no additional probability premise. -/
theorem hasStoppedLazyOverflowRate_of_tilingProductFamily
    {cap : ℕ → ℕ} (data : StoppedLazyTilingProductFamily cap)
    (c : ℝ) :
    HasStoppedLazyOverflowRate c
      (stoppedLazyLawFamilyOfTilingProductFamily data) := by
  have hpower := eventually_const_mul_log_sq_le_nat_rpow
    (Real.log 12 + c) (1 - 2 * kappaOne) (by norm_num [kappaOne])
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpower, hlog.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop data.lawStart, eventually_ge_atTop (1 : ℕ)] with
      m hpowerM hlogM hstart hm
  rw [stoppedLazyOverflowCost_of_tilingProductFamily data hstart hm]
  have hlogSq : 1 ≤ Real.log (m : ℝ) ^ 2 := by nlinarith
  have hlog12 : 0 ≤ Real.log (12 : ℝ) := Real.log_nonneg (by norm_num)
  have htarget : Real.log (12 : ℝ) +
      c * Real.log (m : ℝ) ^ 2 ≤
        (Real.log 12 + c) * Real.log (m : ℝ) ^ 2 := by
    nlinarith
  have hscale0 : 0 ≤ balanceRateScale m := balanceRateScale_nonneg m
  have hdominates : Real.log (12 : ℝ) +
      c * Real.log (m : ℝ) ^ 2 ≤ 17 * balanceRateScale m := by
    calc
    Real.log (12 : ℝ) + c * Real.log (m : ℝ) ^ 2 ≤
        (Real.log 12 + c) * Real.log (m : ℝ) ^ 2 := htarget
    _ ≤ (m : ℝ) ^ (1 - 2 * kappaOne) := hpowerM
    _ = balanceRateScale m := rfl
    _ ≤ 17 * balanceRateScale m := by nlinarith
  convert
    (Gap.ennreal_nat_mul_exp_neg_le_exp_neg (J := 12)
      (exponent := 17 * balanceRateScale m)
      (target := c * Real.log (m : ℝ) ^ 2)
      (by norm_num : 0 < 12) hdominates) using 1 <;> norm_num

theorem eventually_simpleRandomWalk_lazyOverflowExceptionalEvent_le_exp_of_tilingProduct
    {cap : ℕ → ℕ} (data : StoppedLazyTilingProductFamily cap)
    (c : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m)) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
  eventually_simpleRandomWalk_lazyOverflowExceptionalEvent_le_exp
    (stoppedLazyLawFamilyOfTilingProductFamily data)
    (hasStoppedLazyOverflowRate_of_tilingProductFamily data c)

end

end Erdos1165.HLOZStoppedLazyLawClosure
