/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSingletonHistoryProduct

/-!
# Source-scale singleton Theta product

The deterministic HLOZ scale inequalities instantiate every arithmetic field
of the singleton source-history product.  Since the exposed support is a
singleton, both the high-coordinate and low-coordinate contributions have
multiplicity at most one.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaSingletonScaleProduct

open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaProduct
open HLOZSourceOrientedThetaSingletonHistoryProduct
open HLOZSourceOrientedThetaSourceSelectedCarrier
open LazyDecomposition
open ScreeningInstantiation
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Uniform cost of one complete singleton source-slot history. -/
def singletonSourceThetaRatio (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 *
    (Real.exp (-17 * balanceRateScale m) +
      Real.exp (-17 * thetaLowRateScale m)))

theorem externalSourceSelectedArithmetic_of_scale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (cap : ℕ)
    (scale : OrientedThetaScaleArithmetic m) :
    ExternalThetaProductArithmetic
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m))
      (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) cap := by
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data
    (shellWidth48 m) (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
  refine
    { level_pos := scale.level_pos
      width := scale.width
      width_eq := rfl
      externalLow_eq := rfl
      externalHigh_eq := rfl
      geometric := scale.geometric
      theta := scale.theta
      thick_nonneg := scale.thick_nonneg
      low_dom := scale.low_dom
      upper_le_cap := ?_
      mean := ?_
      window_upper := ?_
      window_cap := ?_ }
  · intro b
    dsimp only [sourceData, withExternalSourceSelected, data, concreteFiber]
    omega
  · intro b
    have hcard := card_tilingCoordinatesAt_le_retainedCount_succ t
      eta.1.1.start eta.1.1.retained b.1
    dsimp only [sourceData, withExternalSourceSelected, data, concreteFiber]
      at hcard ⊢
    omega
  · intro b v hv
    have hv' := lazy_le_total_upper_of_mem_thetaFailureWindow hv
    dsimp only [sourceData, withExternalSourceSelected, data, concreteFiber]
    omega
  · intro b v hv
    have hv' := lazy_le_total_upper_of_mem_thetaFailureWindow hv
    dsimp only [sourceData, withExternalSourceSelected, data, concreteFiber]
    omega

theorem externalSourceSelected_cost_le_singletonRatio
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (history : SingletonSourceHistory t o m k supportAt) (cap : ℕ) :
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData history.eta)
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m)) cap c) ≤
      singletonSourceThetaRatio m := by
  let sourceData := withExternalSourceSelected
    (concreteFiber o m k supportAt supportData history.eta)
      (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m)
  have hhigh : (externalThetaHighCoordinates sourceData cap).card ≤ 1 := by
    calc
      (externalThetaHighCoordinates sourceData cap).card ≤
          Fintype.card (TilingAwayDomino t history.eta.1.1.start
            history.eta.1.1.retained
            (supportComplementDistinguished t history.eta.1.1.start
              history.eta.1.1.retained history.eta.1.2)) :=
        Finset.card_le_univ _
      _ = history.eta.1.2.card := by
        rw [Fintype.card_congr (supportAwayEquiv t history.eta.1.1.start
          history.eta.1.1.retained history.eta.1.2
          sourceData.support_represented)]
        exact Fintype.card_coe history.eta.1.2
      _ = 1 := by rw [history.support_singleton]; simp
  have hsum := sum_externalThetaCost_le sourceData cap
  have hreal :
      2 * ∑ c, externalThetaCost sourceData cap c ≤
        2 * (Real.exp (-17 * balanceRateScale m) +
          Real.exp (-17 * thetaLowRateScale m)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      (∑ c, externalThetaCost sourceData cap c) ≤
          ((externalThetaHighCoordinates sourceData cap).card : ℝ) *
              Real.exp (-17 * balanceRateScale m) +
            (history.eta.1.2.card : ℝ) *
              Real.exp (-17 * thetaLowRateScale m) := hsum
      _ ≤ 1 * Real.exp (-17 * balanceRateScale m) +
            1 * Real.exp (-17 * thetaLowRateScale m) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hhigh
          · exact (Real.exp_pos _).le
        · rw [history.support_singleton]
          simp
      _ = _ := by ring
  exact ENNReal.ofReal_le_ofReal hreal

/-- Premise-free arithmetic constructor.  Its only inputs describe the
deterministic retained-word support selector. -/
noncomputable def singletonSourceThetaProductDataOfScale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (scale : OrientedThetaScaleArithmetic m) :
    SingletonSourceThetaProductData t o m k supportAt supportData
      (shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m) (singletonSourceThetaRatio m) where
  supportOfCode := supportOfCode
  support_code := support_code
  arithmetic := fun history cap ↦
    externalSourceSelectedArithmetic_of_scale supportData history.eta cap scale
  cost_le := fun history cap ↦
    externalSourceSelected_cost_le_singletonRatio supportData history cap

theorem simpleRandomWalk_singletonSourceThetaProductMajorant_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (hm : 1 < m) (hk : 0 < k) (scale : OrientedThetaScaleArithmetic m) :
    simpleRandomWalk (singletonSourceThetaProductMajorant t o m k supportAt
      supportData (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m)) ≤
      3 * singletonSourceThetaRatio m :=
  (singletonSourceThetaProductDataOfScale supportData supportOfCode
    support_code scale).measure_majorant_le hm hk

end

end Erdos1165.HLOZSourceOrientedThetaSingletonScaleProduct
