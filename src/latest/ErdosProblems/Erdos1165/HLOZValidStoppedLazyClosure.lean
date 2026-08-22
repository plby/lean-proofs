/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixLowGapProductEndgame
import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.TilingValidTraceCappedStageAdapter

/-!
# Valid-support stopped lazy-overflow closure

The lazy part of the full HLOZ gap screen is partitioned only over genuine
nearest-neighbor traces.  The omitted noncanonical paths have zero
simple-random-walk mass.  Thus no coordinate specification is requested for
the invalid `Option.none` trace piece.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZValidStoppedLazyClosure

open HLOZAllSixLowGapProductEndgame HLOZGapBetaNumerics
open HLOZLazyOverflowClosure
open HLOZTilingGapRandomClockScreen ScreeningInstantiation
open TilingCappedMarginalization TilingStoppedProductDisintegration
open TilingValidTraceCappedStageAdapter
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Exact all-six stopped lazy laws on the canonical walk support. -/
structure AllSixValidStoppedLazyProductData
    (t : DominoTiling) (cap : ℕ → ℕ) where
  lawStart : ℕ
  deviation_le : ∀ m, lawStart ≤ m → geometricDeviation m ≤ m
  evenSpec : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingStoppedCoordinateProductSpec
      (validFavoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m)
  shiftedSpec : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingStoppedCoordinateProductSpec
      (validFavoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m)

/-- Literal factored form of the valid-support lazy laws.  The coordinate
normalization and distinguished-coordinate marginalization are performed by
the checked capped-marginalization constructor below. -/
structure AllSixValidFactoredStoppedLazyProductData
    (t : DominoTiling) (cap : ℕ → ℕ) where
  lawStart : ℕ
  deviation_le : ∀ m, lawStart ≤ m → geometricDeviation m ≤ m
  even : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingFactoredStoppedCoordinateData
      (validFavoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m)
  shifted : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingFactoredStoppedCoordinateData
      (validFavoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m)

/-- Marginalize the literal factored lazy data into the exact coordinate
specifications consumed by the valid-support measure theorem. -/
noncomputable def allSixValidStoppedLazyProductDataOfFactoredData
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixValidFactoredStoppedLazyProductData t cap) :
    AllSixValidStoppedLazyProductData t cap where
  lawStart := data.lawStart
  deviation_le := data.deviation_le
  evenSpec m hstart hm k :=
    tilingStoppedCoordinateProductSpecOfFactoredData
      (data.even m hstart hm k)
  shiftedSpec m hstart hm k :=
    tilingStoppedCoordinateProductSpecOfFactoredData
      (data.shifted m hstart hm k)

/-- One valid-support stopped lazy law bounds the original, unrestricted
event.  Nullity of `validStepWalkᶜ` is discharged by the generic valid-trace
adapter. -/
theorem simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_geometricUpper
    {t : DominoTiling} {o : LazyDecomposition.Orientation}
    {m k cap : ℕ}
    (spec : TilingStoppedCoordinateProductSpec
      (validFavoriteTilingStagePiece t m k (thresholdReachStage m k))
      (tilingStoppedLazyOverflowEvent t o m k cap ∩ validStepWalk)
      (stoppedLazyGeometricUpperCost m)) :
    simpleRandomWalk (tilingStoppedLazyOverflowEvent t o m k cap) ≤
      stoppedLazyGeometricUpperCost m := by
  have hbound :=
    transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
      t m k (thresholdReachStage m k)
      (tilingStoppedLazyOverflowEvent t o m k cap)
      (stoppedLazyGeometricUpperCost m)
      (measurableSet_thresholdReachStage m k)
      (measurableSet_tilingStoppedLazyOverflowEvent t o m k cap)
      (fun _ hs ↦ hs)
      (tilingStoppedLazyOverflowEvent_subset_thresholdReachStage
        t o m k cap)
      ENNReal.ofReal_ne_top spec
  have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (thresholdReachStage m k))
  exact hbound.trans (by
    simpa only [mul_one, one_mul, mul_comm] using
      (mul_le_mul_left hstage (stoppedLazyGeometricUpperCost m)))

/-- Totalized six-coordinate lazy cost.  The finite prefix before the exact
laws start receives the trivial probability bound one. -/
noncomputable def allSixValidStoppedLazyOverflowCost
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixValidStoppedLazyProductData t cap) (m : ℕ) : ℝ≥0∞ :=
  if data.lawStart ≤ m ∧ 0 < m then
    (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m
  else 1

/-- The all-six lazy exceptional event is bounded by the valid-support
coordinate laws. -/
theorem simpleRandomWalk_tilingLazyOverflowExceptionalEvent_le
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixValidStoppedLazyProductData t cap) {m : ℕ}
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap m)) ≤
      allSixValidStoppedLazyOverflowCost data m := by
  rw [allSixValidStoppedLazyOverflowCost, if_pos ⟨hstart, hm⟩]
  unfold tilingLazyOverflowExceptionalEvent
  calc
    simpleRandomWalk
        ((⋃ k : Fin 3,
            tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m)) ∪
          ⋃ k : Fin 3,
            tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m)) ≤
        simpleRandomWalk
            (⋃ k : Fin 3,
              tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m)) +
          simpleRandomWalk
            (⋃ k : Fin 3,
              tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m)) :=
      measure_union_le _ _
    _ ≤
        (∑ k : Fin 3,
          simpleRandomWalk
            (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m))) +
        ∑ k : Fin 3,
          simpleRandomWalk
            (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m)) :=
      add_le_add
        (measure_iUnion_fintype_le simpleRandomWalk _)
        (measure_iUnion_fintype_le simpleRandomWalk _)
    _ ≤
        (∑ _k : Fin 3, stoppedLazyGeometricUpperCost m) +
          ∑ _k : Fin 3, stoppedLazyGeometricUpperCost m := by
      gcongr with k
      · exact
          simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_geometricUpper
            (data.evenSpec m hstart hm k)
      · exact
          simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_geometricUpper
            (data.shiftedSpec m hstart hm k)
    _ = (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m := by
      simp
      ring

/-- The exact valid-support lazy coefficient eventually beats every fixed
squared-logarithmic rate. -/
theorem eventually_allSixValidStoppedLazyOverflowCost_le_exp
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixValidStoppedLazyProductData t cap) (c : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      allSixValidStoppedLazyOverflowCost data m ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hpower := eventually_const_mul_log_sq_le_nat_rpow
    (Real.log 6 + c) (1 - 2 * kappaOne) (by norm_num [kappaOne])
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpower, hlog.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop data.lawStart, eventually_ge_atTop (1 : ℕ)] with
      m hpowerM hlogM hstart hm
  rw [allSixValidStoppedLazyOverflowCost, if_pos ⟨hstart, hm⟩]
  have htail := stoppedLazyGeometricUpperCost_le_balanceCost hm
    (data.deviation_le m hstart)
  have hmul := mul_le_mul_left htail (6 : ℝ≥0∞)
  have hmul' : (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m ≤
      (6 : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) := by
    simpa [mul_comm] using hmul
  have hlogSq : 1 ≤ Real.log (m : ℝ) ^ 2 := by nlinarith
  have htarget : Real.log (6 : ℝ) + c * Real.log (m : ℝ) ^ 2 ≤
      (Real.log 6 + c) * Real.log (m : ℝ) ^ 2 := by
    have hlog6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hdominates : Real.log (6 : ℝ) +
      c * Real.log (m : ℝ) ^ 2 ≤ 17 * balanceRateScale m := by
    calc
      Real.log (6 : ℝ) + c * Real.log (m : ℝ) ^ 2 ≤
          (Real.log 6 + c) * Real.log (m : ℝ) ^ 2 := htarget
      _ ≤ (m : ℝ) ^ (1 - 2 * kappaOne) := hpowerM
      _ = balanceRateScale m := rfl
      _ ≤ 17 * balanceRateScale m := by
        have := balanceRateScale_nonneg m
        nlinarith
  have hgap : (6 : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) ≤
      ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
    have hgap' := Gap.ennreal_nat_mul_exp_neg_le_exp_neg
      (J := 6) (exponent := 17 * balanceRateScale m)
      (target := c * Real.log (m : ℝ) ^ 2) (by norm_num) hdominates
    have hexponent : -(17 * balanceRateScale m) =
        -17 * balanceRateScale m := by ring
    have htarget' : -(c * Real.log (m : ℝ) ^ 2) =
        -c * Real.log (m : ℝ) ^ 2 := by ring
    rw [hexponent, htarget'] at hgap'
    exact hgap'
  exact hmul'.trans hgap

end

end Erdos1165.HLOZValidStoppedLazyClosure
