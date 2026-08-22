/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZValidStoppedLazyClosure
import ErdosProblems.Erdos1165.TilingTypedFavoriteFactorization

/-!
# Literal typed valid-support lazy screening

This replaces the abstract all-six lazy coordinate package by the actual
typed retained-trace screening input.  Each stopped-coordinate
factorization is derived by `typedFactoredStoppedCoordinateData`; invalid raw
trace indices are never requested.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZTypedValidStoppedLazyClosure

open HLOZGapBetaNumerics HLOZLazyOverflowClosure
open HLOZTilingGapRandomClockScreen ScreeningInstantiation
open TilingCappedMarginalization TilingStoppedProductDisintegration
open TilingTypedFavoriteFactorization TilingTypedFavoriteTrace
open TilingValidTraceCappedStageAdapter VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- All six lazy screens specified at the typed valid-support layer.  These
are Boolean stopped-coordinate screens and deterministic invariance/product
facts, not transition-probability premises. -/
structure AllSixTypedValidStoppedLazyScreenData
    (t : DominoTiling) (cap : ℕ → ℕ) where
  lawStart : ℕ
  deviation_le : ∀ m, lawStart ≤ m → geometricDeviation m ≤ m
  even : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TypedStoppedStageScreeningData t m (k + 1)
      (thresholdReachStage m (k + 1))
      (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m)
  shifted : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TypedStoppedStageScreeningData t m (k + 1)
      (thresholdReachStage m (k + 1))
      (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m)

/-- The even typed screen yields its literal factored stopped-coordinate
datum. -/
noncomputable def AllSixTypedValidStoppedLazyScreenData.evenFactored
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixTypedValidStoppedLazyScreenData t cap)
    (m : ℕ) (hstart : data.lawStart ≤ m) (hm : 0 < m) (k : Fin 3) :
    TilingFactoredStoppedCoordinateData
      (typedFavoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m) :=
  typedFactoredStoppedCoordinateData t m (k + 1) hm (by omega)
    (thresholdReachStage m (k + 1))
    (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m) ∩
      validStepWalk)
    (stoppedLazyGeometricUpperCost m) (data.even m hstart hm k)

/-- The shifted typed screen yields its literal factored stopped-coordinate
datum. -/
noncomputable def AllSixTypedValidStoppedLazyScreenData.shiftedFactored
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixTypedValidStoppedLazyScreenData t cap)
    (m : ℕ) (hstart : data.lawStart ≤ m) (hm : 0 < m) (k : Fin 3) :
    TilingFactoredStoppedCoordinateData
      (typedFavoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m) ∩
        validStepWalk)
      (stoppedLazyGeometricUpperCost m) :=
  typedFactoredStoppedCoordinateData t m (k + 1) hm (by omega)
    (thresholdReachStage m (k + 1))
    (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m) ∩
      validStepWalk)
    (stoppedLazyGeometricUpperCost m) (data.shifted m hstart hm k)

/-- A typed valid-support lazy screen bounds the unrestricted lazy event;
the noncanonical complement is null under simple random walk. -/
theorem simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_of_typedScreen
    {t : DominoTiling} {o : LazyDecomposition.Orientation}
    {m k cap : ℕ} (hm : 0 < m) (hk : 0 < k)
    (screen : TypedStoppedStageScreeningData t m k
      (thresholdReachStage m k)
      (tilingStoppedLazyOverflowEvent t o m k cap ∩ validStepWalk)
      (stoppedLazyGeometricUpperCost m)) :
    simpleRandomWalk (tilingStoppedLazyOverflowEvent t o m k cap) ≤
      stoppedLazyGeometricUpperCost m := by
  let factored := typedFactoredStoppedCoordinateData t m k hm hk
    (thresholdReachStage m k)
    (tilingStoppedLazyOverflowEvent t o m k cap ∩ validStepWalk)
    (stoppedLazyGeometricUpperCost m) screen
  let spec := tilingStoppedCoordinateProductSpecOfFactoredData factored
  have hbound :=
    transition_measure_le_of_typedFavoriteTilingStoppedCoordinateSpec
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

/-- Totalized literal typed lazy cost. -/
noncomputable def allSixTypedValidStoppedLazyOverflowCost
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixTypedValidStoppedLazyScreenData t cap) (m : ℕ) : ℝ≥0∞ :=
  if data.lawStart ≤ m ∧ 0 < m then
    (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m
  else 1

/-- The all-six lazy exceptional event is bounded using six derived typed
stopped-coordinate product laws. -/
theorem simpleRandomWalk_tilingLazyOverflowExceptionalEvent_le_of_typedScreens
    {t : DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixTypedValidStoppedLazyScreenData t cap) {m : ℕ}
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap m)) ≤
      allSixTypedValidStoppedLazyOverflowCost data m := by
  rw [allSixTypedValidStoppedLazyOverflowCost, if_pos ⟨hstart, hm⟩]
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
      · exact simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_of_typedScreen
          hm (by omega) (data.even m hstart hm k)
      · exact simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_of_typedScreen
          hm (by omega) (data.shifted m hstart hm k)
    _ = (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m := by
      simp
      ring

end

end Erdos1165.HLOZTypedValidStoppedLazyClosure
