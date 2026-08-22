/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure

/-!
# Exact all-six product endgame for the low HLOZ gaps

This file combines the state-dependent all-six candidate screen with the
matching all-six stopped lazy screen.  Both probability estimates are
derived from literal capped coordinate-product specifications.  The only
remaining quantitative input is a bound on the displayed finite sum of
product coefficients; in particular, no premise is a probability bound for
the candidate or lazy exceptional event.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZAllSixLowGapProductEndgame

open HLOZAllSixBandProductClosure HLOZTilingGapRandomClockClosure
open HLOZTilingGapRandomClockScreen HLOZGapRandomClockScreen
open HLOZGapBetaArithmetic HLOZGapBetaNumerics HLOZGapEstimate
open HLOZPathEvents HLOZProposition48Candidates
open HLOZLazyOverflowClosure HLOZStoppedLazyLawClosure
open ScreeningInstantiation ExternalProposition44
open TilingStoppedProductDisintegration TilingVariableStoppedTracePartition
open HLOZTraceCappedProductScreening
open VariableStoppedTracePartition

noncomputable section

/-! ## The exact all-six stopped lazy product family -/

/-- Literal capped-product data for all six stopped lazy events associated
with one state-dependent tiling.  The positive level and tail-start
hypotheses are explicit. -/
structure AllSixStoppedLazyProductData
    (t : TilingLazyDecomposition.DominoTiling) (cap : ℕ → ℕ) where
  lawStart : ℕ
  deviation_le : ∀ m, lawStart ≤ m → geometricDeviation m ≤ m
  evenSpec : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .even m (k + 1) (cap m))
      (stoppedLazyGeometricUpperCost m)
  shiftedSpec : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m (k + 1)
        (thresholdReachStage m (k + 1)))
      (tilingStoppedLazyOverflowEvent t .shifted m (k + 1) (cap m))
      (stoppedLazyGeometricUpperCost m)

/-- The capped trace screen obtained from one literal all-six coordinate
specification. -/
def tilingStoppedLazyTraceScreenOfCoordinateSpec
    {t : TilingLazyDecomposition.DominoTiling}
    {o : LazyDecomposition.Orientation} {m k cap : ℕ}
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m k (thresholdReachStage m k))
      (tilingStoppedLazyOverflowEvent t o m k cap)
      (stoppedLazyGeometricUpperCost m)) :
    SomeTraceCappedProductScreening
      (thresholdReachStage m k)
      (tilingStoppedLazyOverflowEvent t o m k cap)
      (stoppedLazyGeometricUpperCost m) :=
  someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m k (thresholdReachStage m k)
    (tilingStoppedLazyOverflowEvent t o m k cap)
    (stoppedLazyGeometricUpperCost m)
    (measurableSet_thresholdReachStage m k) (fun _ hs ↦ hs)
    (tilingStoppedLazyOverflowEvent_subset_thresholdReachStage t o m k cap)
    spec

/-- One literal stopped lazy event is bounded by its checked finite
geometric upper-tail mass. -/
theorem simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_geometricUpper
    {t : TilingLazyDecomposition.DominoTiling}
    {o : LazyDecomposition.Orientation} {m k cap : ℕ}
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m k (thresholdReachStage m k))
      (tilingStoppedLazyOverflowEvent t o m k cap)
      (stoppedLazyGeometricUpperCost m)) :
    simpleRandomWalk (tilingStoppedLazyOverflowEvent t o m k cap) ≤
      stoppedLazyGeometricUpperCost m := by
  let screen := tilingStoppedLazyTraceScreenOfCoordinateSpec spec
  have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (thresholdReachStage m k))
  calc
    simpleRandomWalk (tilingStoppedLazyOverflowEvent t o m k cap) ≤
        stoppedLazyGeometricUpperCost m *
          simpleRandomWalk (thresholdReachStage m k) :=
      @transition_measure_le_of_traceCappedProductScreening
        screen.Index screen.countableIndex
        (thresholdReachStage m k)
        (tilingStoppedLazyOverflowEvent t o m k cap)
        (measurableSet_tilingStoppedLazyOverflowEvent t o m k cap)
        (stoppedLazyGeometricUpperCost m) ENNReal.ofReal_ne_top
        screen.screening
    _ ≤ stoppedLazyGeometricUpperCost m * 1 := by gcongr
    _ = stoppedLazyGeometricUpperCost m := mul_one _

/-- Totalized all-six lazy coefficient.  Below the genuine tail start it is
the trivial bound one; above the start it is exactly six copies of the
one-coordinate geometric upper tail. -/
noncomputable def allSixStoppedLazyOverflowCost
    {t : TilingLazyDecomposition.DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixStoppedLazyProductData t cap) (m : ℕ) : ℝ≥0∞ :=
  if data.lawStart ≤ m ∧ 0 < m then
    (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m
  else 1

/-- The exact six-event union is bounded by the all-six lazy coefficient. -/
theorem simpleRandomWalk_tilingLazyOverflowExceptionalEvent_le
    {t : TilingLazyDecomposition.DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixStoppedLazyProductData t cap) {m : ℕ}
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap m)) ≤
      allSixStoppedLazyOverflowCost data m := by
  rw [allSixStoppedLazyOverflowCost, if_pos ⟨hstart, hm⟩]
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
      · exact simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_geometricUpper
          (data.evenSpec m hstart hm k)
      · exact simpleRandomWalk_tilingStoppedLazyOverflowEvent_le_geometricUpper
          (data.shiftedSpec m hstart hm k)
    _ = (6 : ℝ≥0∞) * stoppedLazyGeometricUpperCost m := by
      simp
      ring

/-- The literal geometric upper-tail mass has the checked moderate-deviation
bound at every positive level in the valid tail. -/
theorem stoppedLazyGeometricUpperCost_le_balanceCost
    {m : ℕ} (hm : 0 < m) (hdeviation : geometricDeviation m ≤ m) :
    stoppedLazyGeometricUpperCost m ≤
      ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) := by
  unfold stoppedLazyGeometricUpperCost
  exact ENNReal.ofReal_mono
    (geometricSum_upper_tail_le_balanceCost hm hm le_rfl hdeviation)

/-- The exact all-six lazy coefficient is eventually smaller than any
prescribed logarithmic-square rate. -/
theorem eventually_allSixStoppedLazyOverflowCost_le_exp
    {t : TilingLazyDecomposition.DominoTiling} {cap : ℕ → ℕ}
    (data : AllSixStoppedLazyProductData t cap) (c : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      allSixStoppedLazyOverflowCost data m ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hpower := eventually_const_mul_log_sq_le_nat_rpow
    (Real.log 6 + c) (1 - 2 * kappaOne) (by norm_num [kappaOne])
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpower, hlog.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop data.lawStart, eventually_ge_atTop (1 : ℕ)] with
      m hpowerM hlogM hstart hm
  rw [allSixStoppedLazyOverflowCost, if_pos ⟨hstart, hm⟩]
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

/-! ## Exact candidate and lazy endgame -/

/-- Full low-gap closure for the genuine state-dependent all-six screen.
The candidate and lazy event probabilities are conclusions.  The remaining
`hproductCost` premise is a bound on explicit finite-product coefficients. -/
theorem hasGapDeficitReturnHarnack_of_allSixStoppedProductData
    {c : ℝ} (hc : 0 < c)
    (cap : TilingLazyDecomposition.DominoTiling → ℕ → ℕ)
    (lazyData : ∀ t, AllSixStoppedLazyProductData t (cap t))
    (bands : TilingLazyDecomposition.DominoTiling →
      ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : TilingLazyDecomposition.DominoTiling →
      Finset (GapScale × ℕ))
    (B : TilingLazyDecomposition.DominoTiling → ℕ)
    (hextract : ∀ t m,
      TilingLazyGoodRandomClockExtraction t
        (onTimeLowGapDeficitExceptionalEvent t m) m
        (levelCutoffTime upperTailDelta m) (cap t m) (bands t m))
    (onePoint : ∀ t m band,
      TilingStoppedExternalOnePointData t m
        (levelCutoffTime upperTailDelta m) band)
    (productData : ∀ t m band,
      AllSixBandProductData t m (levelCutoffTime upperTailDelta m) band)
    (hproductStart : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands t m, (productData t m band).lawStart ≤ m)
    (hproductCost : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands t m,
          allSixBandOverflowCoefficient (productData t m band) ≤
        ENNReal.ofReal
          (Real.exp (-(4 * c) * Real.log (m : ℝ) ^ 2)))
    (hscale : ∀ t p, p ∈ templates t → p.1 ∈ lowGapMesh)
    (hprojects : ∀ t m band, band ∈ bands t m →
      (band.scale, index m band) ∈ templates t)
    (hcard : ∀ t m, (bands t m).card ≤ B t)
    (hbetaLower : ∀ t m band, band ∈ bands t m →
      kappaOne ≤ band.beta)
    (hbetaUpper : ∀ t m band, band ∈ bands t m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index m band + 1))
    (hreturns : ∀ t m band, band ∈ bands t m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index m band)) ≤
        band.returns) :
    HLOZUpperEstimates.HasGapDeficitReturnHarnack c := by
  let lazyCost : TilingLazyDecomposition.DominoTiling → ℕ → ℝ≥0∞ :=
    fun t m ↦ allSixStoppedLazyOverflowCost (lazyData t) m
  let candidateCost : TilingLazyDecomposition.DominoTiling → ℕ → ℝ≥0∞ :=
    fun t m ↦ ∑ band ∈ bands t m,
      allSixBandOverflowCoefficient (productData t m band)
  have hlazy : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap t m)) ≤
        lazyCost t m := by
    intro t
    filter_upwards [eventually_ge_atTop (lazyData t).lawStart,
      eventually_ge_atTop (1 : ℕ)] with m hstart hm
    exact simpleRandomWalk_tilingLazyOverflowExceptionalEvent_le
      (lazyData t) hstart hm
  have hcandidate : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m
            (levelCutoffTime upperTailDelta m) (bands t m)) ≤
        candidateCost t m := by
    intro t
    exact
      eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_productData
        t (fun m ↦ levelCutoffTime upperTailDelta m) (bands t)
        (hbetaLower t) (onePoint t) (productData t) (hproductStart t)
  have hlazyCost : ∀ t, ∀ᶠ m : ℕ in atTop,
      lazyCost t m ≤
        ENNReal.ofReal
          (Real.exp (-(4 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro t
    exact eventually_allSixStoppedLazyOverflowCost_le_exp (lazyData t) (4 * c)
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    2 (c := 2 * c) (by linarith)
  have hother : ∀ t, ∀ᶠ m : ℕ in atTop,
      lazyCost t m + candidateCost t m ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro t
    filter_upwards [hlazyCost t, hproductCost t, habsorb] with
      m hlazyM hproductM habsorbM
    let q : ℝ≥0∞ := ENNReal.ofReal
      (Real.exp (-(4 * c) * Real.log (m : ℝ) ^ 2))
    calc
      lazyCost t m + candidateCost t m ≤ q + q :=
        add_le_add hlazyM hproductM
      _ = (2 : ℝ≥0∞) * q := (two_mul q).symm
      _ ≤ ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
        dsimp [q]
        have hfour : -(2 * (2 * c)) * Real.log (m : ℝ) ^ 2 =
            -(4 * c) * Real.log (m : ℝ) ^ 2 := by ring
        rw [hfour] at habsorbM
        exact habsorbM
  exact hasGapDeficitReturnHarnack_of_tilingLazyRandomClock_bounds
    hc cap bands index templates B hextract lazyCost candidateCost hlazy
    hcandidate hother hscale hprojects hcard hbetaUpper hreturns

end

end Erdos1165.HLOZAllSixLowGapProductEndgame
