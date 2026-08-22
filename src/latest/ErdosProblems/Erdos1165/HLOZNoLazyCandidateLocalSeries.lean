/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFullBetaProductBranch
import ErdosProblems.Erdos1165.HLOZNoLazyCandidateRankSplit
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# Candidate-local product series from the exact overflow series

This module closes the numerical beta-band coefficient tail for the no-lazy
candidate-local screen.  The only downstream input is summability of the
literal overflow intersection produced by that screen.  No shell carrier,
Harnack package, global lazy event, or numerical-tail premise appears.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZNoLazyCandidateLocalSeries

open HLOZFullBetaProductBranch HLOZFullBetaRegimeSplit
open HLOZGapRandomClockScreen HLOZNoLazyCandidateRankSplit
open HLOZNoLazyFullBetaProductBranch HLOZPathEvents
open HLOZProposition48Candidates HLOZTilingGapRandomClockScreen
open HLOZUpperEstimates

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The coefficient term in the candidate-local endpoint screen. -/
def candidateLocalGeometricCost
    (cap externalThreshold : ℕ → ℕ) (m : ℕ) : ℝ≥0∞ :=
  ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
    (candidateBudget48 m band.beta : ℝ≥0∞) *
      Gap.geometricReturnCost
        (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
        band.returns

private theorem candidateLocalGeometricCost_ne_top
    (cap externalThreshold : ℕ → ℕ) (m : ℕ) :
    candidateLocalGeometricCost cap externalThreshold m ≠ ∞ := by
  unfold candidateLocalGeometricCost Gap.geometricReturnCost
  simp only [ENNReal.sum_ne_top]
  intro band _hband
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

private theorem ennreal_series_ne_top_of_eventually_exp_neg_log_sq_bound
    (f : ℕ → ℝ≥0∞) (hfinite : ∀ m, f m ≠ ∞)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ m : ℕ in atTop,
      f m ≤ ENNReal.ofReal
        (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    ∑' m, f m ≠ ∞ := by
  let g : ℕ → ℝ≥0 := fun m ↦ (f m).toNNReal
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hg : Summable (fun m : ℕ ↦ (g m : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hpoly
    have hbound' : ∀ᶠ m : ℕ in cofinite,
        f m ≤ ENNReal.ofReal
          (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
      simpa only [Nat.cofinite_eq_atTop] using hbound
    have hlarge : ∀ᶠ m : ℕ in cofinite,
        2 / c ≤ Real.log (m : ℝ) := by
      simpa only [Nat.cofinite_eq_atTop] using
        hlog.eventually (eventually_ge_atTop (2 / c))
    have hmpos : ∀ᶠ m : ℕ in cofinite, 0 < m := by
      simpa only [Nat.cofinite_eq_atTop] using (eventually_gt_atTop 0)
    filter_upwards [hbound', hlarge, hmpos] with m hm hlogm hmpos
    have hmReal : (f m).toReal ≤
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      rw [← ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    have hexponent : -c * Real.log (m : ℝ) ^ 2 ≤
        Real.log (m : ℝ) * (-2) := by
      have hcMul : 2 ≤ c * Real.log (m : ℝ) := by
        calc
          2 = c * (2 / c) := by field_simp
          _ ≤ c * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlogm hc.le
      nlinarith
    have hexp : Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
        (m : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hmpos)]
      exact Real.exp_le_exp.mpr hexponent
    simpa [g, ENNReal.toReal, Real.norm_eq_abs, abs_of_nonneg] using
      hmReal.trans hexp
  have hcoe : ∀ m, (g m : ℝ≥0∞) = f m := by
    intro m
    exact ENNReal.coe_toNNReal (hfinite m)
  rw [← tsum_congr hcoe]
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hg

/-- The explicit finite beta-band geometric contribution is summable for
arbitrary level-dependent cap and external-threshold functions. -/
theorem candidateLocalGeometricCost_series_ne_top
    (cap externalThreshold : ℕ → ℕ) :
    ∑' m, candidateLocalGeometricCost cap externalThreshold m ≠ ∞ := by
  apply ennreal_series_ne_top_of_eventually_exp_neg_log_sq_bound
    (candidateLocalGeometricCost cap externalThreshold)
    (candidateLocalGeometricCost_ne_top cap externalThreshold)
    (by norm_num : (0 : ℝ) < 1)
  simpa only [candidateLocalGeometricCost] using
    (eventually_sourceProductEndpoint_geometric_sum_le
      cap externalThreshold (c := 1) (by norm_num))

/-- Finite levels before both the product extraction and the literal external
threshold are available. -/
def candidateLocalScreenPrefixEvent
    (externalThreshold : ℕ → ℕ) (m : ℕ) : Set WalkPath :=
  if 1 < m ∧ 0 < externalThreshold m then ∅ else Set.univ

theorem eventually_candidateLocalScreenPrefixEvent_eq_empty
    (externalThreshold : ℕ → ℕ)
    (hthreshold : ∀ᶠ m : ℕ in atTop, 0 < externalThreshold m) :
    ∀ᶠ m : ℕ in atTop,
      candidateLocalScreenPrefixEvent externalThreshold m = ∅ := by
  filter_upwards [eventually_gt_atTop (1 : ℕ), hthreshold] with m hm hpos
  rw [candidateLocalScreenPrefixEvent, if_pos ⟨hm, hpos⟩]

theorem simpleRandomWalk_candidateLocalScreenPrefixEvent_series_ne_top
    (externalThreshold : ℕ → ℕ)
    (hthreshold : ∀ᶠ m : ℕ in atTop, 0 < externalThreshold m) :
    ∑' m, simpleRandomWalk
      (candidateLocalScreenPrefixEvent externalThreshold m) ≠ ∞ := by
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk
    (candidateLocalScreenPrefixEvent externalThreshold)
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards
    [eventually_candidateLocalScreenPrefixEvent_eq_empty
      externalThreshold hthreshold] with m hm
  rw [hm]
  simp

/-- Carrier-independent product extraction.  Once the exact overflow
intersection is summable, the finite prefix and coefficient tail are closed
internally. -/
theorem
    simpleRandomWalk_onTimeCandidateLocalProductBeta_series_ne_top_of_overflow
    (t : DominoTiling) (cap externalThreshold : ℕ → ℕ)
    (hthreshold : ∀ᶠ m : ℕ in atTop, 0 < externalThreshold m)
    (hoverflow : ∑' m, simpleRandomWalk
      (candidateLocalProductOverflowEvent t m
        (levelCutoffTime upperTailDelta m) (cap m)
        (externalThreshold m)) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (onTimeCandidateLocalProductBetaLowGapExceptionalEvent
        t m (externalThreshold m)) ≠ ∞ := by
  have hprefix :=
    simpleRandomWalk_candidateLocalScreenPrefixEvent_series_ne_top
      externalThreshold hthreshold
  have hgeometric :=
    candidateLocalGeometricCost_series_ne_top cap externalThreshold
  have hmajor : ∑' m,
      (simpleRandomWalk
          (candidateLocalScreenPrefixEvent externalThreshold m) +
        (simpleRandomWalk
            (candidateLocalProductOverflowEvent t m
              (levelCutoffTime upperTailDelta m) (cap m)
              (externalThreshold m)) +
          candidateLocalGeometricCost cap externalThreshold m)) ≠ ∞ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr
      ⟨hprefix, ENNReal.add_ne_top.mpr ⟨hoverflow, hgeometric⟩⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  by_cases hgood : 1 < m ∧ 0 < externalThreshold m
  · have hscreen :=
      measure_onTimeCandidateLocalProductBetaLowGapExceptionalEvent_le_screen
        t m (cap m) (externalThreshold m) hgood.1 hgood.2
    simpa only [candidateLocalScreenPrefixEvent, if_pos hgood,
      measure_empty, zero_add, candidateLocalProductOverflowEvent,
      candidateLocalGeometricCost] using hscreen
  · calc
      simpleRandomWalk
          (onTimeCandidateLocalProductBetaLowGapExceptionalEvent
            t m (externalThreshold m)) ≤
          simpleRandomWalk Set.univ := measure_mono (subset_univ _)
      _ ≤ simpleRandomWalk Set.univ +
          (simpleRandomWalk
              (candidateLocalProductOverflowEvent t m
                (levelCutoffTime upperTailDelta m) (cap m)
                (externalThreshold m)) +
            candidateLocalGeometricCost cap externalThreshold m) :=
        le_add_right le_rfl
      _ = simpleRandomWalk
            (candidateLocalScreenPrefixEvent externalThreshold m) +
          (simpleRandomWalk
              (candidateLocalProductOverflowEvent t m
                (levelCutoffTime upperTailDelta m) (cap m)
                (externalThreshold m)) +
            candidateLocalGeometricCost cap externalThreshold m) := by
        rw [candidateLocalScreenPrefixEvent, if_neg hgood]

end

end Erdos1165.HLOZNoLazyCandidateLocalSeries
