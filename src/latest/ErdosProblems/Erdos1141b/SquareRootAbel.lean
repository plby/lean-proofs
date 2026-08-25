import Mathlib

/-!
# Abel continuation from a square-root bound on partial sums
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace Erdos1141b

private noncomputable def sqrtPrefixTail (f : ℕ → ℂ) (y : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun u ↦ ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, f n) y

private lemma measurable_sqrtPrefixTail (f : ℕ → ℂ) : Measurable (sqrtPrefixTail f) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact (measurable_of_countable (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k)).comp
    Nat.measurable_floor

private lemma norm_sqrtPrefixTail_le (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    (y : ℝ) : ‖sqrtPrefixTail f y‖ ≤ C * Real.sqrt y := by
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [sqrtPrefixTail, indicator_of_mem hy]
    exact (hprefix ⌊y⌋₊).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.floor_le (zero_lt_one.trans hy).le)) hC)
  · rw [sqrtPrefixTail, indicator_of_notMem hy, norm_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg y)

private lemma locallyIntegrable_sqrtPrefixTail (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ)) :
    LocallyIntegrableOn (sqrtPrefixTail f) (Ioi 0) := by
  have hcont : Continuous (fun y : ℝ ↦ ((C * Real.sqrt y : ℝ) : ℂ)) := by fun_prop
  refine (hcont.locallyIntegrable.locallyIntegrableOn (Ioi 0)).mono
    (measurable_sqrtPrefixTail f).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.sqrt_nonneg y))]
  exact norm_sqrtPrefixTail_le f C hC hprefix y

private lemma sqrtPrefixTail_isBigO_atTop (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ)) :
    sqrtPrefixTail f =O[atTop] (fun y : ℝ ↦ y ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)] using
    norm_sqrtPrefixTail_le f C hC hprefix y

private lemma sqrtPrefixTail_isBigO_nhdsGT_zero (f : ℕ → ℂ) (b : ℝ) :
    sqrtPrefixTail f =O[𝓝[>] 0] (fun y : ℝ ↦ y ^ (-b)) := by
  have hlt : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with y hy
  simp [sqrtPrefixTail, not_lt.mpr hy.le]

private lemma differentiableAt_sqrtPrefixMellin_neg (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun w ↦ mellin (sqrtPrefixTail f) (-w)) s := by
  have hm : DifferentiableAt ℂ (mellin (sqrtPrefixTail f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := -(1 / 2)) (b := (-s).re - 1)
      (locallyIntegrable_sqrtPrefixTail f C hC hprefix) ?_ ?_
      (sqrtPrefixTail_isBigO_nhdsGT_zero f ((-s).re - 1)) ?_
    · simpa only [neg_neg] using sqrtPrefixTail_isBigO_atTop f C hC hprefix
    · simp only [neg_re]; linarith
    · linarith
  exact hm.comp s differentiableAt_id.neg

private lemma sqrtPrefixMellin_neg_eq_integral (f : ℕ → ℂ) (s : ℂ) :
    mellin (sqrtPrefixTail f) (-s) =
      ∫ y in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, f k) * (y : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ in Ioi 0, (y : ℂ) ^ (-s - 1) * sqrtPrefixTail f y) =
        ∫ y : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun u ↦ (u : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, f k) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · simp [sqrtPrefixTail, hy]
      · simp [sqrtPrefixTail, hy]
    _ = ∫ y : ℝ in Ioi 0 ∩ Ioi 1,
        (y : ℂ) ^ (-s - 1) * (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, f k) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ y : ℝ in Ioi 1,
        (y : ℂ) ^ (-s - 1) * (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, f k) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = _ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

/-- Analytic uniqueness continues the Abel integral to `Re(s) > 1/2`. -/
theorem eq_abelIntegral_of_sqrt_prefix (f : ℕ → ℂ) (F : ℂ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    (hF : Differentiable ℂ F)
    (hsummable : ∀ s : ℂ, 1 < s.re → LSeriesSummable f s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries f s)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    F s = s * ∫ y in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, f k) * (y : ℂ) ^ (-(s + 1)) := by
  have hbigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n ↦ ?_⟩
    simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      using hprefix n
  let U : Set ℂ := {w | 1 / 2 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hLeft : AnalyticOnNhd ℂ F U := hF.differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd ℂ (fun w ↦ w * mellin (sqrtPrefixTail f) (-w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) hUOpen
    exact (differentiableAt_id.mul
      (differentiableAt_sqrtPrefixMellin_neg f C hC hprefix hw)).differentiableWithinAt
  have hEq : EqOn F (fun w ↦ w * mellin (sqrtPrefixTail f) (-w)) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : ℂ) ∈ U by norm_num [U]) ?_
    refine eventually_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro w hw
    change 1 < w.re at hw
    change F w = w * mellin (sqrtPrefixTail f) (-w)
    rw [heq w hw, sqrtPrefixMellin_neg_eq_integral]
    exact LSeries_eq_mul_integral f (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : 1 / 2 < w.re) (hsummable w hw) hbigO
  rw [hEq hs]
  change s * mellin (sqrtPrefixTail f) (-s) = _
  rw [sqrtPrefixMellin_neg_eq_integral]

end Erdos1141b
