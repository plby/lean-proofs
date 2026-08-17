/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The explicit numerical cutoff in the proof of Erdős Problem 175

This file proves the entirely real-variable calculation used after combining
the lower and upper estimates of Granville--Ramaré.  The key point is that the
endpoint is close, so the proof uses Mathlib's certified ten-decimal estimate
for `Real.log 2`, followed by an exact rational calculation.
-/

namespace Erdos175

open Set

/-- The logarithmic gap obtained after dividing the two exponential-sum
estimates by `x ^ (23 / 48)` and taking logarithms. -/
private noncomputable def cutoffGap (x : ℝ) : ℝ :=
  Real.log x / 48 - Real.log 56 - (11 / 4 : ℝ) * Real.log (Real.log (256 * x))

/-- The exact rational comparison behind the endpoint `2 ^ 1617`.

The rational `1407955211 / 1250000` is `1625 * 0.6931471808`, hence is a
strict upper bound for `1625 * log 2`. -/
private lemma endpoint_rational_power_bound :
    (56 : ℝ) ^ 48 * (1407955211 / 1250000 : ℝ) ^ 132 < (2 : ℝ) ^ 1617 := by
  have hnat :
      56 ^ 48 * 1407955211 ^ 132 < 2 ^ 1617 * 1250000 ^ 132 := by
    rw [show 2 ^ 1617 = (2 ^ 100) ^ 16 * 2 ^ 17 by
      calc
        2 ^ 1617 = 2 ^ (1600 + 17) := by norm_num
        _ = 2 ^ 1600 * 2 ^ 17 := pow_add 2 1600 17
        _ = 2 ^ (100 * 16) * 2 ^ 17 := by norm_num
        _ = (2 ^ 100) ^ 16 * 2 ^ 17 := by rw [pow_mul]]
    norm_num
  rw [div_pow]
  rw [show (56 : ℝ) ^ 48 * ((1407955211 : ℝ) ^ 132 / (1250000 : ℝ) ^ 132) =
    ((56 : ℝ) ^ 48 * (1407955211 : ℝ) ^ 132) / (1250000 : ℝ) ^ 132 by ring]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (1250000 : ℝ) ^ 132)]
  exact_mod_cast hnat

private lemma endpoint_power_bound :
    (56 : ℝ) ^ 48 * (1625 * Real.log 2) ^ 132 < (2 : ℝ) ^ 1617 := by
  have hlog : 1625 * Real.log 2 < (1407955211 / 1250000 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (1625 * Real.log 2) ^ 132 <
      (1407955211 / 1250000 : ℝ) ^ 132 := by
    exact pow_lt_pow_left₀ hlog (by positivity) (by norm_num)
  calc
    (56 : ℝ) ^ 48 * (1625 * Real.log 2) ^ 132 <
        (56 : ℝ) ^ 48 * (1407955211 / 1250000 : ℝ) ^ 132 := by
          exact mul_lt_mul_of_pos_left hpow (by positivity)
    _ < (2 : ℝ) ^ 1617 := endpoint_rational_power_bound

private lemma cutoffGap_endpoint_pos :
    0 < cutoffGap ((2 : ℝ) ^ 1617) := by
  have ht : 0 < 1625 * Real.log 2 := by positivity
  have hp := endpoint_power_bound
  have hp' := Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
    (mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 1617) = 1617 * Real.log 2 :=
    Real.log_pow 2 1617
  have harg : 256 * (2 : ℝ) ^ 1617 = (2 : ℝ) ^ 1625 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 1617) = 1625 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [cutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma cutoffGap_hasDerivAt {x : ℝ} (hxpos : 0 < x)
    (hinnerpos : 0 < Real.log (256 * x)) :
    HasDerivAt cutoffGap
      (x⁻¹ / 48 - (11 / 4 : ℝ) * (256 / (256 * x)) /
        Real.log (256 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ 256 * y) 256 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (256 : ℝ)
  have hloglin : HasDerivAt (fun y : ℝ ↦ Real.log (256 * y))
      (256 / (256 * x)) x := hlin.log (by positivity)
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log (256 * y)))
      ((256 / (256 * x)) / Real.log (256 * x)) x :=
    hloglin.log hinnerpos.ne'
  unfold cutoffGap
  have hfull := (((Real.hasDerivAt_log hxpos.ne').div_const 48).sub_const
    (Real.log 56)).sub ((hasDerivAt_const x (11 / 4 : ℝ)).mul hloglog)
  refine (hfull.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  change Real.log y / 48 - Real.log 56 -
      (11 / 4 : ℝ) * Real.log (Real.log (256 * y)) =
    Real.log y / 48 - Real.log 56 -
      (11 / 4 : ℝ) * Real.log (Real.log (256 * y))
  rfl

private lemma cutoffGap_strictMonoOn :
    StrictMonoOn cutoffGap (Ici ((2 : ℝ) ^ 1617)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 1617).trans_le hx
    have hxone : 1 < x := (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1617 : ℕ) ≠ 0)).trans_le hx
    have hlogpos : 0 < Real.log (256 * x) := Real.log_pos (by nlinarith)
    exact (cutoffGap_hasDerivAt hxpos hlogpos).continuousAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 1617).trans hx
  have hlogarg : 132 < Real.log (256 * x) := by
    have hmono : Real.log (256 * (2 : ℝ) ^ 1617) < Real.log (256 * x) := by
      exact Real.strictMonoOn_log (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
        (mul_lt_mul_of_pos_left hx (by norm_num))
    have hbase : 132 < Real.log (256 * (2 : ℝ) ^ 1617) := by
      rw [show 256 * (2 : ℝ) ^ 1617 = (2 : ℝ) ^ 1625 by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add],
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans hmono
  have hinnerpos : 0 < Real.log (256 * x) := by linarith
  have hderiv := cutoffGap_hasDerivAt hxpos hinnerpos
  rw [hderiv.deriv]
  have hsimp : 256 / (256 * x) = x⁻¹ := by
    field_simp [hxpos.ne']
  rw [hsimp]
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hcoef : 0 < (1 / 48 : ℝ) - (11 / 4 : ℝ) / Real.log (256 * x) := by
    rw [sub_pos, div_lt_iff₀ hinnerpos]
    nlinarith
  have heq :
      x⁻¹ / 48 - (11 / 4 : ℝ) * x⁻¹ / Real.log (256 * x) =
        x⁻¹ * ((1 / 48 : ℝ) - (11 / 4 : ℝ) / Real.log (256 * x)) := by
    ring
  rw [heq]
  exact mul_pos hxinv hcoef

private lemma cutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 1617 ≤ x) : 0 < cutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact cutoffGap_endpoint_pos
  · exact cutoffGap_endpoint_pos.trans
      (cutoffGap_strictMonoOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx) hxlt)

/-- Above the explicit cutoff, the Granville--Ramaré lower bound is strictly
larger than their specialized reciprocal exponential-sum upper bound. -/
theorem granville_ramare_numeric_contradiction {n : ℕ} (hn : 2 ^ 1617 ≤ n) :
    (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ) <
      (2 / 35 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 1617 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 1617).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 1617).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := cutoffGap_pos_of_cutoff hnreal
  have hcore :
      (56 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ) < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_rpow hlogpos, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [cutoffGap] at hgap
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hcore (show (0 : ℝ) < 2 / 35 by norm_num)]

/-- The same cutoff calculation in the logically convenient contradiction
form used when the analytic lower and upper estimates are both available. -/
theorem not_lower_le_upper_of_ge_cutoff {n : ℕ} (hn : 2 ^ 1617 ≤ n) :
    ¬ ((2 / 35 : ℝ) * Real.sqrt n ≤
      (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ)) := by
  exact not_le_of_gt (granville_ramare_numeric_contradiction hn)

/-! ## A coarser lower-bound constant

The elementary Chebyshev argument used in an alternate assembly gives the
lower constant `1 / 50` instead of `2 / 35`.  The resulting exact cutoff is
slightly larger; `2 ^ 1728` is a convenient certified endpoint. -/

private noncomputable def coarseCutoffGap (x : ℝ) : ℝ :=
  Real.log x / 48 - Real.log 160 -
    (11 / 4 : ℝ) * Real.log (Real.log (256 * x))

private lemma coarse_endpoint_rational_power_bound :
    (160 : ℝ) ^ 48 * (23502021599 / 19531250 : ℝ) ^ 132 <
      (2 : ℝ) ^ 1728 := by
  have hnat :
      160 ^ 48 * 23502021599 ^ 132 < 2 ^ 1728 * 19531250 ^ 132 := by
    rw [show 2 ^ 1728 = (2 ^ 100) ^ 17 * 2 ^ 28 by
      calc
        2 ^ 1728 = 2 ^ (1700 + 28) := by norm_num
        _ = 2 ^ 1700 * 2 ^ 28 := pow_add 2 1700 28
        _ = 2 ^ (100 * 17) * 2 ^ 28 := by norm_num
        _ = (2 ^ 100) ^ 17 * 2 ^ 28 := by rw [pow_mul]]
    norm_num
  rw [div_pow]
  rw [show (160 : ℝ) ^ 48 *
      ((23502021599 : ℝ) ^ 132 / (19531250 : ℝ) ^ 132) =
    ((160 : ℝ) ^ 48 * (23502021599 : ℝ) ^ 132) /
      (19531250 : ℝ) ^ 132 by ring]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (19531250 : ℝ) ^ 132)]
  exact_mod_cast hnat

private lemma coarse_endpoint_power_bound :
    (160 : ℝ) ^ 48 * (1736 * Real.log 2) ^ 132 < (2 : ℝ) ^ 1728 := by
  have hlog : 1736 * Real.log 2 < (23502021599 / 19531250 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (1736 * Real.log 2) ^ 132 <
      (23502021599 / 19531250 : ℝ) ^ 132 := by
    exact pow_lt_pow_left₀ hlog (by positivity) (by norm_num)
  calc
    (160 : ℝ) ^ 48 * (1736 * Real.log 2) ^ 132 <
        (160 : ℝ) ^ 48 * (23502021599 / 19531250 : ℝ) ^ 132 := by
          exact mul_lt_mul_of_pos_left hpow (by positivity)
    _ < (2 : ℝ) ^ 1728 := coarse_endpoint_rational_power_bound

private lemma coarseCutoffGap_endpoint_pos :
    0 < coarseCutoffGap ((2 : ℝ) ^ 1728) := by
  have ht : 0 < 1736 * Real.log 2 := by positivity
  have hp := coarse_endpoint_power_bound
  have hp' := Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
    (mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 1728) = 1728 * Real.log 2 :=
    Real.log_pow 2 1728
  have harg : 256 * (2 : ℝ) ^ 1728 = (2 : ℝ) ^ 1736 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 1728) = 1736 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [coarseCutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma coarseCutoffGap_strictMonoOn :
    StrictMonoOn coarseCutoffGap (Ici ((2 : ℝ) ^ 1728)) := by
  intro x hx y hy hxy
  have hcutoff : (2 : ℝ) ^ 1617 ≤ (2 : ℝ) ^ 1728 :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hmono := cutoffGap_strictMonoOn
    (mem_Ici.mpr (hcutoff.trans hx)) (mem_Ici.mpr (hcutoff.trans hy)) hxy
  dsimp [cutoffGap, coarseCutoffGap] at hmono ⊢
  linarith

private lemma coarseCutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 1728 ≤ x) : 0 < coarseCutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact coarseCutoffGap_endpoint_pos
  · exact coarseCutoffGap_endpoint_pos.trans
      (coarseCutoffGap_strictMonoOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx) hxlt)

/-- With the coarser lower constant `1 / 50`, the same analytic upper bound
is contradictory for every natural `n ≥ 2 ^ 1728`. -/
theorem granville_ramare_numeric_contradiction_coarse {n : ℕ}
    (hn : 2 ^ 1728 ≤ n) :
    (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ) <
      (1 / 50 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 1728 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 1728).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := coarseCutoffGap_pos_of_cutoff hnreal
  have hcore :
      (160 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ) < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_rpow hlogpos, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [coarseCutoffGap] at hgap
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hcore (show (0 : ℝ) < 1 / 50 by norm_num)]

theorem not_coarse_lower_le_upper_of_ge_cutoff {n : ℕ} (hn : 2 ^ 1728 ≤ n) :
    ¬ ((1 / 50 : ℝ) * Real.sqrt n ≤
      (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ)) := by
  exact not_le_of_gt (granville_ramare_numeric_contradiction_coarse hn)

/-! ## Weakened analytic route

An intermediate version of the analytic estimate carries the larger
logarithmic exponent `13 / 4`, while the accompanying elementary lower bound
has constant `1 / 2000`.  The following exact calculation certifies the clean
power-of-two cutoff `2 ^ 2304`. -/

private noncomputable def weakenedCutoffGap (x : ℝ) : ℝ :=
  Real.log x / 48 - Real.log 6400 -
    (13 / 4 : ℝ) * Real.log (Real.log (256 * x))

private lemma weakened_endpoint_rational_power_bound :
    (6400 : ℝ) ^ 48 * (31299927383 / 19531250 : ℝ) ^ 156 <
      (2 : ℝ) ^ 2304 := by
  have hnat :
      6400 ^ 48 * 31299927383 ^ 156 < 2 ^ 2304 * 19531250 ^ 156 := by
    rw [show 2 ^ 2304 = (2 ^ 100) ^ 23 * 2 ^ 4 by
      calc
        2 ^ 2304 = 2 ^ (2300 + 4) := by norm_num
        _ = 2 ^ 2300 * 2 ^ 4 := pow_add 2 2300 4
        _ = 2 ^ (100 * 23) * 2 ^ 4 := by norm_num
        _ = (2 ^ 100) ^ 23 * 2 ^ 4 := by rw [pow_mul]]
    norm_num
  rw [div_pow]
  rw [show (6400 : ℝ) ^ 48 *
      ((31299927383 : ℝ) ^ 156 / (19531250 : ℝ) ^ 156) =
    ((6400 : ℝ) ^ 48 * (31299927383 : ℝ) ^ 156) /
      (19531250 : ℝ) ^ 156 by ring]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (19531250 : ℝ) ^ 156)]
  exact_mod_cast hnat

private lemma weakened_endpoint_power_bound :
    (6400 : ℝ) ^ 48 * (2312 * Real.log 2) ^ 156 < (2 : ℝ) ^ 2304 := by
  have hlog : 2312 * Real.log 2 < (31299927383 / 19531250 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (2312 * Real.log 2) ^ 156 <
      (31299927383 / 19531250 : ℝ) ^ 156 := by
    exact pow_lt_pow_left₀ hlog (by positivity) (by norm_num)
  calc
    (6400 : ℝ) ^ 48 * (2312 * Real.log 2) ^ 156 <
        (6400 : ℝ) ^ 48 * (31299927383 / 19531250 : ℝ) ^ 156 := by
          exact mul_lt_mul_of_pos_left hpow (by positivity)
    _ < (2 : ℝ) ^ 2304 := weakened_endpoint_rational_power_bound

private lemma weakenedCutoffGap_endpoint_pos :
    0 < weakenedCutoffGap ((2 : ℝ) ^ 2304) := by
  have ht : 0 < 2312 * Real.log 2 := by positivity
  have hp := weakened_endpoint_power_bound
  have hp' := Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
    (mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 2304) = 2304 * Real.log 2 :=
    Real.log_pow 2 2304
  have harg : 256 * (2 : ℝ) ^ 2304 = (2 : ℝ) ^ 2312 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 2304) = 2312 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [weakenedCutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma weakenedCutoffGap_hasDerivAt {x : ℝ} (hxpos : 0 < x)
    (hinnerpos : 0 < Real.log (256 * x)) :
    HasDerivAt weakenedCutoffGap
      (x⁻¹ / 48 - (13 / 4 : ℝ) * (256 / (256 * x)) /
        Real.log (256 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ 256 * y) 256 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (256 : ℝ)
  have hloglin : HasDerivAt (fun y : ℝ ↦ Real.log (256 * y))
      (256 / (256 * x)) x := hlin.log (by positivity)
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log (256 * y)))
      ((256 / (256 * x)) / Real.log (256 * x)) x :=
    hloglin.log hinnerpos.ne'
  unfold weakenedCutoffGap
  have hfull := (((Real.hasDerivAt_log hxpos.ne').div_const 48).sub_const
    (Real.log 6400)).sub ((hasDerivAt_const x (13 / 4 : ℝ)).mul hloglog)
  refine (hfull.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  change Real.log y / 48 - Real.log 6400 -
      (13 / 4 : ℝ) * Real.log (Real.log (256 * y)) =
    Real.log y / 48 - Real.log 6400 -
      (13 / 4 : ℝ) * Real.log (Real.log (256 * y))
  rfl

private lemma weakenedCutoffGap_strictMonoOn :
    StrictMonoOn weakenedCutoffGap (Ici ((2 : ℝ) ^ 2304)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 2304).trans_le hx
    have hxone : 1 < x := (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (2304 : ℕ) ≠ 0)).trans_le hx
    have hlogpos : 0 < Real.log (256 * x) := Real.log_pos (by nlinarith)
    exact (weakenedCutoffGap_hasDerivAt hxpos hlogpos).continuousAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 2304).trans hx
  have hlogarg : 156 < Real.log (256 * x) := by
    have hmono : Real.log (256 * (2 : ℝ) ^ 2304) < Real.log (256 * x) := by
      exact Real.strictMonoOn_log (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
        (mul_lt_mul_of_pos_left hx (by norm_num))
    have hbase : 156 < Real.log (256 * (2 : ℝ) ^ 2304) := by
      rw [show 256 * (2 : ℝ) ^ 2304 = (2 : ℝ) ^ 2312 by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add],
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans hmono
  have hinnerpos : 0 < Real.log (256 * x) := by linarith
  have hderiv := weakenedCutoffGap_hasDerivAt hxpos hinnerpos
  rw [hderiv.deriv]
  have hsimp : 256 / (256 * x) = x⁻¹ := by
    field_simp [hxpos.ne']
  rw [hsimp]
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hcoef : 0 < (1 / 48 : ℝ) - (13 / 4 : ℝ) / Real.log (256 * x) := by
    rw [sub_pos, div_lt_iff₀ hinnerpos]
    nlinarith
  have heq :
      x⁻¹ / 48 - (13 / 4 : ℝ) * x⁻¹ / Real.log (256 * x) =
        x⁻¹ * ((1 / 48 : ℝ) - (13 / 4 : ℝ) / Real.log (256 * x)) := by
    ring
  rw [heq]
  exact mul_pos hxinv hcoef

private lemma weakenedCutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 2304 ≤ x) : 0 < weakenedCutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact weakenedCutoffGap_endpoint_pos
  · exact weakenedCutoffGap_endpoint_pos.trans
      (weakenedCutoffGap_strictMonoOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx) hxlt)

/-- Numerical contradiction for the weakened analytic estimate carrying
`(log (256 n)) ^ (13 / 4)` and the lower constant `1 / 2000`. -/
theorem granville_ramare_numeric_contradiction_weakened {n : ℕ}
    (hn : 2 ^ 2304 ≤ n) :
    (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (13 / 4 : ℝ) <
      (1 / 2000 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 2304 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 2304).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 2304).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := weakenedCutoffGap_pos_of_cutoff hnreal
  have hcore :
      (6400 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ (13 / 4 : ℝ) < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_rpow hlogpos, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [weakenedCutoffGap] at hgap
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hcore (show (0 : ℝ) < 1 / 2000 by norm_num)]

theorem not_weakened_lower_le_upper_of_ge_cutoff {n : ℕ} (hn : 2 ^ 2304 ≤ n) :
    ¬ ((1 / 2000 : ℝ) * Real.sqrt n ≤
      (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (13 / 4 : ℝ)) := by
  exact not_le_of_gt (granville_ramare_numeric_contradiction_weakened hn)

/-! ## Robust weakened route

The fully coarse form of the analytic argument has coefficient `100` and
logarithmic exponent `15 / 4`.  After division by the lower constant
`1 / 2000`, the logarithmic gap contains the ratio `200000`. -/

private noncomputable def robustCutoffGap (x : ℝ) : ℝ :=
  Real.log x / 48 - Real.log 200000 -
    (15 / 4 : ℝ) * Real.log (Real.log (256 * x))

private lemma robust_endpoint_rational_power_bound :
    (200000 : ℝ) ^ 48 * (38231399191 / 19531250 : ℝ) ^ 180 <
      (2 : ℝ) ^ 2816 := by
  have hnat :
      200000 ^ 48 * 38231399191 ^ 180 < 2 ^ 2816 * 19531250 ^ 180 := by
    rw [show 2 ^ 2816 = (2 ^ 100) ^ 28 * 2 ^ 16 by
      calc
        2 ^ 2816 = 2 ^ (2800 + 16) := by norm_num
        _ = 2 ^ 2800 * 2 ^ 16 := pow_add 2 2800 16
        _ = 2 ^ (100 * 28) * 2 ^ 16 := by norm_num
        _ = (2 ^ 100) ^ 28 * 2 ^ 16 := by rw [pow_mul]]
    norm_num
  rw [div_pow]
  rw [show (200000 : ℝ) ^ 48 *
      ((38231399191 : ℝ) ^ 180 / (19531250 : ℝ) ^ 180) =
    ((200000 : ℝ) ^ 48 * (38231399191 : ℝ) ^ 180) /
      (19531250 : ℝ) ^ 180 by ring]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (19531250 : ℝ) ^ 180)]
  exact_mod_cast hnat

private lemma robust_endpoint_power_bound :
    (200000 : ℝ) ^ 48 * (2824 * Real.log 2) ^ 180 < (2 : ℝ) ^ 2816 := by
  have hlog : 2824 * Real.log 2 < (38231399191 / 19531250 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (2824 * Real.log 2) ^ 180 <
      (38231399191 / 19531250 : ℝ) ^ 180 := by
    exact pow_lt_pow_left₀ hlog (by positivity) (by norm_num)
  calc
    (200000 : ℝ) ^ 48 * (2824 * Real.log 2) ^ 180 <
        (200000 : ℝ) ^ 48 * (38231399191 / 19531250 : ℝ) ^ 180 := by
          exact mul_lt_mul_of_pos_left hpow (by positivity)
    _ < (2 : ℝ) ^ 2816 := robust_endpoint_rational_power_bound

private lemma robustCutoffGap_endpoint_pos :
    0 < robustCutoffGap ((2 : ℝ) ^ 2816) := by
  have ht : 0 < 2824 * Real.log 2 := by positivity
  have hp := robust_endpoint_power_bound
  have hp' := Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
    (mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 2816) = 2816 * Real.log 2 :=
    Real.log_pow 2 2816
  have harg : 256 * (2 : ℝ) ^ 2816 = (2 : ℝ) ^ 2824 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 2816) = 2824 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [robustCutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma robustCutoffGap_hasDerivAt {x : ℝ} (hxpos : 0 < x)
    (hinnerpos : 0 < Real.log (256 * x)) :
    HasDerivAt robustCutoffGap
      (x⁻¹ / 48 - (15 / 4 : ℝ) * (256 / (256 * x)) /
        Real.log (256 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ 256 * y) 256 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (256 : ℝ)
  have hloglin : HasDerivAt (fun y : ℝ ↦ Real.log (256 * y))
      (256 / (256 * x)) x := hlin.log (by positivity)
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log (256 * y)))
      ((256 / (256 * x)) / Real.log (256 * x)) x :=
    hloglin.log hinnerpos.ne'
  unfold robustCutoffGap
  have hfull := (((Real.hasDerivAt_log hxpos.ne').div_const 48).sub_const
    (Real.log 200000)).sub ((hasDerivAt_const x (15 / 4 : ℝ)).mul hloglog)
  refine (hfull.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  change Real.log y / 48 - Real.log 200000 -
      (15 / 4 : ℝ) * Real.log (Real.log (256 * y)) =
    Real.log y / 48 - Real.log 200000 -
      (15 / 4 : ℝ) * Real.log (Real.log (256 * y))
  rfl

private lemma robustCutoffGap_strictMonoOn :
    StrictMonoOn robustCutoffGap (Ici ((2 : ℝ) ^ 2816)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 2816).trans_le hx
    have hxone : 1 < x := (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (2816 : ℕ) ≠ 0)).trans_le hx
    have hlogpos : 0 < Real.log (256 * x) := Real.log_pos (by nlinarith)
    exact (robustCutoffGap_hasDerivAt hxpos hlogpos).continuousAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 2816).trans hx
  have hlogarg : 180 < Real.log (256 * x) := by
    have hmono : Real.log (256 * (2 : ℝ) ^ 2816) < Real.log (256 * x) := by
      exact Real.strictMonoOn_log (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
        (mul_lt_mul_of_pos_left hx (by norm_num))
    have hbase : 180 < Real.log (256 * (2 : ℝ) ^ 2816) := by
      rw [show 256 * (2 : ℝ) ^ 2816 = (2 : ℝ) ^ 2824 by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add],
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans hmono
  have hinnerpos : 0 < Real.log (256 * x) := by linarith
  have hderiv := robustCutoffGap_hasDerivAt hxpos hinnerpos
  rw [hderiv.deriv]
  have hsimp : 256 / (256 * x) = x⁻¹ := by
    field_simp [hxpos.ne']
  rw [hsimp]
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hcoef : 0 < (1 / 48 : ℝ) - (15 / 4 : ℝ) / Real.log (256 * x) := by
    rw [sub_pos, div_lt_iff₀ hinnerpos]
    nlinarith
  have heq :
      x⁻¹ / 48 - (15 / 4 : ℝ) * x⁻¹ / Real.log (256 * x) =
        x⁻¹ * ((1 / 48 : ℝ) - (15 / 4 : ℝ) / Real.log (256 * x)) := by
    ring
  rw [heq]
  exact mul_pos hxinv hcoef

private lemma robustCutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 2816 ≤ x) : 0 < robustCutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact robustCutoffGap_endpoint_pos
  · exact robustCutoffGap_endpoint_pos.trans
      (robustCutoffGap_strictMonoOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx) hxlt)

/-- Robust numerical contradiction for the coarse coefficient-`100`,
log-exponent-`15 / 4` route. -/
theorem granville_ramare_numeric_contradiction_robust {n : ℕ}
    (hn : 2 ^ 2816 ≤ n) :
    (100 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (15 / 4 : ℝ) <
      (1 / 2000 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 2816 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 2816).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 2816).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := robustCutoffGap_pos_of_cutoff hnreal
  have hcore :
      (200000 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ (15 / 4 : ℝ) < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_rpow hlogpos, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [robustCutoffGap] at hgap
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hcore (show (0 : ℝ) < 1 / 2000 by norm_num)]

theorem not_robust_lower_le_upper_of_ge_cutoff {n : ℕ} (hn : 2 ^ 2816 ≤ n) :
    ¬ ((1 / 2000 : ℝ) * Real.sqrt n ≤
      (100 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (15 / 4 : ℝ)) := by
  exact not_le_of_gt (granville_ramare_numeric_contradiction_robust hn)

/-! ## Final coarse envelope

The last assembly uses the deliberately generous coefficient `10^12`, the
power `27 / 56`, and six powers of the logarithm.  Although the gap to the
square-root exponent is only `1 / 56`, the power-of-two endpoint `2 ^ 8192`
still leaves ample room.  Multiplying by the reciprocal of the lower-bound
constant `1 / 5000` gives the ratio `5 * 10^15` below.
-/

private noncomputable def finalCutoffGap (x : ℝ) : ℝ :=
  Real.log x / 56 - Real.log 5000000000000000 -
    6 * Real.log (Real.log (256 * x))

private lemma final_endpoint_integer_power_bound :
    (5000000000000000 : ℝ) ^ 56 * (6000 : ℝ) ^ 336 <
      (2 : ℝ) ^ 8192 := by
  have hnat :
      5000000000000000 ^ 56 * 6000 ^ 336 < (2 : ℕ) ^ 8192 := by
    calc
      5000000000000000 ^ 56 * 6000 ^ 336 <
          ((2 : ℕ) ^ 53) ^ 56 * ((2 : ℕ) ^ 13) ^ 336 := by
            gcongr <;> norm_num
      _ = (2 : ℕ) ^ 7336 := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
      _ < (2 : ℕ) ^ 8192 :=
        Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  exact_mod_cast hnat

private lemma final_endpoint_power_bound :
    (5000000000000000 : ℝ) ^ 56 * (8200 * Real.log 2) ^ 336 <
      (2 : ℝ) ^ 8192 := by
  have hlog : 8200 * Real.log 2 < (6000 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (8200 * Real.log 2) ^ 336 < (6000 : ℝ) ^ 336 := by
    exact pow_lt_pow_left₀ hlog (by positivity) (by norm_num)
  calc
    (5000000000000000 : ℝ) ^ 56 * (8200 * Real.log 2) ^ 336 <
        (5000000000000000 : ℝ) ^ 56 * (6000 : ℝ) ^ 336 := by
          exact mul_lt_mul_of_pos_left hpow (by positivity)
    _ < (2 : ℝ) ^ 8192 := final_endpoint_integer_power_bound

private lemma finalCutoffGap_endpoint_pos :
    0 < finalCutoffGap ((2 : ℝ) ^ 8192) := by
  have hp := final_endpoint_power_bound
  have hp' := Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
    (mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 8192) = 8192 * Real.log 2 :=
    Real.log_pow 2 8192
  have harg : 256 * (2 : ℝ) ^ 8192 = (2 : ℝ) ^ 8200 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 8192) = 8200 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [finalCutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma finalCutoffGap_hasDerivAt {x : ℝ} (hxpos : 0 < x)
    (hinnerpos : 0 < Real.log (256 * x)) :
    HasDerivAt finalCutoffGap
      (x⁻¹ / 56 - 6 * (256 / (256 * x)) / Real.log (256 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ 256 * y) 256 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (256 : ℝ)
  have hloglin : HasDerivAt (fun y : ℝ ↦ Real.log (256 * y))
      (256 / (256 * x)) x := hlin.log (by positivity)
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log (256 * y)))
      ((256 / (256 * x)) / Real.log (256 * x)) x :=
    hloglin.log hinnerpos.ne'
  unfold finalCutoffGap
  have hfull := (((Real.hasDerivAt_log hxpos.ne').div_const 56).sub_const
    (Real.log 5000000000000000)).sub ((hasDerivAt_const x (6 : ℝ)).mul hloglog)
  refine (hfull.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  change Real.log y / 56 - Real.log 5000000000000000 -
      6 * Real.log (Real.log (256 * y)) =
    Real.log y / 56 - Real.log 5000000000000000 -
      6 * Real.log (Real.log (256 * y))
  rfl

private lemma finalCutoffGap_strictMonoOn :
    StrictMonoOn finalCutoffGap (Ici ((2 : ℝ) ^ 8192)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 8192).trans_le hx
    have hxone : 1 < x := (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (8192 : ℕ) ≠ 0)).trans_le hx
    have hlogpos : 0 < Real.log (256 * x) := Real.log_pos (by nlinarith)
    exact (finalCutoffGap_hasDerivAt hxpos hlogpos).continuousAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 8192).trans hx
  have hlogarg : 336 < Real.log (256 * x) := by
    have hmono : Real.log (256 * (2 : ℝ) ^ 8192) < Real.log (256 * x) := by
      exact Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
        (mem_Ioi.mpr (by positivity)) (mul_lt_mul_of_pos_left hx (by norm_num))
    have hbase : 336 < Real.log (256 * (2 : ℝ) ^ 8192) := by
      rw [show 256 * (2 : ℝ) ^ 8192 = (2 : ℝ) ^ 8200 by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add],
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans hmono
  have hinnerpos : 0 < Real.log (256 * x) := by linarith
  have hderiv := finalCutoffGap_hasDerivAt hxpos hinnerpos
  rw [hderiv.deriv]
  have hsimp : 256 / (256 * x) = x⁻¹ := by
    field_simp [hxpos.ne']
  rw [hsimp]
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hcoef : 0 < (1 / 56 : ℝ) - 6 / Real.log (256 * x) := by
    rw [sub_pos, div_lt_iff₀ hinnerpos]
    nlinarith
  have heq :
      x⁻¹ / 56 - 6 * x⁻¹ / Real.log (256 * x) =
        x⁻¹ * ((1 / 56 : ℝ) - 6 / Real.log (256 * x)) := by
    ring
  rw [heq]
  exact mul_pos hxinv hcoef

private lemma finalCutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 8192 ≤ x) : 0 < finalCutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact finalCutoffGap_endpoint_pos
  · exact finalCutoffGap_endpoint_pos.trans
      (finalCutoffGap_strictMonoOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx) hxlt)

/-- At `n ≥ 2 ^ 8192`, even the coefficient-`10^12`, exponent-`27 / 56`,
six-logarithm upper envelope is strictly below the elementary lower bound. -/
theorem granville_ramare_numeric_contradiction_final {n : ℕ}
    (hn : 2 ^ 8192 ≤ n) :
    (10 ^ 12 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ 6 <
      (1 / 5000 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 8192 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 8192).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 8192).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := finalCutoffGap_pos_of_cutoff hnreal
  have hcore :
      (5000000000000000 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ 6 < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_pow, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [finalCutoffGap] at hgap
    norm_num at hgap ⊢
    linarith
  nlinarith [mul_lt_mul_of_pos_left hcore (show (0 : ℝ) < 1 / 5000 by norm_num)]

theorem not_final_lower_le_upper_of_ge_cutoff {n : ℕ} (hn : 2 ^ 8192 ≤ n) :
    ¬ ((1 / 5000 : ℝ) * Real.sqrt n ≤
      (10 ^ 12 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ 6) := by
  exact not_le_of_gt (granville_ramare_numeric_contradiction_final hn)

#print axioms granville_ramare_numeric_contradiction
#print axioms granville_ramare_numeric_contradiction_coarse
#print axioms granville_ramare_numeric_contradiction_weakened
#print axioms granville_ramare_numeric_contradiction_robust
#print axioms granville_ramare_numeric_contradiction_final

end Erdos175
