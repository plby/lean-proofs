/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Endpoint
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős Problem 446: asymptotic scale and perturbation lemmas

This file defines the precise Ford scale and proves that the one-endpoint
error is negligible on that scale.  It also provides the norm-controlled
perturbation lemma used to transfer Ford's half-open result to the literal
open interval in the problem.
-/

namespace Erdos446

open Filter Real
open scoped Topology

/-- Ford's exponent `1 - (1 + log log 2) / log 2`. -/
noncomputable def alpha446 : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- The denominator in Ford's dyadic density scale. -/
noncomputable def growthDenominator446 (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ alpha446 *
    Real.log (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)

/-- `1 / ((log n)^alpha446 (log log n)^(3/2))`. -/
noncomputable def growth446 (n : ℕ) : ℝ :=
  (growthDenominator446 n)⁻¹

theorem alpha446_pos : 0 < alpha446 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2lt : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hlog2ne : Real.log 2 ≠ 1 := ne_of_lt hlog2lt
  have hstrict := Real.log_lt_sub_one_of_pos hlog2pos hlog2ne
  have hnum : 1 + Real.log (Real.log 2) < Real.log 2 := by linarith
  have hquot : (1 + Real.log (Real.log 2)) / Real.log 2 < 1 :=
    (div_lt_one hlog2pos).2 hnum
  simpa only [alpha446] using sub_pos.mpr hquot

private theorem tendsto_logLog_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_growthDenominator446_pos :
    ∀ᶠ n : ℕ in atTop, 0 < growthDenominator446 n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlog.eventually (eventually_gt_atTop 0),
        tendsto_logLog_nat_atTop.eventually (eventually_gt_atTop 0)]
      with n hn hhn
  exact mul_pos (Real.rpow_pos_of_pos hn alpha446)
    (Real.rpow_pos_of_pos hhn (3 / 2 : ℝ))

private theorem growthDenominator446_isLittleO_natCast :
    growthDenominator446 =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have hlogReal :
      (fun x : ℝ ↦ Real.log x ^ alpha446) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop alpha446 (by norm_num)
  have hlogNat :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ alpha446) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ)) :=
    hlogReal.natCast_atTop
  have hlogLogToLogReal :
      (fun x : ℝ ↦ Real.log (Real.log x) ^ (3 / 2 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ Real.log x ^ (1 / 2 : ℝ)) :=
    (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) (by norm_num)).comp_tendsto
      Real.tendsto_log_atTop
  have hlogToSqrtReal :
      (fun x : ℝ ↦ Real.log x ^ (1 / 2 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ) (by norm_num)
  have hlogLogNat :
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ)) :=
    (hlogLogToLogReal.trans hlogToSqrtReal).natCast_atTop
  have hproduct := hlogNat.mul hlogLogNat
  refine hproduct.congr' ?_ ?_
  · exact Eventually.of_forall fun n ↦ by
      simp only [growthDenominator446, Pi.mul_apply]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.rpow_add hnR]
    norm_num

/-- The density of the single right endpoint is negligible on Ford's scale. -/
theorem one_div_nat_isLittleO_growth446 :
    (fun n : ℕ ↦ 1 / (n : ℝ)) =o[atTop] growth446 := by
  have hgrowthPos : ∀ᶠ n : ℕ in atTop, 0 < growth446 n :=
    eventually_growthDenominator446_pos.mono fun n hn ↦ by
      exact inv_pos.mpr hn
  apply Asymptotics.isLittleO_of_tendsto'
    (hgrowthPos.mono fun _ hn hzero ↦ (hn.ne' hzero).elim)
  have hratio := growthDenominator446_isLittleO_natCast.tendsto_div_nhds_zero
  apply hratio.congr'
  filter_upwards [eventually_growthDenominator446_pos,
    eventually_gt_atTop 0] with n hden hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [growth446, one_div, div_eq_mul_inv, inv_inv]
  field_simp [hden.ne', hnR.ne']

theorem endpointError_isLittleO_growth446 :
    (fun n : ℕ ↦ 1 / (2 * n : ℝ)) =o[atTop] growth446 := by
  have h := one_div_nat_isLittleO_growth446.const_mul_left (1 / 2 : ℝ)
  refine h.congr_left ?_
  intro n
  simp only [one_div, Nat.cast_ofNat, Nat.cast_mul]
  rw [mul_inv_rev]
  ring

/-- A pointwise norm error that is little-oh of `g` does not change a
Theta estimate. -/
theorem isTheta_of_isTheta_of_abs_sub_isLittleO
    {f h e g : ℕ → ℝ}
    (hf : f =Θ[atTop] g) (he : e =o[atTop] g)
    (hbound : ∀ᶠ n : ℕ in atTop, |h n - f n| ≤ |e n|) :
    h =Θ[atTop] g := by
  have herrorBigO : (fun n ↦ h n - f n) =O[atTop] e := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hbound] with n hn
    simpa only [Real.norm_eq_abs, one_mul] using hn
  have herror : (fun n ↦ h n - f n) =o[atTop] g :=
    herrorBigO.trans_isLittleO he
  have hsum : (f + fun n ↦ h n - f n) =Θ[atTop] g :=
    Asymptotics.IsTheta.add_isLittleO hf herror
  have heq : f + (fun n ↦ h n - f n) = h := by
    funext n
    simp only [Pi.add_apply]
    ring
  rw [heq] at hsum
  exact hsum

/-- The open and half-open union densities have the same asymptotic scale. -/
theorem delta_isTheta_growth446_of_epsilon
    (hford : (fun n ↦ epsilon n (2 * n)) =Θ[atTop] growth446) :
    delta =Θ[atTop] growth446 := by
  apply isTheta_of_isTheta_of_abs_sub_isLittleO hford
    endpointError_isLittleO_growth446
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h := abs_delta_sub_epsilon_le n hn
  have herrpos : 0 < (1 / (2 * n : ℝ)) := by positivity
  simpa only [abs_abs, abs_of_pos herrpos] using h

end Erdos446
