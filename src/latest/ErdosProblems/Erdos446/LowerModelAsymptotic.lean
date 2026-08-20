/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ScaleAsymptotics

/-!
# Erdős Problem 446: the lower model has Ford's order

The identity `2 * exp 1 * log 2 = 2 ^ (2 - alpha446)` converts the
exponential-in-depth output of the construction into a power of `log y`.
Together with Stirling's `K^(-3/2)` term and the selected-depth comparisons,
this gives exactly `growth446` after the two sieve logarithms are divided out.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

theorem ford_exponential_base :
    (2 * Real.log 2 * Real.exp 1 : ℝ) =
      (2 : ℝ) ^ (2 - alpha446) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogne : Real.log 2 ≠ 0 := hlog.ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexponent : Real.log 2 * (2 - alpha446) =
      Real.log 2 + 1 + Real.log (Real.log 2) := by
    dsimp [alpha446]
    field_simp [hlogne]
    ring
  rw [hexponent, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
    Real.exp_log hlog]
  ring

noncomputable def fordDepthModel (M y : ℕ) : ℝ :=
  ((2 : ℝ) ^ fordScaleDepth M y) ^ (2 - alpha446) /
    (fordScaleDepth M y : ℝ) ^ (3 / 2 : ℝ)

private theorem self_mul_sqrt_eq_rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  calc
    x * Real.sqrt x = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) + 1 / 2) :=
      (Real.rpow_add hx (1 : ℝ) (1 / 2 : ℝ)).symm
    _ = x ^ (3 / 2 : ℝ) := by norm_num

theorem fordStirlingModel_eq_depthModel {K : ℕ} (hK : 0 < K) :
    fordStirlingModel K =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (((2 : ℝ) ^ K) ^ (2 - alpha446) /
          (K : ℝ) ^ (3 / 2 : ℝ)) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hden : (K : ℝ) * Real.sqrt (2 * (K : ℝ) * Real.pi) =
      Real.sqrt (2 * Real.pi) * (K : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show 2 * (K : ℝ) * Real.pi = (2 * Real.pi) * K by ring,
      Real.sqrt_mul (by positivity)]
    rw [show (K : ℝ) * (Real.sqrt (2 * Real.pi) * Real.sqrt K) =
      Real.sqrt (2 * Real.pi) * ((K : ℝ) * Real.sqrt K) by ring,
      self_mul_sqrt_eq_rpow_three_halves hKR]
  dsimp [fordStirlingModel]
  rw [ford_exponential_base,
    Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), hden]
  field_simp

theorem fordCombinatorialWeight_depth_isTheta_depthModel (M : ℕ) :
    (fun y : ℕ ↦ fordCombinatorialWeight (fordScaleDepth M y)) =Θ[atTop]
      fordDepthModel M := by
  have hcoeff :
      (fun y : ℕ ↦ fordCombinatorialWeight (fordScaleDepth M y)) =Θ[atTop]
        (fun y : ℕ ↦ fordStirlingModel (fordScaleDepth M y)) :=
    ⟨fordCombinatorialWeight_isTheta_stirlingModel.1.comp_tendsto
        (tendsto_fordScaleDepth_atTop M),
      fordCombinatorialWeight_isTheta_stirlingModel.2.comp_tendsto
        (tendsto_fordScaleDepth_atTop M)⟩
  have heq :
      (fun y : ℕ ↦ fordStirlingModel (fordScaleDepth M y)) =ᶠ[atTop]
        fun y : ℕ ↦
          (Real.sqrt (2 * Real.pi))⁻¹ * fordDepthModel M y := by
    filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    rw [fordStirlingModel_eq_depthModel (fordScaleDepth_pos hy)]
    rfl
  have hconst :
      (fun y : ℕ ↦ (Real.sqrt (2 * Real.pi))⁻¹ * fordDepthModel M y) =Θ[atTop]
        fordDepthModel M := by
    exact (isTheta_const_mul_left (inv_ne_zero (by positivity))).2 isTheta_rfl
  exact hcoeff.trans (heq.isTheta.trans hconst)

theorem fordDepthModel_isTheta_logModel (M : ℕ) :
    fordDepthModel M =Θ[atTop]
      (fun y : ℕ ↦
        Real.log (y : ℝ) ^ (2 - alpha446) /
          Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ)) := by
  have hlog := log_nat_isTheta_pow_fordScaleDepth M
  have hloglog := log_log_nat_isTheta_fordScaleDepth M
  have hlogNonneg : ∀ᶠ y : ℕ in atTop, 0 ≤ Real.log (y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 0)
  have hpowNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ (2 : ℝ) ^ fordScaleDepth M y :=
    Eventually.of_forall fun _ ↦ by positivity
  have hloglogNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (Real.log (y : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop 0)
  have hdepthNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ (fordScaleDepth M y : ℝ) :=
    Eventually.of_forall fun _ ↦ Nat.cast_nonneg _
  have hnum := hlog.symm.rpow hpowNonneg hlogNonneg
    (r := 2 - alpha446)
  have hden := hloglog.symm.rpow hdepthNonneg hloglogNonneg
    (r := (3 / 2 : ℝ))
  have hdiv := hnum.div hden
  have hdef : fordDepthModel M =ᶠ[atTop]
      fun y : ℕ ↦
        ((2 : ℝ) ^ fordScaleDepth M y) ^ (2 - alpha446) /
          (fordScaleDepth M y : ℝ) ^ (3 / 2 : ℝ) :=
    Eventually.of_forall fun _ ↦ rfl
  exact hdef.isTheta.trans hdiv

noncomputable def fordDepthDensityModel (M y : ℕ) : ℝ :=
  fordDepthModel M y / Real.log (y : ℝ) ^ 2

theorem fordDepthDensityModel_isTheta_growth446 (M : ℕ) :
    fordDepthDensityModel M =Θ[atTop] growth446 := by
  have hmodel := fordDepthModel_isTheta_logModel M
  have hdiv := hmodel.div
    (isTheta_refl (fun y : ℕ ↦ Real.log (y : ℝ) ^ 2) atTop)
  have heq :
      (fun y : ℕ ↦
          (Real.log (y : ℝ) ^ (2 - alpha446) /
            Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ)) /
              Real.log (y : ℝ) ^ 2) =ᶠ[atTop] growth446 := by
    filter_upwards [(Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)]
      with y hlog
    dsimp [growth446, growthDenominator446]
    have hpow :
        Real.log (y : ℝ) ^ (2 - alpha446) /
            Real.log (y : ℝ) ^ 2 =
          Real.log (y : ℝ) ^ (-alpha446) := by
      calc
        Real.log (y : ℝ) ^ (2 - alpha446) /
              Real.log (y : ℝ) ^ 2 =
            Real.log (y : ℝ) ^ (2 - alpha446) /
              Real.log (y : ℝ) ^ (2 : ℝ) := by
          congr 1
          exact (Real.rpow_natCast (Real.log (y : ℝ)) 2).symm
        _ = Real.log (y : ℝ) ^ ((2 - alpha446) - 2) :=
          (Real.rpow_sub hlog (2 - alpha446) 2).symm
        _ = Real.log (y : ℝ) ^ (-alpha446) := by
          congr 1
          ring
    rw [show
      (Real.log (y : ℝ) ^ (2 - alpha446) /
          Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ)) /
            Real.log (y : ℝ) ^ 2 =
        (Real.log (y : ℝ) ^ (2 - alpha446) /
            Real.log (y : ℝ) ^ 2) /
          Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ) by ring,
      hpow]
    calc
      Real.log (y : ℝ) ^ (-alpha446) /
            Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ) =
          (Real.log (y : ℝ) ^ alpha446)⁻¹ /
            Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ) := by
        exact congrArg
          (fun z : ℝ ↦ z /
            Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ))
          (Real.rpow_neg hlog.le alpha446)
      _ = (Real.log (y : ℝ) ^ alpha446 *
          Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ))⁻¹ := by
        ring
  exact hdiv.trans heq.isTheta

end Erdos446
