/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Parameters for the Liu--Sawhney lower bound in Erdős problem 297

This file records the three scales used in the application of Proposition 3.2
of Liu--Sawhney:

* `M = N / sqrt (log log log N)`;
* `S = N / (log N)^4`;
* `K = 10^{-7} N / log N`.

The real scales are the quantities which occur in the analytic inequalities.
Natural-number parameters are obtained by taking floors.  All the statements
below are eventual statements, so the harmless values of `Real.log` before its
arguments enter the positive range never play a role.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos297

/-- `log N`, regarded as a function on natural numbers. -/
noncomputable def logScale (N : ℕ) : ℝ := Real.log (N : ℝ)

/-- `log log N`, regarded as a function on natural numbers. -/
noncomputable def logLogScale (N : ℕ) : ℝ := Real.log (logScale N)

/-- `log log log N`, regarded as a function on natural numbers. -/
noncomputable def logLogLogScale (N : ℕ) : ℝ := Real.log (logLogScale N)

/-- The smoothness scale `M = N / sqrt (log log log N)`. -/
noncomputable def MReal (N : ℕ) : ℝ :=
  (N : ℝ) / Real.sqrt (logLogLogScale N)

/-- The small-prime-power cutoff `S = N / (log N)^4`. -/
noncomputable def SReal (N : ℕ) : ℝ :=
  (N : ℝ) / logScale N ^ 4

/-- The factorization scale `K = 10⁻⁷ N / log N`. -/
noncomputable def KReal (N : ℕ) : ℝ :=
  (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)

/-- A slightly smaller factorization scale which leaves a growing dyadic
multiplier window: `N / (10^7 log N log log N)`. -/
noncomputable def KSafeReal (N : ℕ) : ℝ :=
  KReal N / logLogScale N

/-- The integer version of `MReal`. -/
noncomputable def M (N : ℕ) : ℕ := ⌊MReal N⌋₊

/-- The integer version of `SReal`. -/
noncomputable def S (N : ℕ) : ℕ := ⌊SReal N⌋₊

/-- The integer version of `KReal`. -/
noncomputable def K (N : ℕ) : ℕ := ⌊KReal N⌋₊

/-- Integer version of the safe factorization scale. -/
noncomputable def KSafe (N : ℕ) : ℕ := ⌊KSafeReal N⌋₊

/-- Available dyadic multiplier scale after reserving the factor `4000`. -/
noncomputable def dyadicMultiplierScale (N : ℕ) : ℝ :=
  (N : ℝ) / (4000 * (KSafe N : ℝ) * logScale N)

/-- The exponent `0.9999` in the range condition of Liu--Sawhney. -/
noncomputable def almostOnePower (N : ℕ) : ℝ :=
  (N : ℝ) ^ ((9999 : ℝ) / 10000)

/-- All numerical hypotheses on `S`, `K`, and `M` in Liu--Sawhney,
Proposition 3.2, specialized to the scales used for Erdős problem 297. -/
def LiuScaleConditions (C : ℝ) (N : ℕ) : Prop :=
  almostOnePower N ≤ SReal N ∧
    SReal N ≤ KReal N ∧
    KReal N ≤ MReal N ∧
    MReal N ≤ (N : ℝ) / 10 ∧
    SReal N ≤ MReal N ^ 2 / (C * (N : ℝ)) ∧
    SReal N ≤ KReal N ^ 3 /
      (C * (N : ℝ) ^ 2 * logLogScale N ^ 5) ∧
    (N : ℝ) / logScale N ^ 10 ≤ KReal N ∧
    KReal N ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)

/-- The same hypotheses after the source parameters have been rounded down to
natural numbers.  Casts are displayed explicitly because the two nonlinear
hypotheses are analytic inequalities. -/
def LiuNatScaleConditions (C : ℝ) (N : ℕ) : Prop :=
  almostOnePower N ≤ (S N : ℝ) ∧
    (S N : ℝ) ≤ (K N : ℝ) ∧
    (K N : ℝ) ≤ (M N : ℝ) ∧
    (M N : ℝ) ≤ (N : ℝ) / 10 ∧
    (S N : ℝ) ≤ (M N : ℝ) ^ 2 / (C * (N : ℝ)) ∧
    (S N : ℝ) ≤ (K N : ℝ) ^ 3 /
      (C * (N : ℝ) ^ 2 * logLogScale N ^ 5) ∧
    (N : ℝ) / logScale N ^ 10 ≤ (K N : ℝ) ∧
    (K N : ℝ) ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)

/-- The repaired scale package used when the averaged phase derivative costs
one additional factor of `log log N`. -/
def LiuScaleConditionsSix (C : ℝ) (N : ℕ) : Prop :=
  LiuScaleConditions C N ∧
    SReal N ≤ KReal N ^ 3 /
      (C * (N : ℝ) ^ 2 * logLogScale N ^ 6)

/-- Natural-floor version of `LiuScaleConditionsSix`. -/
def LiuNatScaleConditionsSix (C : ℝ) (N : ℕ) : Prop :=
  LiuNatScaleConditions C N ∧
    (S N : ℝ) ≤ (K N : ℝ) ^ 3 /
      (C * (N : ℝ) ^ 2 * logLogScale N ^ 6)

/-- The source scale conditions with the safe factorization cutoff.  The
cubic bound uses the repaired sixth power of `log log N`. -/
def LiuSafeNatScaleConditions (C : ℝ) (N : ℕ) : Prop :=
  almostOnePower N ≤ (S N : ℝ) ∧
    (S N : ℝ) ≤ (KSafe N : ℝ) ∧
    (KSafe N : ℝ) ≤ (M N : ℝ) ∧
    (M N : ℝ) ≤ (N : ℝ) / 10 ∧
    (S N : ℝ) ≤ (M N : ℝ) ^ 2 / (C * (N : ℝ)) ∧
    (S N : ℝ) ≤ (KSafe N : ℝ) ^ 3 /
      (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) ∧
    (N : ℝ) / logScale N ^ 10 ≤ (KSafe N : ℝ) ∧
    (KSafe N : ℝ) ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)

lemma tendsto_logScale : Tendsto logScale atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_logLogScale : Tendsto logLogScale atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_logScale

lemma tendsto_logLogLogScale : Tendsto logLogLogScale atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_logLogScale

lemma eventually_pos_scales :
    ∀ᶠ N : ℕ in atTop,
      0 < (N : ℝ) ∧ 1 < logScale N ∧ 1 < logLogScale N ∧
        0 < logLogLogScale N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_logScale.eventually_gt_atTop 1,
    tendsto_logLogScale.eventually_gt_atTop 1,
    tendsto_logLogLogScale.eventually_gt_atTop 0] with N hN hL hLL hLLL
  exact ⟨by exact_mod_cast hN, hL, hLL, hLLL⟩

lemma eventually_log_pow_four_le_small_rpow :
    ∀ᶠ N : ℕ in atTop,
      logScale N ^ 4 ≤ (N : ℝ) ^ ((1 : ℝ) / 10000) := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (4 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ ((1 : ℝ) / 10000)) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num)
  have hcomp := (hlittle.comp_tendsto tendsto_natCast_atTop_atTop).bound one_pos
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hlognonneg : 0 ≤ Real.log (N : ℝ) := by
    simpa [logScale] using zero_le_one.trans hL.le
  simp only [Function.comp_apply, one_mul] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  simpa [logScale, Real.rpow_natCast] using hN

lemma eventually_mul_log_pow_four_le_small_rpow (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      D * logScale N ^ 4 ≤ (N : ℝ) ^ ((1 : ℝ) / 10000) := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (4 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ ((1 : ℝ) / 10000)) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num)
  have hcomp :=
    (hlittle.comp_tendsto tendsto_natCast_atTop_atTop).bound (inv_pos.mpr hD)
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hlognonneg : 0 ≤ Real.log (N : ℝ) := by
    simpa [logScale] using zero_le_one.trans hL.le
  simp only [Function.comp_apply] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  have hraw : logScale N ^ 4 ≤ D⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 10000) := by
    simpa [logScale, Real.rpow_natCast] using hN
  calc
    D * logScale N ^ 4 ≤ D * (D⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 10000)) :=
      mul_le_mul_of_nonneg_left hraw hD.le
    _ = (N : ℝ) ^ ((1 : ℝ) / 10000) := by field_simp

lemma eventually_mul_almostOnePower_le_SReal (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, D * almostOnePower N ≤ SReal N := by
  filter_upwards [eventually_mul_log_pow_four_le_small_rpow D hD,
    eventually_pos_scales] with N hlog hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hN0 : 0 ≤ (N : ℝ) := hNpos.le
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hpowpos : 0 < logScale N ^ 4 := pow_pos hLpos _
  rw [almostOnePower, SReal]
  apply (le_div_iff₀ hpowpos).2
  calc
    D * (N : ℝ) ^ ((9999 : ℝ) / 10000) * logScale N ^ 4 =
        (N : ℝ) ^ ((9999 : ℝ) / 10000) *
          (D * logScale N ^ 4) := by ring
    _ ≤ (N : ℝ) ^ ((9999 : ℝ) / 10000) *
          (N : ℝ) ^ ((1 : ℝ) / 10000) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hN0 _)
    _ = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num

lemma eventually_almostOnePower_le_SReal :
    ∀ᶠ N : ℕ in atTop, almostOnePower N ≤ SReal N := by
  filter_upwards [eventually_log_pow_four_le_small_rpow,
    eventually_pos_scales] with N hlog hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hpowpos : 0 < logScale N ^ 4 := pow_pos hLpos _
  rw [almostOnePower, SReal]
  apply (le_div_iff₀ hpowpos).2
  calc
    (N : ℝ) ^ ((9999 : ℝ) / 10000) * logScale N ^ 4
        ≤ (N : ℝ) ^ ((9999 : ℝ) / 10000) *
            (N : ℝ) ^ ((1 : ℝ) / 10000) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hN0 _)
    _ = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num

lemma eventually_SReal_le_KReal :
    ∀ᶠ N : ℕ in atTop, SReal N ≤ KReal N := by
  have hlarge := tendsto_logScale.eventually_ge_atTop ((10 : ℝ) ^ 3)
  filter_upwards [hlarge, eventually_pos_scales] with N hL hpos
  rcases hpos with ⟨hNpos, hLone, hLL, hLLL⟩
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hLp : 0 < logScale N := zero_lt_one.trans hLone
  dsimp [SReal, KReal]
  rw [div_le_div_iff_of_pos_left hNpos (pow_pos hLp 4)
    (mul_pos (by positivity) hLp)]
  have hcub : (10 : ℝ) ^ 7 ≤ logScale N ^ 3 := by
    calc
      (10 : ℝ) ^ 7 ≤ ((10 : ℝ) ^ 3) ^ 3 := by norm_num
      _ ≤ logScale N ^ 3 := pow_le_pow_left₀ (by positivity) hL 3
  nlinarith [mul_pos (sq_pos_of_pos hLp) hLp]

lemma eventually_logLogScale_le_logScale :
    ∀ᶠ N : ℕ in atTop, logLogScale N ≤ logScale N := by
  filter_upwards [eventually_pos_scales] with N hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  dsimp [logLogScale]
  exact (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)

lemma eventually_SReal_le_KSafeReal :
    ∀ᶠ N : ℕ in atTop, SReal N ≤ KSafeReal N := by
  have hlarge := tendsto_logScale.eventually_ge_atTop 10000
  filter_upwards [hlarge, eventually_logLogScale_le_logScale,
    eventually_pos_scales] with N hLlarge hLLle hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  dsimp [SReal, KSafeReal, KReal]
  field_simp
  have hconst : (10 : ℝ) ^ 7 ≤ logScale N ^ 2 := by
    calc
      (10 : ℝ) ^ 7 ≤ (10000 : ℝ) ^ 2 := by norm_num
      _ ≤ logScale N ^ 2 := pow_le_pow_left₀ (by norm_num) hLlarge 2
  have h₁ := mul_le_mul_of_nonneg_right hconst hLLpos.le
  have h₂ := mul_le_mul_of_nonneg_left hLLle (sq_nonneg (logScale N))
  nlinarith [h₁, h₂, pow_pos hLpos 2]

lemma eventually_KSafeReal_le_KReal :
    ∀ᶠ N : ℕ in atTop, KSafeReal N ≤ KReal N := by
  filter_upwards [eventually_pos_scales] with N hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hKnonneg : 0 ≤ KReal N := by
    exact div_nonneg hNpos.le
      (mul_nonneg (by positivity) (zero_le_one.trans hL.le))
  dsimp [KSafeReal]
  exact div_le_self hKnonneg hLL.le

lemma eventually_sqrt_logLogLog_le_logScale :
    ∀ᶠ N : ℕ in atTop,
      Real.sqrt (logLogLogScale N) ≤ logScale N := by
  filter_upwards [eventually_pos_scales] with N hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hLLLle : logLogLogScale N ≤ logLogScale N := by
    dsimp [logLogLogScale]
    exact (Real.log_le_sub_one_of_pos hLLpos).trans (by linarith)
  have hLLle : logLogScale N ≤ logScale N := by
    dsimp [logLogScale]
    exact (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hLLLleLsq : logLogLogScale N ≤ logScale N ^ 2 := by
    calc
      logLogLogScale N ≤ logScale N := hLLLle.trans hLLle
      _ ≤ logScale N ^ 2 := by nlinarith
  exact (Real.sqrt_le_iff).2 ⟨hLpos.le, hLLLleLsq⟩

lemma eventually_KReal_le_MReal :
    ∀ᶠ N : ℕ in atTop, KReal N ≤ MReal N := by
  filter_upwards [eventually_sqrt_logLogLog_le_logScale,
    eventually_pos_scales] with N hsqrt hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) :=
    Real.sqrt_pos.2 hLLL
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  dsimp [KReal, MReal]
  rw [div_le_div_iff_of_pos_left hNpos (mul_pos (by positivity) hLpos) hsqrtpos]
  nlinarith

lemma eventually_KSafeReal_le_MReal :
    ∀ᶠ N : ℕ in atTop, KSafeReal N ≤ MReal N := by
  filter_upwards [eventually_KSafeReal_le_KReal,
    eventually_KReal_le_MReal] with N hsafe hKM
  exact hsafe.trans hKM

lemma eventually_MReal_le_tenth :
    ∀ᶠ N : ℕ in atTop, MReal N ≤ (N : ℝ) / 10 := by
  have hlarge := tendsto_logLogLogScale.eventually_ge_atTop 100
  filter_upwards [hlarge, eventually_pos_scales] with N hlarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) :=
    Real.sqrt_pos.2 hLLL
  have hsqrt : 10 ≤ Real.sqrt (logLogLogScale N) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
    apply Real.sqrt_le_sqrt
    norm_num at hlarge ⊢
    exact hlarge
  dsimp [MReal]
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hsqrt

lemma eventually_SReal_le_M_term (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      SReal N ≤ MReal N ^ 2 / (C * (N : ℝ)) := by
  have hlarge := tendsto_logScale.eventually_ge_atTop (max 1 C)
  filter_upwards [hlarge, eventually_pos_scales] with N hL hpos
  rcases hpos with ⟨hNpos, hLone, hLL, hLLLpos⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hLone
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) := Real.sqrt_pos.2 hLLLpos
  have hLLLleL : logLogLogScale N ≤ logScale N := by
    have h₁ : logLogLogScale N ≤ logLogScale N := by
      dsimp [logLogLogScale]
      exact (Real.log_le_sub_one_of_pos hLLpos).trans (by linarith)
    have h₂ : logLogScale N ≤ logScale N := by
      dsimp [logLogScale]
      exact (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
    exact h₁.trans h₂
  have hCleL : C ≤ logScale N := (le_max_right 1 C).trans hL
  have hCLLL : C * logLogLogScale N ≤ logScale N ^ 4 := by
    calc
      C * logLogLogScale N ≤ logScale N * logScale N :=
        mul_le_mul hCleL hLLLleL hLLLpos.le hLpos.le
      _ ≤ logScale N ^ 4 := by
        rw [show logScale N * logScale N = logScale N ^ 2 by ring,
          show logScale N ^ 4 = logScale N ^ 2 * logScale N ^ 2 by ring]
        exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hLone.le)
  dsimp [SReal, MReal]
  rw [div_pow, Real.sq_sqrt hLLLpos.le]
  field_simp
  nlinarith

lemma eventually_logLog_pow_five_le_logScale (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      D * logLogScale N ^ 5 ≤ logScale N := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (5 : ℝ)) =o[atTop] (fun x : ℝ ↦ x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 5 (by norm_num : (0 : ℝ) < 1))
  have hcomp := (hlittle.comp_tendsto tendsto_logScale).bound (inv_pos.mpr hD)
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  simp only [Function.comp_apply] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg
      (show 0 ≤ Real.log (logScale N) by
        simpa [logLogScale] using zero_le_one.trans hLL.le) _),
    Real.norm_of_nonneg (zero_le_one.trans hL.le)] at hN
  have hraw : logLogScale N ^ 5 ≤ D⁻¹ * logScale N := by
    simpa [logLogScale, Real.rpow_natCast] using hN
  calc
    D * logLogScale N ^ 5 ≤ D * (D⁻¹ * logScale N) :=
      mul_le_mul_of_nonneg_left hraw hD.le
    _ = logScale N := by field_simp

lemma eventually_logLog_pow_six_le_logScale (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      D * logLogScale N ^ 6 ≤ logScale N := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (6 : ℝ)) =o[atTop] (fun x : ℝ ↦ x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 6 (by norm_num : (0 : ℝ) < 1))
  have hcomp := (hlittle.comp_tendsto tendsto_logScale).bound (inv_pos.mpr hD)
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  simp only [Function.comp_apply] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg
      (show 0 ≤ Real.log (logScale N) by
        simpa [logLogScale] using zero_le_one.trans hLL.le) _),
    Real.norm_of_nonneg (zero_le_one.trans hL.le)] at hN
  have hraw : logLogScale N ^ 6 ≤ D⁻¹ * logScale N := by
    simpa [logLogScale, Real.rpow_natCast] using hN
  calc
    D * logLogScale N ^ 6 ≤ D * (D⁻¹ * logScale N) :=
      mul_le_mul_of_nonneg_left hraw hD.le
    _ = logScale N := by field_simp

lemma eventually_logLog_pow_nine_le_logScale (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      D * logLogScale N ^ 9 ≤ logScale N := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (9 : ℝ)) =o[atTop] (fun x : ℝ ↦ x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 9 (by norm_num : (0 : ℝ) < 1))
  have hcomp := (hlittle.comp_tendsto tendsto_logScale).bound (inv_pos.mpr hD)
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  simp only [Function.comp_apply] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg
      (show 0 ≤ Real.log (logScale N) by
        simpa [logLogScale] using zero_le_one.trans hLL.le) _),
    Real.norm_of_nonneg (zero_le_one.trans hL.le)] at hN
  have hraw : logLogScale N ^ 9 ≤ D⁻¹ * logScale N := by
    simpa [logLogScale, Real.rpow_natCast] using hN
  calc
    D * logLogScale N ^ 9 ≤ D * (D⁻¹ * logScale N) :=
      mul_le_mul_of_nonneg_left hraw hD.le
    _ = logScale N := by field_simp

lemma eventually_SReal_le_K_term (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      SReal N ≤ KReal N ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 5) := by
  have hD : 0 < C * (10 : ℝ) ^ 21 := mul_pos hC (by positivity)
  have hlarge := eventually_logLog_pow_five_le_logScale (C * (10 : ℝ) ^ 21) hD
  filter_upwards [hlarge, eventually_pos_scales] with N hmain hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  dsimp [SReal, KReal]
  field_simp
  nlinarith

lemma eventually_SReal_le_min_terms (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      SReal N ≤ min (MReal N ^ 2 / (C * (N : ℝ)))
        (KReal N ^ 3 /
          (C * (N : ℝ) ^ 2 * logLogScale N ^ 5)) := by
  filter_upwards [eventually_SReal_le_M_term C hC,
    eventually_SReal_le_K_term C hC] with N hM hK
  exact le_min hM hK

/-- The chosen scales have enough slack for a sixth power of `log log N`. -/
lemma eventually_SReal_le_K_term_six (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      SReal N ≤ KReal N ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
  have hD : 0 < C * (10 : ℝ) ^ 21 := mul_pos hC (by positivity)
  have hlarge := eventually_logLog_pow_six_le_logScale
    (C * (10 : ℝ) ^ 21) hD
  filter_upwards [hlarge, eventually_pos_scales] with N hmain hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  dsimp [SReal, KReal]
  field_simp
  nlinarith

/-- Cleared-denominator form of `eventually_SReal_le_K_term_six`. -/
lemma eventually_SReal_mul_repaired_den_le_K_cube (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      SReal N * (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) ≤ KReal N ^ 3 := by
  filter_upwards [eventually_SReal_le_K_term_six C hC,
    eventually_pos_scales] with N hbound hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  exact (le_div_iff₀ (by positivity)).mp hbound

lemma eventually_KSafe_lower :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / logScale N ^ 10 ≤ KSafeReal N := by
  have hlarge := tendsto_logScale.eventually_ge_atTop 10
  filter_upwards [hlarge, eventually_logLogScale_le_logScale,
    eventually_pos_scales] with N hLlarge hLLle hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hconst : (10 : ℝ) ^ 7 ≤ logScale N ^ 8 := by
    calc
      (10 : ℝ) ^ 7 ≤ (10 : ℝ) ^ 8 := by norm_num
      _ ≤ logScale N ^ 8 := pow_le_pow_left₀ (by norm_num) hLlarge 8
  have hmul := mul_le_mul_of_nonneg_right hconst hLLpos.le
  have hLLmul := mul_le_mul_of_nonneg_left hLLle
    (pow_nonneg hLpos.le 8)
  dsimp [KSafeReal, KReal]
  field_simp
  nlinarith [hmul, hLLmul]

lemma eventually_two_mul_KSafe_lower :
    ∀ᶠ N : ℕ in atTop,
      2 * ((N : ℝ) / logScale N ^ 10) ≤ KSafeReal N := by
  have hlarge := tendsto_logScale.eventually_ge_atTop 20
  filter_upwards [hlarge, eventually_logLogScale_le_logScale,
    eventually_pos_scales] with N hLlarge hLLle hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hconst : 2 * (10 : ℝ) ^ 7 ≤ logScale N ^ 8 := by
    calc
      2 * (10 : ℝ) ^ 7 ≤ (20 : ℝ) ^ 8 := by norm_num
      _ ≤ logScale N ^ 8 := pow_le_pow_left₀ (by norm_num) hLlarge 8
  have hmul := mul_le_mul_of_nonneg_right hconst hLLpos.le
  have hLLmul := mul_le_mul_of_nonneg_left hLLle
    (pow_nonneg hLpos.le 8)
  dsimp [KSafeReal, KReal]
  field_simp
  nlinarith [hmul, hLLmul]

lemma eventually_SReal_le_KSafe_term_six (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      SReal N ≤ KSafeReal N ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
  have hD : 0 < C * (10 : ℝ) ^ 21 := mul_pos hC (by positivity)
  have hlarge := eventually_logLog_pow_nine_le_logScale
    (C * (10 : ℝ) ^ 21) hD
  filter_upwards [hlarge, eventually_pos_scales] with N hmain hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  dsimp [SReal, KSafeReal, KReal]
  field_simp
  nlinarith

lemma eventually_K_lower :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / logScale N ^ 10 ≤ KReal N := by
  have hlarge := tendsto_logScale.eventually_ge_atTop 10
  filter_upwards [hlarge, eventually_pos_scales] with N hL hpos
  rcases hpos with ⟨hNpos, hLone, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hLone
  dsimp [KReal]
  rw [div_le_div_iff_of_pos_left hNpos (pow_pos hLpos 10)
    (mul_pos (by positivity) hLpos)]
  have hpow : (10 : ℝ) ^ 7 ≤ logScale N ^ 9 := by
    calc
      (10 : ℝ) ^ 7 ≤ (10 : ℝ) ^ 9 := by norm_num
      _ ≤ logScale N ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
  nlinarith [pow_pos hLpos 8]

lemma eventually_two_mul_K_lower :
    ∀ᶠ N : ℕ in atTop,
      2 * ((N : ℝ) / logScale N ^ 10) ≤ KReal N := by
  have hlarge := tendsto_logScale.eventually_ge_atTop 20
  filter_upwards [hlarge, eventually_pos_scales] with N hL hpos
  rcases hpos with ⟨hNpos, hLone, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hLone
  have hfrac :
      (2 : ℝ) / logScale N ^ 10 ≤
        1 / ((10 : ℝ) ^ 7 * logScale N) := by
    rw [div_le_div_iff₀ (pow_pos hLpos 10) (mul_pos (by positivity) hLpos)]
    have hpow : 2 * (10 : ℝ) ^ 7 ≤ logScale N ^ 9 := by
      calc
        2 * (10 : ℝ) ^ 7 ≤ (20 : ℝ) ^ 9 := by norm_num
        _ ≤ logScale N ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
    nlinarith [pow_pos hLpos 8]
  dsimp [KReal]
  calc
    2 * ((N : ℝ) / logScale N ^ 10) =
        (N : ℝ) * (2 / logScale N ^ 10) := by ring
    _ ≤ (N : ℝ) * (1 / ((10 : ℝ) ^ 7 * logScale N)) :=
      mul_le_mul_of_nonneg_left hfrac hNpos.le
    _ = (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N) := by ring

lemma half_le_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor := Nat.lt_floor_add_one x
  linarith

lemma eventually_real_scales_ge_two :
    ∀ᶠ N : ℕ in atTop, 2 ≤ SReal N ∧ 2 ≤ KReal N ∧ 2 ≤ MReal N := by
  have hpow : Tendsto almostOnePower atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (9999 : ℝ) / 10000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_almostOnePower_le_SReal,
    eventually_SReal_le_KReal, eventually_KReal_le_MReal,
    hpow.eventually_ge_atTop 2] with N hNS hSK hKM htwo
  exact ⟨htwo.trans hNS, htwo.trans (hNS.trans hSK),
    htwo.trans (hNS.trans (hSK.trans hKM))⟩

lemma eventually_nat_scale_chain :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ (K N : ℝ) ∧ (K N : ℝ) ≤ (M N : ℝ) ∧
        (M N : ℝ) ≤ (N : ℝ) / 10 := by
  filter_upwards [eventually_SReal_le_KReal, eventually_KReal_le_MReal,
    eventually_MReal_le_tenth, eventually_pos_scales] with N hSK hKM hMN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hMnonneg : 0 ≤ MReal N := by
    exact div_nonneg hNpos.le (Real.sqrt_nonneg _)
  exact ⟨by exact_mod_cast Nat.floor_mono hSK,
    by exact_mod_cast Nat.floor_mono hKM,
    (Nat.floor_le hMnonneg).trans hMN⟩

lemma eventually_almostOnePower_le_natS :
    ∀ᶠ N : ℕ in atTop, almostOnePower N ≤ (S N : ℝ) := by
  filter_upwards [eventually_mul_almostOnePower_le_SReal 2 (by norm_num),
    eventually_real_scales_ge_two] with N htwo hlarge
  exact (show almostOnePower N ≤ SReal N / 2 by linarith).trans
    (half_le_floor hlarge.1)

lemma eventually_nat_K_lower :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / logScale N ^ 10 ≤ (K N : ℝ) := by
  filter_upwards [eventually_two_mul_K_lower,
    eventually_real_scales_ge_two] with N htwo hlarge
  exact (show (N : ℝ) / logScale N ^ 10 ≤ KReal N / 2 by linarith).trans
    (half_le_floor hlarge.2.1)

lemma eventually_nat_K_upper :
    ∀ᶠ N : ℕ in atTop,
      (K N : ℝ) ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N) := by
  filter_upwards [eventually_pos_scales] with N hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  exact Nat.floor_le (div_nonneg hNpos.le
    (mul_nonneg (by positivity) (zero_le_one.trans hL.le)))

lemma eventually_nat_S_le_M_term (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ (M N : ℝ) ^ 2 / (C * (N : ℝ)) := by
  have h4C : 0 < 4 * C := mul_pos (by norm_num) hC
  filter_upwards [eventually_SReal_le_M_term (4 * C) h4C,
    eventually_real_scales_ge_two, eventually_pos_scales] with N hreal hlarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hSnonneg : 0 ≤ SReal N := by
    exact div_nonneg hNpos.le (pow_nonneg (zero_le_one.trans hL.le) _)
  have hMhalf : MReal N / 2 ≤ (M N : ℝ) := half_le_floor hlarge.2.2
  have hMnonneg : 0 ≤ MReal N := by
    exact div_nonneg hNpos.le (Real.sqrt_nonneg _)
  have hMsq : MReal N ^ 2 ≤ 4 * (M N : ℝ) ^ 2 := by
    have hdiff : 0 ≤ 2 * (M N : ℝ) - MReal N := by linarith
    have hsum : 0 ≤ 2 * (M N : ℝ) + MReal N := by positivity
    nlinarith [mul_nonneg hdiff hsum]
  calc
    (S N : ℝ) ≤ SReal N := Nat.floor_le hSnonneg
    _ ≤ MReal N ^ 2 / ((4 * C) * (N : ℝ)) := hreal
    _ ≤ (M N : ℝ) ^ 2 / (C * (N : ℝ)) := by
      have hid :
          MReal N ^ 2 / ((4 * C) * (N : ℝ)) =
            (MReal N ^ 2 / 4) / (C * (N : ℝ)) := by
        field_simp
      rw [hid, div_le_div_iff_of_pos_right (mul_pos hC hNpos)]
      nlinarith

lemma eventually_nat_S_le_K_term (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ (K N : ℝ) ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 5) := by
  have h8C : 0 < 8 * C := mul_pos (by norm_num) hC
  filter_upwards [eventually_SReal_le_K_term (8 * C) h8C,
    eventually_real_scales_ge_two, eventually_pos_scales] with N hreal hlarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hSnonneg : 0 ≤ SReal N := by
    exact div_nonneg hNpos.le (pow_nonneg (zero_le_one.trans hL.le) _)
  have hKhalf : KReal N / 2 ≤ (K N : ℝ) := half_le_floor hlarge.2.1
  have hKnonneg : 0 ≤ KReal N := by
    exact div_nonneg hNpos.le
      (mul_nonneg (by positivity) (zero_le_one.trans hL.le))
  have hKcube : KReal N ^ 3 ≤ 8 * (K N : ℝ) ^ 3 := by
    have hKle : KReal N ≤ 2 * (K N : ℝ) := by linarith
    calc
      KReal N ^ 3 ≤ (2 * (K N : ℝ)) ^ 3 := pow_le_pow_left₀ hKnonneg hKle 3
      _ = 8 * (K N : ℝ) ^ 3 := by ring
  have hdenpos : 0 < C * (N : ℝ) ^ 2 * logLogScale N ^ 5 := by positivity
  calc
    (S N : ℝ) ≤ SReal N := Nat.floor_le hSnonneg
    _ ≤ KReal N ^ 3 /
        ((8 * C) * (N : ℝ) ^ 2 * logLogScale N ^ 5) := hreal
    _ ≤ (K N : ℝ) ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 5) := by
      have hid :
          KReal N ^ 3 / ((8 * C) * (N : ℝ) ^ 2 * logLogScale N ^ 5) =
            (KReal N ^ 3 / 8) /
              (C * (N : ℝ) ^ 2 * logLogScale N ^ 5) := by
        field_simp
      rw [hid, div_le_div_iff_of_pos_right hdenpos]
      nlinarith

lemma eventually_nat_S_le_min_terms (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ min ((M N : ℝ) ^ 2 / (C * (N : ℝ)))
        ((K N : ℝ) ^ 3 /
          (C * (N : ℝ) ^ 2 * logLogScale N ^ 5)) := by
  filter_upwards [eventually_nat_S_le_M_term C hC,
    eventually_nat_S_le_K_term C hC] with N hM hK
  exact le_min hM hK

lemma eventually_nat_S_le_K_term_six (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ (K N : ℝ) ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
  have h8C : 0 < 8 * C := mul_pos (by norm_num) hC
  filter_upwards [eventually_SReal_le_K_term_six (8 * C) h8C,
    eventually_real_scales_ge_two, eventually_pos_scales] with N hreal hlarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hSnonneg : 0 ≤ SReal N := by
    exact div_nonneg hNpos.le (pow_nonneg (zero_le_one.trans hL.le) _)
  have hKhalf : KReal N / 2 ≤ (K N : ℝ) := half_le_floor hlarge.2.1
  have hKnonneg : 0 ≤ KReal N := by
    exact div_nonneg hNpos.le
      (mul_nonneg (by positivity) (zero_le_one.trans hL.le))
  have hKcube : KReal N ^ 3 ≤ 8 * (K N : ℝ) ^ 3 := by
    have hKle : KReal N ≤ 2 * (K N : ℝ) := by linarith
    calc
      KReal N ^ 3 ≤ (2 * (K N : ℝ)) ^ 3 := pow_le_pow_left₀ hKnonneg hKle 3
      _ = 8 * (K N : ℝ) ^ 3 := by ring
  have hdenpos : 0 < C * (N : ℝ) ^ 2 * logLogScale N ^ 6 := by positivity
  calc
    (S N : ℝ) ≤ SReal N := Nat.floor_le hSnonneg
    _ ≤ KReal N ^ 3 /
        ((8 * C) * (N : ℝ) ^ 2 * logLogScale N ^ 6) := hreal
    _ ≤ (K N : ℝ) ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
      have hid :
          KReal N ^ 3 / ((8 * C) * (N : ℝ) ^ 2 * logLogScale N ^ 6) =
            (KReal N ^ 3 / 8) /
              (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
        field_simp
      rw [hid, div_le_div_iff_of_pos_right hdenpos]
      nlinarith

/-- Cleared-denominator natural-floor form of the repaired scale bound. -/
lemma eventually_nat_S_mul_repaired_den_le_K_cube (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) * (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) ≤ (K N : ℝ) ^ 3 := by
  filter_upwards [eventually_nat_S_le_K_term_six C hC,
    eventually_pos_scales] with N hbound hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  exact (le_div_iff₀ (by positivity)).mp hbound

lemma eventually_KSafeReal_ge_two :
    ∀ᶠ N : ℕ in atTop, 2 ≤ KSafeReal N := by
  filter_upwards [eventually_real_scales_ge_two,
    eventually_SReal_le_KSafeReal] with N hlarge hSK
  exact hlarge.1.trans hSK

lemma eventually_nat_safe_scale_chain :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ (KSafe N : ℝ) ∧
        (KSafe N : ℝ) ≤ (M N : ℝ) ∧
        (M N : ℝ) ≤ (N : ℝ) / 10 := by
  filter_upwards [eventually_SReal_le_KSafeReal,
    eventually_KSafeReal_le_MReal, eventually_MReal_le_tenth,
    eventually_pos_scales] with N hSK hKM hMN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hMnonneg : 0 ≤ MReal N :=
    div_nonneg hNpos.le (Real.sqrt_nonneg _)
  exact ⟨by exact_mod_cast Nat.floor_mono hSK,
    by exact_mod_cast Nat.floor_mono hKM,
    (Nat.floor_le hMnonneg).trans hMN⟩

lemma eventually_nat_KSafe_lower :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / logScale N ^ 10 ≤ (KSafe N : ℝ) := by
  filter_upwards [eventually_two_mul_KSafe_lower,
    eventually_KSafeReal_ge_two] with N htwo hlarge
  exact (show (N : ℝ) / logScale N ^ 10 ≤ KSafeReal N / 2 by linarith).trans
    (half_le_floor hlarge)

lemma eventually_nat_KSafe_upper :
    ∀ᶠ N : ℕ in atTop,
      (KSafe N : ℝ) ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N) := by
  filter_upwards [eventually_KSafeReal_le_KReal,
    eventually_pos_scales] with N hsafe hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hsafenonneg : 0 ≤ KSafeReal N := by
    dsimp [KSafeReal, KReal]
    positivity
  exact (Nat.floor_le hsafenonneg).trans (hsafe.trans_eq rfl)

lemma eventually_nat_S_le_KSafe_term_six (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) ≤ (KSafe N : ℝ) ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
  have h8C : 0 < 8 * C := mul_pos (by norm_num) hC
  filter_upwards [eventually_SReal_le_KSafe_term_six (8 * C) h8C,
    eventually_KSafeReal_ge_two, eventually_pos_scales] with N hreal hlarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hSnonneg : 0 ≤ SReal N := by
    exact div_nonneg hNpos.le (pow_nonneg (zero_le_one.trans hL.le) _)
  have hKhalf : KSafeReal N / 2 ≤ (KSafe N : ℝ) := half_le_floor hlarge
  have hKnonneg : 0 ≤ KSafeReal N := by
    dsimp [KSafeReal, KReal]
    positivity
  have hKcube : KSafeReal N ^ 3 ≤ 8 * (KSafe N : ℝ) ^ 3 := by
    have hKle : KSafeReal N ≤ 2 * (KSafe N : ℝ) := by linarith
    calc
      KSafeReal N ^ 3 ≤ (2 * (KSafe N : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hKnonneg hKle 3
      _ = 8 * (KSafe N : ℝ) ^ 3 := by ring
  have hdenpos : 0 < C * (N : ℝ) ^ 2 * logLogScale N ^ 6 := by positivity
  calc
    (S N : ℝ) ≤ SReal N := Nat.floor_le hSnonneg
    _ ≤ KSafeReal N ^ 3 /
        ((8 * C) * (N : ℝ) ^ 2 * logLogScale N ^ 6) := hreal
    _ ≤ (KSafe N : ℝ) ^ 3 /
        (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
      have hid :
          KSafeReal N ^ 3 / ((8 * C) * (N : ℝ) ^ 2 * logLogScale N ^ 6) =
            (KSafeReal N ^ 3 / 8) /
              (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) := by
        field_simp
      rw [hid, div_le_div_iff_of_pos_right hdenpos]
      nlinarith

lemma eventually_nat_S_mul_safe_repaired_den_le_KSafe_cube
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (S N : ℝ) * (C * (N : ℝ) ^ 2 * logLogScale N ^ 6) ≤
        (KSafe N : ℝ) ^ 3 := by
  filter_upwards [eventually_nat_S_le_KSafe_term_six C hC,
    eventually_pos_scales] with N hbound hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  exact (le_div_iff₀ (by positivity)).mp hbound

/-- All safe natural scale hypotheses, in one package for the local-limit
theorem. -/
theorem eventually_liuSafeNatScaleConditions (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, LiuSafeNatScaleConditions C N := by
  filter_upwards [eventually_almostOnePower_le_natS,
    eventually_nat_safe_scale_chain, eventually_nat_S_le_M_term C hC,
    eventually_nat_S_le_KSafe_term_six C hC, eventually_nat_KSafe_lower,
    eventually_nat_KSafe_upper] with N hNS hchain hSM hSK hKlower hKupper
  exact ⟨hNS, hchain.1, hchain.2.1, hchain.2.2,
    hSM, hSK, hKlower, hKupper⟩

lemma eventually_4000_mul_KSafe_mul_log_le_div :
    ∀ᶠ N : ℕ in atTop,
      4000 * (KSafe N : ℝ) * logScale N ≤ (N : ℝ) / 2000 := by
  filter_upwards [eventually_KSafeReal_ge_two,
    eventually_pos_scales] with N hsafeLarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hsafenonneg : 0 ≤ KSafeReal N := (by norm_num : (0 : ℝ) ≤ 2).trans hsafeLarge
  have hfloor : (KSafe N : ℝ) ≤ KSafeReal N := Nat.floor_le hsafenonneg
  calc
    4000 * (KSafe N : ℝ) * logScale N ≤
        4000 * KSafeReal N * logScale N := by gcongr
    _ = (N : ℝ) / (2500 * logLogScale N) := by
      dsimp [KSafeReal, KReal]
      field_simp
      norm_num
    _ ≤ (N : ℝ) / 2000 := by
      rw [div_le_div_iff_of_pos_left hNpos (by positivity) (by norm_num)]
      nlinarith

lemma eventually_dyadicMultiplierScale_ge_logLog :
  ∀ᶠ N : ℕ in atTop,
      2500 * logLogScale N ≤ dyadicMultiplierScale N := by
  filter_upwards [eventually_KSafeReal_ge_two,
    eventually_pos_scales] with N hsafeLarge hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hsafenonneg : 0 ≤ KSafeReal N := (by norm_num : (0 : ℝ) ≤ 2).trans hsafeLarge
  have hfloor : (KSafe N : ℝ) ≤ KSafeReal N := Nat.floor_le hsafenonneg
  have hKSafePos : (0 : ℝ) < KSafe N := by
    have hhalf := half_le_floor hsafeLarge
    have hsafepos : 0 < KSafeReal N := (by norm_num : (0 : ℝ) < 2).trans_le hsafeLarge
    exact (div_pos hsafepos (by norm_num)).trans_le hhalf
  dsimp [dyadicMultiplierScale]
  rw [le_div_iff₀ (by positivity)]
  calc
    2500 * logLogScale N * (4000 * (KSafe N : ℝ) * logScale N) ≤
        2500 * logLogScale N * (4000 * KSafeReal N * logScale N) := by
      gcongr
    _ = (N : ℝ) := by
      dsimp [KSafeReal, KReal]
      field_simp
      norm_num

/-- The dyadic multiplier range left by `KSafe` grows without bound. -/
theorem tendsto_dyadicMultiplierScale :
    Tendsto dyadicMultiplierScale atTop atTop := by
  exact tendsto_atTop_mono' atTop eventually_dyadicMultiplierScale_ge_logLog
    (tendsto_logLogScale.const_mul_atTop (by norm_num : (0 : ℝ) < 2500))

lemma eventually_log_pow_ten_le_almostOnePower :
    ∀ᶠ N : ℕ in atTop, logScale N ^ 10 ≤ almostOnePower N := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (10 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ ((9999 : ℝ) / 10000)) :=
    isLittleO_log_rpow_rpow_atTop 10 (by norm_num)
  have hcomp := (hlittle.comp_tendsto tendsto_natCast_atTop_atTop).bound one_pos
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hlognonneg : 0 ≤ Real.log (N : ℝ) := by
    simpa [logScale] using zero_le_one.trans hL.le
  simp only [Function.comp_apply, one_mul] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  simpa [logScale, almostOnePower, Real.rpow_natCast] using hN

/-- The safe factorization cutoff is large enough that every `d ≥ KSafe N`
has complementary factor at most the smoothness cutoff. -/
lemma eventually_N_div_KSafe_le_S :
    ∀ᶠ N : ℕ in atTop, N / KSafe N ≤ S N := by
  filter_upwards [eventually_nat_KSafe_lower,
    eventually_KSafeReal_ge_two, eventually_log_pow_ten_le_almostOnePower,
    eventually_almostOnePower_le_natS, eventually_pos_scales] with N hKlower
      hsafeLarge hlog hNS hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hL
  have hhalf := half_le_floor hsafeLarge
  have hsafepos : 0 < KSafeReal N := (by norm_num : (0 : ℝ) < 2).trans_le hsafeLarge
  have hKpos : (0 : ℝ) < KSafe N :=
    (div_pos hsafepos (by norm_num)).trans_le hhalf
  have hcross : (N : ℝ) ≤ (KSafe N : ℝ) * logScale N ^ 10 := by
    exact (div_le_iff₀ (pow_pos hLpos 10)).mp hKlower
  have hrealDiv : (N : ℝ) / (KSafe N : ℝ) ≤ logScale N ^ 10 := by
    rw [div_le_iff₀ hKpos]
    simpa [mul_comm] using hcross
  have hcast : ((N / KSafe N : ℕ) : ℝ) ≤ (S N : ℝ) :=
    Nat.cast_div_le.trans (hrealDiv.trans (hlog.trans hNS))
  exact_mod_cast hcast

/-- The floored denominator lower endpoint is `o(N)`. -/
lemma tendsto_M_div :
    Tendsto (fun N : ℕ ↦ (M N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hmajor :
      Tendsto (fun N : ℕ ↦ (Real.sqrt (logLogLogScale N))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_logLogLogScale)
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_pos_scales] with N hpos
    rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
    have hMnonneg : 0 ≤ MReal N :=
      div_nonneg hNpos.le (Real.sqrt_nonneg _)
    calc
      (M N : ℝ) / (N : ℝ) ≤ MReal N / (N : ℝ) :=
        div_le_div_of_nonneg_right (Nat.floor_le hMnonneg) hNpos.le
      _ = (Real.sqrt (logLogLogScale N))⁻¹ := by
        dsimp [MReal]
        field_simp
  · exact hmajor

/-- The floored prime-power cutoff is `o(N)`. -/
lemma tendsto_S_div :
    Tendsto (fun N : ℕ ↦ (S N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ ↦ x ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hmajor :
      Tendsto (fun N : ℕ ↦ (logScale N ^ 4)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (hpow.comp tendsto_logScale)
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_pos_scales] with N hpos
    rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
    have hSnonneg : 0 ≤ SReal N :=
      div_nonneg hNpos.le (pow_nonneg (zero_le_one.trans hL.le) _)
    calc
      (S N : ℝ) / (N : ℝ) ≤ SReal N / (N : ℝ) :=
        div_le_div_of_nonneg_right (Nat.floor_le hSnonneg) hNpos.le
      _ = (logScale N ^ 4)⁻¹ := by
        dsimp [SReal]
        field_simp
  · exact hmajor

lemma eventually_one_le_M : ∀ᶠ N : ℕ in atTop, 1 ≤ M N := by
  filter_upwards [eventually_real_scales_ge_two] with N hlarge
  have hhalf := half_le_floor hlarge.2.2
  have hcast : (1 : ℝ) ≤ (⌊MReal N⌋₊ : ℝ) := by linarith
  exact_mod_cast hcast

lemma eventually_M_le_N : ∀ᶠ N : ℕ in atTop, M N ≤ N := by
  filter_upwards [eventually_nat_scale_chain,
    eventually_pos_scales] with N hchain hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  exact_mod_cast hchain.2.2.trans
    (div_le_self hNpos.le (by norm_num : (1 : ℝ) ≤ 10))

lemma eventually_one_le_M_and_M_le_N :
    ∀ᶠ N : ℕ in atTop, 1 ≤ M N ∧ M N ≤ N :=
  eventually_one_le_M.and eventually_M_le_N

/-- After flooring the three source scales, every hypothesis of
Liu--Sawhney, Proposition 3.2, still holds eventually. -/
theorem eventually_liuNatScaleConditions (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, LiuNatScaleConditions C N := by
  filter_upwards [eventually_almostOnePower_le_natS,
    eventually_nat_scale_chain, eventually_nat_S_le_M_term C hC,
    eventually_nat_S_le_K_term C hC, eventually_nat_K_lower,
    eventually_nat_K_upper] with N hNS hchain hSM hSK3 hKlower hKupper
  exact ⟨hNS, hchain.1, hchain.2.1, hchain.2.2, hSM, hSK3, hKlower, hKupper⟩

theorem eventually_liuNatScaleConditionsSix (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, LiuNatScaleConditionsSix C N := by
  filter_upwards [eventually_liuNatScaleConditions C hC,
    eventually_nat_S_le_K_term_six C hC] with N hsource hrepaired
  exact ⟨hsource, hrepaired⟩

/-- The complete collection of scale inequalities needed to invoke
Liu--Sawhney, Proposition 3.2, holds for every fixed positive constant `C`. -/
theorem eventually_liuScaleConditions (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, LiuScaleConditions C N := by
  filter_upwards [eventually_almostOnePower_le_SReal,
    eventually_SReal_le_KReal, eventually_KReal_le_MReal,
    eventually_MReal_le_tenth, eventually_SReal_le_M_term C hC,
    eventually_SReal_le_K_term C hC, eventually_K_lower] with N hNS hSK hKM hMN
      hSM hSK3 hKlower
  exact ⟨hNS, hSK, hKM, hMN, hSM, hSK3, hKlower, le_rfl⟩

theorem eventually_liuScaleConditionsSix (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, LiuScaleConditionsSix C N := by
  filter_upwards [eventually_liuScaleConditions C hC,
    eventually_SReal_le_K_term_six C hC] with N hsource hrepaired
  exact ⟨hsource, hrepaired⟩

end Erdos297
