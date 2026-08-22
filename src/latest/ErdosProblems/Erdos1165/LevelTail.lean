/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Basic
import ErdosProblems.Erdos1165.Clock

/-!
# The level-time cutoff for Erdős Problem 1165

This file isolates the deduction of HLOZ Lemma 2.6 from the lower-deviation
estimate in their Proposition 1.3.  Proposition 1.3 is *not* asserted: it is
an explicit parameter of the final implication.  The cutoff algebra and the
pathwise inclusion of the late level event in a lower-deviation event are
proved here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace Erdos1165

/-! ## The HLOZ cutoff and lower-deviation event -/

/-- The exponent `8/5 + δ` in HLOZ Proposition 1.3. -/
noncomputable def levelTailExponent (δ : ℝ) : ℝ := 8 / 5 + δ

/-- The leading term `√(πm)` in `log ψₘ`. -/
noncomputable def levelCutoffLeading (m : ℕ) : ℝ :=
  Real.sqrt (Real.pi * (m : ℝ))

/-- The correction in `log ψₘ`, written in a form which makes the cancellation
in the proof transparent: `π (√(πm))^(3/5+δ)`. -/
noncomputable def levelCutoffCorrection (δ : ℝ) (m : ℕ) : ℝ :=
  Real.pi * levelCutoffLeading m ^ (levelTailExponent δ - 1)

/-- The logarithm of HLOZ's deterministic cutoff `ψₘ(δ)`. -/
noncomputable def levelCutoffLog (δ : ℝ) (m : ℕ) : ℝ :=
  levelCutoffLeading m + levelCutoffCorrection δ m

/-- HLOZ's real-valued cutoff `ψₘ(δ)`. -/
noncomputable def levelCutoff (δ : ℝ) (m : ℕ) : ℝ :=
  Real.exp (levelCutoffLog δ m)

/-- The natural time at which Proposition 1.3 is applied.  Taking the ceiling
is the exact interpretation of the paper's comparison of the integer-valued
stopping time with the real number `ψₘ`. -/
noncomputable def levelCutoffTime (δ : ℝ) (m : ℕ) : ℕ :=
  ⌈levelCutoff δ m⌉₊

/-- The lower-deviation threshold from Proposition 1.3. -/
noncomputable def lowerDeviationThreshold (δ : ℝ) (n : ℕ) : ℝ :=
  Real.log n ^ 2 / Real.pi - Real.log n ^ levelTailExponent δ

/-- The event in which the level-`m` favorite configuration occurs, but the
creation of its `k`-th site is later than the real cutoff `ψₘ`.  Since the
stopping time is integer-valued, `ψₘ < T` is represented exactly by
`⌊ψₘ⌋ < T`. -/
def lateLevelSet (δ : ℝ) (m k : ℕ) : Set WalkPath :=
  {s | (⌊levelCutoff δ m⌋₊ : WithTop ℕ) < thresholdTime s m k ∧
    levelFavorite s m k}

/-- The lower-deviation event at a deterministic time. -/
def lowerDeviationSet (δ : ℝ) (n : ℕ) : Set WalkPath :=
  {s | (maxLocalTime s n : ℝ) < lowerDeviationThreshold δ n}

lemma levelCutoffLeading_nonneg (m : ℕ) : 0 ≤ levelCutoffLeading m := by
  exact Real.sqrt_nonneg _

lemma levelCutoffLeading_pos {m : ℕ} (hm : 0 < m) : 0 < levelCutoffLeading m := by
  rw [levelCutoffLeading]
  positivity

lemma levelCutoffLeading_sq (m : ℕ) : levelCutoffLeading m ^ 2 = Real.pi * m := by
  rw [levelCutoffLeading, Real.sq_sqrt (by positivity)]

/-- The leading term in the notation used in HLOZ (2.20). -/
lemma levelCutoffLeading_eq_hloz (m : ℕ) :
    levelCutoffLeading m = Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) := by
  rw [levelCutoffLeading, Real.sqrt_eq_rpow]
  exact Real.mul_rpow Real.pi_pos.le (Nat.cast_nonneg m)

/-- Our cancellation-friendly definition of the correction is exactly the
second term displayed in HLOZ (2.20). -/
lemma levelCutoffCorrection_eq_hloz (δ : ℝ) {m : ℕ} (hm : 0 < m) :
    levelCutoffCorrection δ m =
      Real.pi ^ (13 / 10 + δ / 2 : ℝ) *
        (m : ℝ) ^ (3 / 10 + δ / 2 : ℝ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  rw [levelCutoffCorrection, levelCutoffLeading_eq_hloz]
  rw [Real.mul_rpow (Real.rpow_nonneg hpi.le _) (Real.rpow_nonneg hmReal.le _)]
  rw [← Real.rpow_mul hpi.le, ← Real.rpow_mul hmReal.le]
  have hpiCombine : Real.pi *
        Real.pi ^ ((1 / 2 : ℝ) * (levelTailExponent δ - 1)) =
      Real.pi ^ (13 / 10 + δ / 2 : ℝ) := by
    calc
      Real.pi * Real.pi ^ ((1 / 2 : ℝ) * (levelTailExponent δ - 1)) =
          Real.pi ^ (1 : ℝ) *
            Real.pi ^ ((1 / 2 : ℝ) * (levelTailExponent δ - 1)) := by
        rw [Real.rpow_one]
      _ = Real.pi ^ (1 + (1 / 2 : ℝ) * (levelTailExponent δ - 1)) :=
        (Real.rpow_add hpi _ _).symm
      _ = Real.pi ^ (13 / 10 + δ / 2 : ℝ) := by
        congr 1
        unfold levelTailExponent
        ring
  have hmExponent : (m : ℝ) ^ ((1 / 2 : ℝ) * (levelTailExponent δ - 1)) =
      (m : ℝ) ^ (3 / 10 + δ / 2 : ℝ) := by
    congr 1
    unfold levelTailExponent
    ring
  rw [hmExponent]
  calc
    Real.pi *
        (Real.pi ^ ((1 / 2 : ℝ) * (levelTailExponent δ - 1)) *
          (m : ℝ) ^ (3 / 10 + δ / 2 : ℝ)) =
      (Real.pi * Real.pi ^ ((1 / 2 : ℝ) * (levelTailExponent δ - 1))) *
        (m : ℝ) ^ (3 / 10 + δ / 2 : ℝ) := by ring
    _ = _ := by rw [hpiCombine]

lemma levelCutoffLog_eq_hloz (δ : ℝ) {m : ℕ} (hm : 0 < m) :
    levelCutoffLog δ m =
      Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) +
        Real.pi ^ (13 / 10 + δ / 2 : ℝ) *
          (m : ℝ) ^ (3 / 10 + δ / 2 : ℝ) := by
  rw [levelCutoffLog, levelCutoffLeading_eq_hloz,
    levelCutoffCorrection_eq_hloz δ hm]

lemma levelCutoffCorrection_nonneg (δ : ℝ) (m : ℕ) :
    0 ≤ levelCutoffCorrection δ m := by
  exact mul_nonneg Real.pi_pos.le
    (Real.rpow_nonneg (levelCutoffLeading_nonneg m) _)

lemma levelCutoffLog_nonneg (δ : ℝ) (m : ℕ) : 0 ≤ levelCutoffLog δ m := by
  exact add_nonneg (levelCutoffLeading_nonneg m) (levelCutoffCorrection_nonneg δ m)

lemma levelCutoffTime_pos (δ : ℝ) (m : ℕ) : 0 < levelCutoffTime δ m := by
  rw [levelCutoffTime, levelCutoff]
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

lemma levelCutoffLog_le_log_time (δ : ℝ) (m : ℕ) :
    levelCutoffLog δ m ≤ Real.log (levelCutoffTime δ m) := by
  have hceil : Real.exp (levelCutoffLog δ m) ≤ (levelCutoffTime δ m : ℝ) := by
    exact Nat.le_ceil _
  have hlog := Real.log_le_log (Real.exp_pos (levelCutoffLog δ m)) hceil
  simpa using hlog

lemma log_levelCutoffTime_lt (δ : ℝ) (m : ℕ) :
    Real.log (levelCutoffTime δ m) < levelCutoffLog δ m + 1 := by
  have hceil : (levelCutoffTime δ m : ℝ) <
      Real.exp (levelCutoffLog δ m) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  have hexpOne : 1 ≤ Real.exp (levelCutoffLog δ m) :=
    (Real.one_le_exp_iff.mpr (levelCutoffLog_nonneg δ m))
  have htwo : Real.exp (levelCutoffLog δ m) + 1 ≤
      2 * Real.exp (levelCutoffLog δ m) := by linarith
  have htimePos : (0 : ℝ) < levelCutoffTime δ m := by
    exact_mod_cast levelCutoffTime_pos δ m
  have hlog := Real.log_lt_log htimePos (hceil.trans_le htwo)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hlogTwo : Real.log 2 < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  linarith

lemma tendsto_levelCutoffLeading :
    Tendsto (fun m : ℕ ↦ levelCutoffLeading m) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos)

lemma levelCutoffLeading_mul_correction_div_pi {δ : ℝ} {m : ℕ} (hm : 0 < m) :
    levelCutoffLeading m * levelCutoffCorrection δ m / Real.pi =
      levelCutoffLeading m ^ levelTailExponent δ := by
  have ha : 0 < levelCutoffLeading m := levelCutoffLeading_pos hm
  rw [levelCutoffCorrection]
  calc
    levelCutoffLeading m *
          (Real.pi * levelCutoffLeading m ^ (levelTailExponent δ - 1)) / Real.pi =
        levelCutoffLeading m *
          levelCutoffLeading m ^ (levelTailExponent δ - 1) := by
      field_simp [Real.pi_ne_zero]
    _ = levelCutoffLeading m ^ (1 + (levelTailExponent δ - 1)) := by
      rw [Real.rpow_add ha, Real.rpow_one]
    _ = levelCutoffLeading m ^ levelTailExponent δ := by ring_nf

lemma eventually_levelCutoffCorrection_le (δ : ℝ)
    (hδ : δ < 2 / 5) :
    ∀ᶠ m : ℕ in atTop,
      levelCutoffCorrection δ m ≤ levelCutoffLeading m / 20 := by
  have hq : levelTailExponent δ < 2 := by
    unfold levelTailExponent
    linarith
  have hpow : Tendsto
      (fun m : ℕ ↦ levelCutoffLeading m ^ (levelTailExponent δ - 2))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hq)).comp tendsto_levelCutoffLeading
    apply h.congr'
    filter_upwards [] with m
    change levelCutoffLeading m ^ (-(2 - levelTailExponent δ)) =
      levelCutoffLeading m ^ (levelTailExponent δ - 2)
    congr 1
    ring
  have hscaled : Tendsto
      (fun m : ℕ ↦ Real.pi * levelCutoffLeading m ^ (levelTailExponent δ - 2))
      atTop (𝓝 0) := by
    simpa using (show Tendsto
      (fun m : ℕ ↦ Real.pi * levelCutoffLeading m ^ (levelTailExponent δ - 2))
      atTop (𝓝 (Real.pi * 0)) from
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Real.pi) atTop (𝓝 Real.pi)).mul hpow)
  have hsmall : ∀ᶠ m : ℕ in atTop,
      Real.pi * levelCutoffLeading m ^ (levelTailExponent δ - 2) < 1 / 20 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num))
  have hpositive : ∀ᶠ m : ℕ in atTop, 0 < levelCutoffLeading m :=
    tendsto_levelCutoffLeading.eventually (eventually_gt_atTop 0)
  filter_upwards [hsmall, hpositive] with m hsmallm ham
  rw [levelCutoffCorrection]
  have hpowSplit :
      levelCutoffLeading m ^ (levelTailExponent δ - 1) =
        levelCutoffLeading m ^ (levelTailExponent δ - 2) * levelCutoffLeading m := by
    calc
      levelCutoffLeading m ^ (levelTailExponent δ - 1) =
          levelCutoffLeading m ^ ((levelTailExponent δ - 2) + 1) := by ring_nf
      _ = levelCutoffLeading m ^ (levelTailExponent δ - 2) *
          levelCutoffLeading m ^ 1 := Real.rpow_add ham _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpowSplit]
  calc
    Real.pi *
          (levelCutoffLeading m ^ (levelTailExponent δ - 2) *
            levelCutoffLeading m) =
        (Real.pi * levelCutoffLeading m ^ (levelTailExponent δ - 2)) *
          levelCutoffLeading m := by ring
    _ ≤ (1 / 20) * levelCutoffLeading m :=
      mul_le_mul_of_nonneg_right hsmallm.le ham.le
    _ = levelCutoffLeading m / 20 := by ring

/-- The exact cutoff inequality used in HLOZ Lemma 2.6.  The restriction
`δ < 2/5` is the range in which the displayed correction is lower order than
the leading `√m` term.  An arbitrary positive parameter is reduced to this
range below by monotonicity of the cutoff. -/
theorem eventually_lt_lowerDeviationThreshold_at_levelCutoff (δ : ℝ)
    (hδpos : 0 < δ) (hδlt : δ < 2 / 5) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < lowerDeviationThreshold δ (levelCutoffTime δ m) := by
  have hcorrection := eventually_levelCutoffCorrection_le δ hδlt
  have hleading : ∀ᶠ m : ℕ in atTop, 20 ≤ levelCutoffLeading m :=
    tendsto_levelCutoffLeading.eventually (eventually_ge_atTop 20)
  filter_upwards [hcorrection, hleading] with m hb ha20
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst m
    norm_num [levelCutoffLeading] at ha20
  let a : ℝ := levelCutoffLeading m
  let b : ℝ := levelCutoffCorrection δ m
  let q : ℝ := levelTailExponent δ
  let y : ℝ := Real.log (levelCutoffTime δ m)
  have ha : 0 < a := levelCutoffLeading_pos hm
  have hb0 : 0 ≤ b := levelCutoffCorrection_nonneg δ m
  have hq0 : 0 < q := by
    dsimp [q, levelTailExponent]
    linarith
  have hq2 : q < 2 := by
    dsimp [q, levelTailExponent]
    linarith
  have hlogLower : a + b ≤ y := by
    simpa [a, b, y, levelCutoffLog] using levelCutoffLog_le_log_time δ m
  have hlogUpper : y < a + b + 1 := by
    simpa [a, b, y, levelCutoffLog, add_assoc] using log_levelCutoffTime_lt δ m
  have hone : (1 : ℝ) ≤ a / 20 := by
    dsimp [a]
    linarith
  have hbSmall : b ≤ a / 20 := by simpa [a, b] using hb
  have hy0 : 0 ≤ y := (add_nonneg ha.le hb0).trans hlogLower
  have hyUpper : y < (11 / 10 : ℝ) * a := by
    linarith
  have hbasePow : (11 / 10 : ℝ) ^ q ≤ (11 / 10 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2.le
  have haq0 : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  have hyPow : y ^ q < 2 * a ^ q := by
    calc
      y ^ q < ((11 / 10 : ℝ) * a) ^ q :=
        Real.rpow_lt_rpow hy0 hyUpper hq0
      _ = (11 / 10 : ℝ) ^ q * a ^ q :=
        Real.mul_rpow (by norm_num) ha.le
      _ ≤ (11 / 10 : ℝ) ^ (2 : ℝ) * a ^ q :=
        mul_le_mul_of_nonneg_right hbasePow haq0.le
      _ < 2 * a ^ q := by
        rw [Real.rpow_two]
        norm_num
        nlinarith
  have haSq : a ^ 2 = Real.pi * (m : ℝ) := by
    simpa [a] using levelCutoffLeading_sq m
  have hcross : a * b / Real.pi = a ^ q := by
    simpa [a, b, q] using
      (levelCutoffLeading_mul_correction_div_pi (δ := δ) (m := m) hm)
  have hab : a * b = Real.pi * a ^ q := by
    have h := (div_eq_iff Real.pi_ne_zero).mp hcross
    simpa [mul_comm] using h
  have hsumSq : (a + b) ^ 2 / Real.pi =
      (m : ℝ) + 2 * a ^ q + b ^ 2 / Real.pi := by
    field_simp [Real.pi_ne_zero]
    nlinarith
  have hsum_le_y_sq : (a + b) ^ 2 ≤ y ^ 2 := by
    nlinarith
  have hquad : (m : ℝ) + 2 * a ^ q ≤ y ^ 2 / Real.pi := by
    have hdiv : (a + b) ^ 2 / Real.pi ≤ y ^ 2 / Real.pi :=
      div_le_div_of_nonneg_right hsum_le_y_sq Real.pi_pos.le
    rw [hsumSq] at hdiv
    have hbSq : 0 ≤ b ^ 2 / Real.pi := div_nonneg (sq_nonneg b) Real.pi_pos.le
    linarith
  change (m : ℝ) < y ^ 2 / Real.pi - y ^ q
  linarith

/-! ## Monotonicity and the double-exponential tail -/

lemma one_lt_levelCutoffLeading {m : ℕ} (hm : 1 ≤ m) :
    1 < levelCutoffLeading m := by
  rw [levelCutoffLeading, Real.lt_sqrt (by norm_num)]
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [Real.pi_gt_three]

lemma levelCutoffLog_mono_parameter {ε δ : ℝ} (hεδ : ε ≤ δ) {m : ℕ} (hm : 1 ≤ m) :
    levelCutoffLog ε m ≤ levelCutoffLog δ m := by
  have ha : 1 ≤ levelCutoffLeading m := (one_lt_levelCutoffLeading hm).le
  have hq : levelTailExponent ε - 1 ≤ levelTailExponent δ - 1 := by
    unfold levelTailExponent
    linarith
  have hpow : levelCutoffLeading m ^ (levelTailExponent ε - 1) ≤
      levelCutoffLeading m ^ (levelTailExponent δ - 1) :=
    Real.rpow_le_rpow_of_exponent_le ha hq
  unfold levelCutoffLog levelCutoffCorrection
  exact add_le_add_right (mul_le_mul_of_nonneg_left hpow Real.pi_pos.le) _

lemma levelCutoffTime_mono_parameter {ε δ : ℝ} (hεδ : ε ≤ δ) {m : ℕ} (hm : 1 ≤ m) :
    levelCutoffTime ε m ≤ levelCutoffTime δ m := by
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (levelCutoffLog_mono_parameter hεδ hm))

lemma lateLevelSet_mono_parameter {ε δ : ℝ} (hεδ : ε ≤ δ) {m k : ℕ} (hm : 1 ≤ m) :
    lateLevelSet δ m k ⊆ lateLevelSet ε m k := by
  intro s hs
  have hreal : levelCutoff ε m ≤ levelCutoff δ m := by
    exact Real.exp_le_exp.mpr (levelCutoffLog_mono_parameter hεδ hm)
  have hfloor : ⌊levelCutoff ε m⌋₊ ≤ ⌊levelCutoff δ m⌋₊ := Nat.floor_mono hreal
  have hfloorTop : (⌊levelCutoff ε m⌋₊ : WithTop ℕ) ≤ ⌊levelCutoff δ m⌋₊ := by
    exact_mod_cast hfloor
  exact ⟨hfloorTop.trans_lt hs.1, hs.2⟩

lemma tendsto_levelCutoffTime (δ : ℝ) :
    Tendsto (levelCutoffTime δ) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  have hlead : ∀ᶠ m : ℕ in atTop, (N : ℝ) ≤ levelCutoffLeading m :=
    tendsto_levelCutoffLeading.eventually (eventually_ge_atTop (N : ℝ))
  filter_upwards [hlead] with m hm
  have hlog : levelCutoffLeading m ≤ levelCutoffLog δ m := by
    unfold levelCutoffLog
    exact le_add_of_nonneg_right (levelCutoffCorrection_nonneg δ m)
  have hlogExp : levelCutoffLog δ m ≤ Real.exp (levelCutoffLog δ m) := by
    linarith [Real.add_one_le_exp (levelCutoffLog δ m)]
  have hceil : Real.exp (levelCutoffLog δ m) ≤ (levelCutoffTime δ m : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hm.trans (hlog.trans (hlogExp.trans hceil))

/-- The double exponential in Proposition 1.3 dominates `exp(-m)` after
substitution of the HLOZ cutoff. -/
lemma eventually_prop13_bound_le_exp_neg_level (δ C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      C * Real.exp
          (-Real.exp (Real.log (levelCutoffTime δ m) ^ (3 / 5 : ℝ))) ≤
        Real.exp (-(m : ℝ)) := by
  have hzTop : Tendsto
      (fun m : ℕ ↦ levelCutoffLeading m ^ (3 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp
      tendsto_levelCutoffLeading
  have hratio : Tendsto
      (fun m : ℕ ↦
        Real.exp (levelCutoffLeading m ^ (3 / 5 : ℝ)) /
          (levelCutoffLeading m ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ))
      atTop atTop :=
    (tendsto_exp_div_rpow_atTop (10 / 3 : ℝ)).comp hzTop
  have hratioLarge : ∀ᶠ m : ℕ in atTop,
      2 / Real.pi ≤
        Real.exp (levelCutoffLeading m ^ (3 / 5 : ℝ)) /
          (levelCutoffLeading m ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) :=
    hratio.eventually (eventually_ge_atTop (2 / Real.pi))
  have hmPos : ∀ᶠ m : ℕ in atTop, 0 < m := eventually_gt_atTop 0
  have hmLog : ∀ᶠ m : ℕ in atTop, |Real.log C| ≤ (m : ℝ) := by
    have hnat : ∀ᶠ m : ℕ in atTop, ⌈|Real.log C|⌉₊ ≤ m :=
      eventually_ge_atTop ⌈|Real.log C|⌉₊
    filter_upwards [hnat] with m hm
    exact (Nat.le_ceil _).trans (by exact_mod_cast hm)
  filter_upwards [hratioLarge, hmPos, hmLog] with m hratioM hm hmLogM
  let a : ℝ := levelCutoffLeading m
  let z : ℝ := a ^ (3 / 5 : ℝ)
  let y : ℝ := Real.log (levelCutoffTime δ m)
  have ha : 0 < a := levelCutoffLeading_pos hm
  have hz : 0 < z := Real.rpow_pos_of_pos ha _
  have hzPow : z ^ (10 / 3 : ℝ) = a ^ 2 := by
    dsimp [z]
    rw [← Real.rpow_mul ha.le]
    norm_num
  have htwoM : 2 * (m : ℝ) ≤ Real.exp z := by
    have hmul := (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mp hratioM
    rw [hzPow] at hmul
    have haSq : a ^ 2 = Real.pi * (m : ℝ) := by
      simpa [a] using levelCutoffLeading_sq m
    rw [haSq] at hmul
    have hpi : 0 < Real.pi := Real.pi_pos
    calc
      2 * (m : ℝ) = (2 / Real.pi) * (Real.pi * (m : ℝ)) := by field_simp
      _ ≤ Real.exp z := hmul
  have hay : a ≤ y := by
    have := levelCutoffLog_le_log_time δ m
    unfold levelCutoffLog at this
    exact (le_add_of_nonneg_right (levelCutoffCorrection_nonneg δ m)).trans this
  have hy0 : 0 ≤ y := ha.le.trans hay
  have hzle : z ≤ y ^ (3 / 5 : ℝ) := by
    exact Real.rpow_le_rpow ha.le hay (by norm_num)
  have hexpTwo : 2 * (m : ℝ) ≤ Real.exp (y ^ (3 / 5 : ℝ)) :=
    htwoM.trans (Real.exp_le_exp.mpr hzle)
  have hlogC : Real.log C ≤ (m : ℝ) := (le_abs_self _).trans hmLogM
  have hexponent : Real.log C - Real.exp (y ^ (3 / 5 : ℝ)) ≤ -(m : ℝ) := by
    linarith
  calc
    C * Real.exp (-Real.exp (y ^ (3 / 5 : ℝ))) =
        Real.exp (Real.log C - Real.exp (y ^ (3 / 5 : ℝ))) := by
      nth_rewrite 1 [← Real.exp_log hC]
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.mpr hexponent

/-! ## The pathwise event inclusion -/

/-- Before the first time a site reaches level `m+1`, the maximal local time
is at most `m`. -/
theorem maxLocalTime_le_of_time_lt_nextThreshold (s : WalkPath) (m n : ℕ)
    (hbefore : (n : WithTop ℕ) < thresholdTime s (m + 1) 1) :
    maxLocalTime s n ≤ m := by
  rw [← thresholdCount_succ_level_eq_zero_iff]
  by_contra hne
  have hpositive : 1 ≤ thresholdCount s n (m + 1) := Nat.one_le_iff_ne_zero.mpr hne
  let hreach : ReachesThreshold s (m + 1) 1 := ⟨n, hpositive⟩
  have hmin : Nat.find hreach ≤ n := thresholdTime_min s (m + 1) 1 n hreach hpositive
  have hclock : thresholdTime s (m + 1) 1 = (Nat.find hreach : WithTop ℕ) :=
    thresholdTime_eq_coe s (m + 1) 1 hreach
  rw [hclock] at hbefore
  exact (not_lt_of_ge (by exact_mod_cast hmin)) hbefore

/-- Exact deterministic content of HLOZ Lemma 2.6: once the cutoff threshold
is above `m`, every late occurrence of `Mₘᵏ` forces a lower deviation of the
maximal local time at the cutoff. -/
theorem lateLevelSet_subset_lowerDeviationSet (δ : ℝ) (m k : ℕ)
    (hk : 0 < k)
    (hcutoff : (m : ℝ) < lowerDeviationThreshold δ (levelCutoffTime δ m)) :
    lateLevelSet δ m k ⊆ lowerDeviationSet δ (levelCutoffTime δ m) := by
  intro s hs
  change (⌊levelCutoff δ m⌋₊ : WithTop ℕ) < thresholdTime s m k ∧
    levelFavorite s m k at hs
  have hlevel : thresholdTime s m k < thresholdTime s (m + 1) 1 :=
    (levelFavorite_iff_thresholdTime_lt s m k hk).mp hs.2
  have hreach : ReachesThreshold s m k :=
    (thresholdTime_lt_top_iff s m k).mp (hlevel.trans_le le_top)
  have hfloorNat : ⌊levelCutoff δ m⌋₊ < Nat.find hreach := by
    rw [thresholdTime_eq_coe s m k hreach] at hs
    exact_mod_cast hs.1
  have hrealLt : levelCutoff δ m < (Nat.find hreach : ℝ) :=
    (Nat.floor_lt (Real.exp_nonneg _)).mp hfloorNat
  have hceilNat : levelCutoffTime δ m ≤ Nat.find hreach := by
    exact Nat.ceil_le.mpr hrealLt.le
  have hcutoffBeforeLevel :
      (levelCutoffTime δ m : WithTop ℕ) ≤ thresholdTime s m k := by
    rw [thresholdTime_eq_coe s m k hreach]
    exact_mod_cast hceilNat
  have hbefore : (levelCutoffTime δ m : WithTop ℕ) < thresholdTime s (m + 1) 1 :=
    hcutoffBeforeLevel.trans_lt hlevel
  have hmax : maxLocalTime s (levelCutoffTime δ m) ≤ m :=
    maxLocalTime_le_of_time_lt_nextThreshold s m (levelCutoffTime δ m) hbefore
  change (maxLocalTime s (levelCutoffTime δ m) : ℝ) <
    lowerDeviationThreshold δ (levelCutoffTime δ m)
  have hmaxReal : (maxLocalTime s (levelCutoffTime δ m) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmax
  exact hmaxReal.trans_lt hcutoff

/-! ## Proposition 1.3 as the sole probabilistic input -/

/-- The exact lower-deviation estimate of HLOZ Proposition 1.3, packaged as
a property of a path measure.  No inhabitant of this predicate is declared in
this file: the estimate is an explicit hypothesis of the implication below. -/
def HasPlanarMaximumLowerDeviation (μ : Measure WalkPath) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    μ (lowerDeviationSet δ n) <
      ENNReal.ofReal
        (C * Real.exp (-Real.exp (Real.log n ^ (3 / 5 : ℝ))))

/-- HLOZ Lemma 2.6, for all positive cutoff parameters and all positive
favorite counts, as a direct implication from Proposition 1.3.  The theorem
is stated eventually in `m`, which is the exact output of Proposition 1.3;
the paper's extension to the finitely many remaining levels is immaterial to
every subsequent use of the lemma. -/
theorem levelTime_tail_of_lowerDeviation
    (μ : Measure WalkPath) (hProp13 : HasPlanarMaximumLowerDeviation μ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, ∀ k : ℕ, 0 < k →
      μ (lateLevelSet δ m k) < ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
  let ε : ℝ := min δ (1 / 5)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ (by norm_num)
  have hεlt : ε < 2 / 5 := by
    dsimp [ε]
    exact (min_le_right δ (1 / 5)).trans_lt (by norm_num)
  have hεδ : ε ≤ δ := by
    dsimp [ε]
    exact min_le_left _ _
  obtain ⟨C, hC, N, hN⟩ := hProp13 ε hεpos
  have hcutoff := eventually_lt_lowerDeviationThreshold_at_levelCutoff ε hεpos hεlt
  have hmOne : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  have htimeN : ∀ᶠ m : ℕ in atTop, N ≤ levelCutoffTime ε m :=
    (tendsto_levelCutoffTime ε).eventually (eventually_ge_atTop N)
  have htail := eventually_prop13_bound_le_exp_neg_level ε C hC
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [hcutoff, hmOne, htimeN, htail] with m hcut hm hNtime htailM
  intro k hk
  have hlateMono : lateLevelSet δ m k ⊆ lateLevelSet ε m k :=
    lateLevelSet_mono_parameter hεδ hm
  have hlateDeviation :
      lateLevelSet ε m k ⊆ lowerDeviationSet ε (levelCutoffTime ε m) :=
    lateLevelSet_subset_lowerDeviationSet ε m k hk hcut
  have hmeasure : μ (lateLevelSet δ m k) <
      ENNReal.ofReal
        (C * Real.exp
          (-Real.exp (Real.log (levelCutoffTime ε m) ^ (3 / 5 : ℝ)))) :=
    (measure_mono hlateMono).trans_lt <|
      (measure_mono hlateDeviation).trans_lt (hN (levelCutoffTime ε m) hNtime)
  have hrealStrict : Real.exp (-(m : ℝ)) < Real.exp (-(1 / 2 : ℝ) * (m : ℝ)) := by
    apply Real.exp_lt_exp.mpr
    have hmReal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    linarith
  have hofRealTail : ENNReal.ofReal
        (C * Real.exp
          (-Real.exp (Real.log (levelCutoffTime ε m) ^ (3 / 5 : ℝ)))) <
      ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * (m : ℝ))) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
    exact htailM.trans_lt hrealStrict
  exact hmeasure.trans hofRealTail

end Erdos1165
