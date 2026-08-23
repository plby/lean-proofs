/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.TwoScaleLifting

/-!
# A nested iteration step

This file packages the three nested regular Bohr scales in the integer
Kelley--Meka iteration.  Simultaneous narrowing either gives an immediate
density increment or supplies two centred slices.  The outer slice is the
new dense set and the inner slice supplies doubled centres.  If the outer
carrier is not already terminally small, the two-scale lifting theorem and
the improved Bloom--Sisask bootstrap give a uniform density increment.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicNestedDensityStep

variable {N : ℕ} [NeZero N]

/-- A regular local state for a fixed regularity parameter `m`. -/
structure State (N m : ℕ) [NeZero N] where
  B : CyclicBohr.Set N
  t : ℝ
  delta : ℝ
  beta : ℝ
  A : Finset (ZMod N)
  radius_pos : 0 < B.radius
  rank_pos : 0 < B.rank
  t_lower : 1 / 2 ≤ t
  t_upper : t ≤ 1
  delta_pos : 0 < delta
  delta_lt : delta < t
  delta_formula : delta = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹
  regular :
    (10 * m) * (B.dilate (t + delta)).carrier.card ≤
      (10 * m + 1) * (B.dilate (t - delta)).carrier.card
  A_nonempty : A.Nonempty
  A_subset : A ⊆ (B.dilate t).carrier
  beta_pos : 0 < beta
  beta_le_one : beta ≤ 1
  density_eq : beta * (B.dilate t).carrier.card = A.card
  threeAPFree : ThreeAPFree (A : Set (ZMod N))

/-- The carrier represented by a state. -/
noncomputable abbrev State.carrier (s : State N m) : Finset (ZMod N) :=
  (s.B.dilate s.t).carrier

/-- The common logarithmic entropy budget used by every stable-carrier branch
of one nested step. -/
noncomputable def State.entropyBudget (s : State N m) : ℕ :=
  ⌈2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6⌉₊

/-- A rank-preserving reference Bohr set whose radius is exactly the radius
reached before the stable-carrier extraction in the canonical scale
construction.  The actual construction passes through the doubling
automorphism; that automorphism changes frequencies but not rank or radius,
so this simpler reference set records precisely the quantitative data needed
by the iteration. -/
noncomputable def State.radiusReference (s : State N m) : CyclicBohr.Set N :=
  let d : ℝ := (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹
  let e : ℝ := (400 * (s.B.rank : ℝ))⁻¹
  (((((s.B.dilate (s.delta / 4)).dilate (d / 8)).dilate (d / 16)).dilate
    (e / 4)).dilate e)

/-- Multiplicative radius loss incurred before the sharp spectral
controller in one canonical nested step. -/
noncomputable def State.referenceFactor (s : State N m) : ℝ :=
  let d : ℝ := (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹
  let e : ℝ := (400 * (s.B.rank : ℝ))⁻¹
  e * (e / 4 * (d / 16 * (d / 8 * (s.delta / 4))))

lemma State.radiusReference_radius (s : State N m) :
    s.radiusReference.radius = s.referenceFactor * s.B.radius := by
  have hr : (0 : ℝ) < s.B.rank := by exact_mod_cast s.rank_pos
  have hd : 0 < (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by
    have hmR : (0 : ℝ) < m := by
      have hmNat : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        have hzero : s.delta = 0 := by
          simpa only [hm0, Nat.cast_zero, mul_zero, zero_mul, inv_zero] using
            s.delta_formula
        linarith [s.delta_pos]
      exact_mod_cast hmNat
    positivity
  have he : 0 < (400 * (s.B.rank : ℝ))⁻¹ := by positivity
  simp only [State.radiusReference, State.referenceFactor,
    CyclicBohr.Set.radius_dilate]
  rw [abs_of_pos he, abs_of_pos (div_pos he (by norm_num)),
    abs_of_pos (div_pos hd (by norm_num)),
    abs_of_pos (div_pos hd (by norm_num)),
    abs_of_pos (div_pos s.delta_pos (by norm_num))]
  ring

lemma State.referenceFactor_pos (s : State N m) :
    0 < s.referenceFactor := by
  have hr : (0 : ℝ) < s.B.rank := by exact_mod_cast s.rank_pos
  have hmR : (0 : ℝ) < m := by
    have hmNat : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hzero : s.delta = 0 := by
        simpa only [hm0, Nat.cast_zero, mul_zero, zero_mul, inv_zero] using
          s.delta_formula
      linarith [s.delta_pos]
    exact_mod_cast hmNat
  unfold State.referenceFactor
  have he : 0 < (400 * (s.B.rank : ℝ))⁻¹ := by positivity
  have hd : 0 < (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by positivity
  exact mul_pos he (mul_pos (div_pos he (by norm_num))
    (mul_pos (div_pos hd (by norm_num))
      (mul_pos (div_pos hd (by norm_num)) (div_pos s.delta_pos (by norm_num)))))

lemma State.referenceFactor_le_one (s : State N m) :
    s.referenceFactor ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ s.B.rank := by exact_mod_cast s.rank_pos
  have he0 : 0 ≤ (400 * (s.B.rank : ℝ))⁻¹ := by positivity
  have he1 : (400 * (s.B.rank : ℝ))⁻¹ ≤ 1 := by
    have hden : (1 : ℝ) ≤ 400 * s.B.rank := by nlinarith
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have hdEq : (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ = s.delta := by
    exact s.delta_formula.symm
  have hdelta1 : s.delta ≤ 1 := s.delta_lt.le.trans s.t_upper
  have hd0 : 0 ≤ (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by positivity
  have hd1 : (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ ≤ 1 := by
    rw [hdEq]
    exact hdelta1
  have he4_0 : 0 ≤ (400 * (s.B.rank : ℝ))⁻¹ / 4 := by positivity
  have he4_1 : (400 * (s.B.rank : ℝ))⁻¹ / 4 ≤ 1 :=
    (div_le_self he0 (by norm_num)).trans he1
  have hd16_0 : 0 ≤ (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 16 := by
    positivity
  have hd16_1 : (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 16 ≤ 1 :=
    (div_le_self hd0 (by norm_num)).trans hd1
  have hd8_0 : 0 ≤ (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 := by
    positivity
  have hd8_1 : (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 ≤ 1 :=
    (div_le_self hd0 (by norm_num)).trans hd1
  have hdelta4_0 : 0 ≤ s.delta / 4 :=
    div_nonneg s.delta_pos.le (by norm_num)
  have hdelta4_1 : s.delta / 4 ≤ 1 :=
    (div_le_self s.delta_pos.le (by norm_num)).trans hdelta1
  have hinner1 :
      (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 * (s.delta / 4) ≤ 1 :=
    mul_le_one₀ hd8_1 hdelta4_0 hdelta4_1
  have hinner0 : 0 ≤
      (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 * (s.delta / 4) := by
    positivity
  have hmiddle1 :
      (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 16 *
          ((400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 *
            (s.delta / 4)) ≤ 1 :=
    mul_le_one₀ hd16_1 hinner0 hinner1
  have hmiddle0 : 0 ≤
      (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 16 *
        ((400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 *
          (s.delta / 4)) := by positivity
  have houter1 :
      (400 * (s.B.rank : ℝ))⁻¹ / 4 *
          ((400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 16 *
            ((400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 *
              (s.delta / 4))) ≤ 1 :=
    mul_le_one₀ he4_1 hmiddle0 hmiddle1
  have houter0 : 0 ≤
      (400 * (s.B.rank : ℝ))⁻¹ / 4 *
        ((400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 16 *
          ((400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ / 8 *
            (s.delta / 4))) := by positivity
  unfold State.referenceFactor
  exact mul_le_one₀ he1 houter0 houter1

private lemma mul_min_one_le_min_one_mul {a r : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hr0 : 0 ≤ r) :
    a * min 1 r ≤ min 1 (a * r) := by
  by_cases hr1 : r ≤ 1
  · rw [min_eq_right hr1,
      min_eq_right (mul_le_one₀ ha1 hr0 hr1)]
  · rw [min_eq_left (le_of_not_ge hr1), mul_one]
    apply le_min ha1
    calc
      a = a * 1 := (mul_one a).symm
      _ ≤ a * r := mul_le_mul_of_nonneg_left (le_of_not_ge hr1) ha0

/-- The exact multiplicative factor retained by the sharp radius floor in
one nested step. -/
noncomputable def State.oneStepRadiusFactor (s : State N m) : ℝ :=
  s.referenceFactor * ((1 - 1 / 8192 : ℝ) * s.beta) /
    (2 ^ 40 * (s.entropyBudget + 1 : ℝ) * (s.B.rank : ℝ) ^ 2)

/-- The absolute radius floor retained by every outcome of one canonical
nested step. -/
noncomputable def State.stepRadiusFloor (s : State N m) : ℝ :=
  CyclicQuantitativeBounds.controlledSharpRadiusFloor s.radiusReference
    ((1 - 1 / 8192 : ℝ) * s.beta) s.entropyBudget

lemma State.radiusReference_rank (s : State N m) :
    s.radiusReference.rank = s.B.rank := by
  simp [State.radiusReference]

lemma State.radiusReference_radius_pos (s : State N m) (hm : 0 < m) :
    0 < s.radiusReference.radius := by
  have hr : (0 : ℝ) < s.B.rank := by exact_mod_cast s.rank_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by positivity
  have he : 0 < (400 * (s.B.rank : ℝ))⁻¹ := by positivity
  simp only [State.radiusReference, CyclicBohr.Set.radius_dilate]
  rw [abs_of_pos he, abs_of_pos (div_pos he (by norm_num)),
    abs_of_pos (div_pos hd (by norm_num)),
    abs_of_pos (div_pos hd (by norm_num)),
    abs_of_pos (div_pos s.delta_pos (by norm_num))]
  exact mul_pos he (mul_pos (div_pos he (by norm_num))
    (mul_pos (div_pos hd (by norm_num))
      (mul_pos (div_pos hd (by norm_num))
        (mul_pos (div_pos s.delta_pos (by norm_num)) s.radius_pos))))

lemma State.stepRadiusFloor_pos (s : State N m) (hm : 0 < m) :
    0 < s.stepRadiusFloor := by
  apply CyclicQuantitativeBounds.controlledSharpRadiusFloor_pos
  · exact s.radiusReference_radius_pos hm
  · rw [s.radiusReference_rank]
    exact s.rank_pos
  · exact mul_pos (by norm_num) s.beta_pos

lemma State.oneStepRadiusFactor_pos (s : State N m) :
    0 < s.oneStepRadiusFactor := by
  unfold State.oneStepRadiusFactor
  have hr : (0 : ℝ) < s.B.rank := by exact_mod_cast s.rank_pos
  exact div_pos (mul_pos s.referenceFactor_pos
    (mul_pos (by norm_num) s.beta_pos)) (by positivity)

/-- Closed form of the sharp one-step radius factor.  All five canonical
narrowings and the two powers of the current rank are exposed in one
polynomial denominator. -/
lemma State.oneStepRadiusFactor_eq (s : State N m) :
    s.oneStepRadiusFactor =
      ((1 - 1 / 8192 : ℝ) * s.beta) /
        (2 ^ 51 * 400 ^ 5 * (m : ℝ) ^ 3 *
          (s.entropyBudget + 1 : ℝ) * (s.B.rank : ℝ) ^ 7) := by
  have hr : (s.B.rank : ℝ) ≠ 0 := by exact_mod_cast s.rank_pos.ne'
  have hmNat : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hzero : s.delta = 0 := by
      simpa only [hm0, Nat.cast_zero, mul_zero, zero_mul, inv_zero] using
        s.delta_formula
    linarith [s.delta_pos]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hmNat.ne'
  rw [State.oneStepRadiusFactor]
  unfold State.referenceFactor
  rw [s.delta_formula]
  field_simp
  ring

lemma State.oneStepRadiusFactor_le_one (s : State N m) :
    s.oneStepRadiusFactor ≤ 1 := by
  rw [s.oneStepRadiusFactor_eq]
  have hm1 : (1 : ℝ) ≤ m := by
    have hmNat : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hzero : s.delta = 0 := by
        simpa only [hm0, Nat.cast_zero, mul_zero, zero_mul, inv_zero] using
          s.delta_formula
      linarith [s.delta_pos]
    exact_mod_cast hmNat
  have hr1 : (1 : ℝ) ≤ s.B.rank := by exact_mod_cast s.rank_pos
  have hM1 : (1 : ℝ) ≤ s.entropyBudget + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s.entropyBudget)
  have hden1 : (1 : ℝ) ≤
      2 ^ 51 * 400 ^ 5 * (m : ℝ) ^ 3 *
        (s.entropyBudget + 1 : ℝ) * (s.B.rank : ℝ) ^ 7 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hm1)) hM1)
      (one_le_pow₀ hr1)
  have hnum0 : 0 ≤ (1 - 1 / 8192 : ℝ) * s.beta :=
    mul_nonneg (by norm_num) s.beta_pos.le
  have hnum1 : (1 - 1 / 8192 : ℝ) * s.beta ≤ 1 := by
    nlinarith [s.beta_pos, s.beta_le_one]
  exact (div_le_self hnum0 hden1).trans hnum1

lemma State.oneStepRadiusFactor_mul_min_le_stepRadiusFloor
    (s : State N m) :
    s.oneStepRadiusFactor * min 1 s.B.radius ≤ s.stepRadiusFloor := by
  have href := mul_min_one_le_min_one_mul
    s.referenceFactor_pos.le s.referenceFactor_le_one s.B.radius_nonneg
  have hbeta0 : 0 ≤ (1 - 1 / 8192 : ℝ) * s.beta :=
    (mul_pos (by norm_num) s.beta_pos).le
  rw [← s.radiusReference_radius] at href
  unfold State.oneStepRadiusFactor State.stepRadiusFloor
    CyclicQuantitativeBounds.controlledSharpRadiusFloor
  calc
    (s.referenceFactor * ((1 - 1 / 8192) * s.beta) /
        (2 ^ 40 * (s.entropyBudget + 1 : ℝ) * (s.B.rank : ℝ) ^ 2)) *
          min 1 s.B.radius =
      (s.referenceFactor * min 1 s.B.radius) *
        ((1 - 1 / 8192) * s.beta) /
          (2 ^ 40 * (s.entropyBudget + 1 : ℝ) * (s.B.rank : ℝ) ^ 2) := by
      ring
    _ ≤ min 1 s.radiusReference.radius *
        ((1 - 1 / 8192) * s.beta) /
          (2 ^ 40 * (s.entropyBudget + 1 : ℝ) * (s.B.rank : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right href hbeta0)
        (by positivity)
    _ = min 1 s.radiusReference.radius *
        ((1 - 1 / 8192) * s.beta) /
          (2 ^ 40 * (s.entropyBudget + 1 : ℝ) *
            (s.radiusReference.rank : ℝ) ^ 2) := by
      rw [s.radiusReference_rank]

lemma State.stepRadiusFloor_le_one (s : State N m) :
    s.stepRadiusFloor ≤ 1 := by
  have hbeta : (1 - 1 / 8192 : ℝ) * s.beta ≤ 1 := by
    nlinarith [s.beta_pos, s.beta_le_one]
  have hnum0 : 0 ≤ min 1 s.radiusReference.radius :=
    le_min zero_le_one s.radiusReference.radius_nonneg
  have hnum : min 1 s.radiusReference.radius *
      ((1 - 1 / 8192 : ℝ) * s.beta) ≤ 1 := by
    exact mul_le_one₀ (min_le_left _ _)
      (mul_nonneg (by norm_num) s.beta_pos.le) hbeta
  have hr : (1 : ℝ) ≤ s.radiusReference.rank := by
    rw [s.radiusReference_rank]
    exact_mod_cast s.rank_pos
  have hden : (1 : ℝ) ≤
      2 ^ 40 * (s.entropyBudget + 1 : ℝ) *
        (s.radiusReference.rank : ℝ) ^ 2 := by
    have hM : (1 : ℝ) ≤ s.entropyBudget + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le s.entropyBudget)
    have hrSq : (1 : ℝ) ≤ (s.radiusReference.rank : ℝ) ^ 2 :=
      one_le_pow₀ hr
    calc
      (1 : ℝ) ≤ 2 ^ 40 := by norm_num
      _ ≤ 2 ^ 40 * (s.entropyBudget + 1 : ℝ) := by
        exact le_mul_of_one_le_right (by positivity) hM
      _ ≤ 2 ^ 40 * (s.entropyBudget + 1 : ℝ) *
          (s.radiusReference.rank : ℝ) ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) hrSq
  unfold State.stepRadiusFloor
    CyclicQuantitativeBounds.controlledSharpRadiusFloor
  exact (div_le_self
    (mul_nonneg hnum0 (mul_nonneg (by norm_num) s.beta_pos.le)) hden).trans hnum

private lemma radius_dilate_le_self (B : CyclicBohr.Set N) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (B.dilate a).radius ≤ B.radius := by
  rw [CyclicBohr.Set.radius_dilate, abs_of_nonneg ha0]
  nlinarith [B.radius_nonneg]

/-- Quantitative radius data supplied by the canonical nested scales.  This
calculation is kept outside the main structural dichotomy so elaborating the
large analytic branch stays within the default heartbeat budget. -/
lemma State.canonical_radius_data
    (hN : Odd N) (s : State N m) (J K H R : CyclicBohr.Set N)
    {dj dk zeta eta : ℝ}
    (hJdef : J = s.B.dilate (s.delta / 4))
    (hKdef : K = J.dilate (dj / 8))
    (hHdef : H = (CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 16))
    (hRdef : R = H.dilate (zeta / 4))
    (hdj0 : 0 < dj) (hdj1 : dj ≤ 1)
    (hdk0 : 0 < dk) (hdk1 : dk ≤ 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hdjFormula : dj = (400 * (m : ℝ) * (J.rank : ℝ))⁻¹)
    (hdkFormula : dk = (400 * (m : ℝ) * (K.rank : ℝ))⁻¹)
    (hzetaFormula : zeta = (400 * (H.rank : ℝ))⁻¹)
    (hetaFormula : eta = (400 * (R.rank : ℝ))⁻¹)
    (hJrankState : J.rank = s.B.rank)
    (hKrankState : K.rank = s.B.rank)
    (hRrankState : R.rank = s.B.rank) :
    s.radiusReference.radius = (R.dilate eta).radius ∧
      s.stepRadiusFloor ≤ J.radius ∧ s.stepRadiusFloor ≤ K.radius := by
  have hHrankState : H.rank = s.B.rank := by
    rw [hHdef, CyclicBohr.Set.rank_dilate,
      CyclicTwoScaleLifting.doubleBohr_rank, hKrankState]
  have hdjState : dj = (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by
    simpa only [hJrankState] using hdjFormula
  have hdkState : dk = (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by
    simpa only [hKrankState] using hdkFormula
  have hzetaState : zeta = (400 * (s.B.rank : ℝ))⁻¹ := by
    simpa only [hHrankState] using hzetaFormula
  have hetaState : eta = (400 * (s.B.rank : ℝ))⁻¹ := by
    simpa only [hRrankState] using hetaFormula
  have hdState : 0 < (400 * (m : ℝ) * (s.B.rank : ℝ))⁻¹ := by
    rw [← hdjState]
    exact hdj0
  have heState : 0 < (400 * (s.B.rank : ℝ))⁻¹ := by
    rw [← hetaState]
    exact heta0
  have hReferenceRadius : s.radiusReference.radius =
      (R.dilate eta).radius := by
    rw [hRdef, hHdef, hKdef, hJdef]
    simp only [State.radiusReference, CyclicBohr.Set.radius_dilate,
      CyclicTwoScaleLifting.doubleBohr_radius]
    rw [abs_of_pos heta0, abs_of_pos (div_pos hzeta0 (by norm_num)),
      abs_of_pos (div_pos hdk0 (by norm_num)),
      abs_of_pos (div_pos hdj0 (by norm_num)),
      abs_of_pos (div_pos s.delta_pos (by norm_num))]
    rw [hdjState, hdkState, hzetaState, hetaState]
    rw [abs_of_pos heState, abs_of_pos (div_pos heState (by norm_num)),
      abs_of_pos (div_pos hdState (by norm_num)),
      abs_of_pos (div_pos hdState (by norm_num))]
  have hReferenceLeK : s.radiusReference.radius ≤ K.radius := by
    rw [hReferenceRadius]
    calc
      (R.dilate eta).radius ≤ R.radius :=
        radius_dilate_le_self R heta0.le heta1
      _ = (H.dilate (zeta / 4)).radius := by rw [hRdef]
      _ ≤ H.radius := radius_dilate_le_self H (by positivity) (by nlinarith)
      _ = ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
          (dk / 16)).radius := by rw [hHdef]
      _ ≤ (CyclicTwoScaleLifting.doubleBohr hN K).radius :=
        radius_dilate_le_self _ (by positivity) (by nlinarith)
      _ = K.radius := CyclicTwoScaleLifting.doubleBohr_radius hN K
  have hReferenceLeJ : s.radiusReference.radius ≤ J.radius :=
    hReferenceLeK.trans (by
      rw [hKdef]
      exact radius_dilate_le_self J (by positivity) (by nlinarith))
  have hbetaFloor0 : 0 ≤ (1 - 1 / 8192 : ℝ) * s.beta :=
    (mul_pos (by norm_num) s.beta_pos).le
  have hbetaFloor1 : (1 - 1 / 8192 : ℝ) * s.beta ≤ 1 := by
    nlinarith [s.beta_pos, s.beta_le_one]
  have hFloorReference : s.stepRadiusFloor ≤ s.radiusReference.radius := by
    exact CyclicQuantitativeBounds.controlledSharpRadiusFloor_le_radius
      s.radiusReference s.entropyBudget
      (by rw [s.radiusReference_rank]; exact s.rank_pos)
      hbetaFloor0 hbetaFloor1
  exact ⟨hReferenceRadius, hFloorReference.trans hReferenceLeJ,
    hFloorReference.trans hReferenceLeK⟩

/-- Quantitative data retained by a nonterminal density increment. -/
structure IncrementOutcome {m : ℕ} (s s' : State N m) : Prop where
  density_gain : (1 + 1 / 32768 : ℝ) * s.beta ≤ s'.beta
  rank_bound : (s'.B.rank : ℝ) ≤ (s.B.rank : ℝ) +
    2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6
  radius_floor : s.stepRadiusFloor ≤ s'.B.radius

/-- Quantitative data retained by the terminal alternative. -/
structure TerminalOutcome {m : ℕ} (s st : State N m) : Prop where
  density_lower : (1 - 1 / 8192 : ℝ) * s.beta ≤ st.beta
  terminal : st.A.card ^ 2 < 2 * st.carrier.card
  rank_bound : (st.B.rank : ℝ) ≤ (s.B.rank : ℝ) +
    2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6
  radius_floor : s.stepRadiusFloor ≤ st.B.radius

lemma IncrementOutcome.radius_retained {m : ℕ} {s s' : State N m}
    (h : IncrementOutcome s s') :
    s.oneStepRadiusFactor * min 1 s.B.radius ≤ min 1 s'.B.radius := by
  refine s.oneStepRadiusFactor_mul_min_le_stepRadiusFloor.trans ?_
  exact le_min s.stepRadiusFloor_le_one h.radius_floor

lemma TerminalOutcome.radius_retained {m : ℕ} {s st : State N m}
    (h : TerminalOutcome s st) :
    s.oneStepRadiusFactor * min 1 s.B.radius ≤ min 1 st.B.radius := by
  refine s.oneStepRadiusFactor_mul_min_le_stepRadiusFloor.trans ?_
  exact le_min s.stepRadiusFloor_le_one h.radius_floor

/-- Convert the stable-carrier radius certificate, stated on the innermost
canonical scale, to the uniform radius floor attached to the current state. -/
lemma State.stepRadiusFloor_le_of_controlled
    (s : State N m) (R C : CyclicBohr.Set N) {eta betaOut : ℝ}
    (hRrankState : R.rank = s.B.rank)
    (hReferenceRadius : s.radiusReference.radius = (R.dilate eta).radius)
    (hbetaGood : (1 - 1 / 8192 : ℝ) * s.beta ≤ betaOut)
    (hcontrolled :
      CyclicQuantitativeBounds.controlledSharpRadiusFloor
          (R.dilate eta) betaOut s.entropyBudget ≤ C.radius) :
    s.stepRadiusFloor ≤ C.radius := by
  have hFloorEq :
      CyclicQuantitativeBounds.controlledSharpRadiusFloor
          s.radiusReference betaOut s.entropyBudget =
        CyclicQuantitativeBounds.controlledSharpRadiusFloor
          (R.dilate eta) betaOut s.entropyBudget := by
    unfold CyclicQuantitativeBounds.controlledSharpRadiusFloor
    rw [hReferenceRadius, s.radiusReference_rank,
      CyclicBohr.Set.rank_dilate, hRrankState]
  calc
    s.stepRadiusFloor ≤
        CyclicQuantitativeBounds.controlledSharpRadiusFloor
          s.radiusReference betaOut s.entropyBudget := by
      apply CyclicQuantitativeBounds.controlledSharpRadiusFloor_mono_beta
      · rw [s.radiusReference_rank]
        exact s.rank_pos
      · exact hbetaGood
    _ = CyclicQuantitativeBounds.controlledSharpRadiusFloor
          (R.dilate eta) betaOut s.entropyBudget := hFloorEq
    _ ≤ C.radius := hcontrolled

/-- Relative density of a finite set in a nonempty carrier. -/
noncomputable def relativeDensity (A S : Finset (ZMod N)) : ℝ :=
  (A.card : ℝ) / S.card

lemma relativeDensity_pos (A S : Finset (ZMod N))
    (hA : A.Nonempty) (hS : S.Nonempty) :
    0 < relativeDensity A S := by
  unfold relativeDensity
  positivity

lemma relativeDensity_le_one (A S : Finset (ZMod N)) (hAS : A ⊆ S) :
    relativeDensity A S ≤ 1 := by
  unfold relativeDensity
  by_cases hSempty : S = ∅
  · subst S
    simp at hAS ⊢
  · have hScard : (0 : ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSempty)
    rw [div_le_one hScard]
    exact_mod_cast Finset.card_le_card hAS

lemma relativeDensity_mul_card (A S : Finset (ZMod N))
    (hS : S.Nonempty) :
    relativeDensity A S * (S.card : ℝ) = A.card := by
  unfold relativeDensity
  have hScard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  field_simp

/-- Normalized slices are monotone in their carrier. -/
lemma normalizedSlice_mono (A S T : Finset (ZMod N)) (x : ZMod N)
    (hTS : T ⊆ S) :
    CyclicDensityIncrement.normalizedSlice A T x ⊆
      CyclicDensityIncrement.normalizedSlice A S x := by
  intro y hy
  unfold CyclicDensityIncrement.normalizedSlice at hy ⊢
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hTS hy.1, hy.2⟩

private lemma nonempty_of_positive_density
    (A S : Finset (ZMod N)) {alpha : ℝ}
    (halpha : 0 < alpha) (hS : S.Nonempty)
    (hdense : alpha ≤ (A.card : ℝ) / S.card) : A.Nonempty := by
  by_contra hA
  rw [not_nonempty_iff_eq_empty.mp hA] at hdense
  simp at hdense
  exact (not_lt_of_ge hdense) halpha

/-- A narrowing increment on the inner regular carrier remains a slightly
smaller increment after enlarging back to the central regular carrier. -/
private lemma density_gain_on_enlarged_regular_scale
    (K : CyclicBohr.Set N) (A : Finset (ZMod N)) (m : ℕ)
    {tk dk alpha : ℝ} (hm : 8192 ≤ m) (htk0 : 0 ≤ tk) (hdk : 0 < dk)
    (halpha : 0 < alpha)
    (hregular :
      (10 * m) * (K.dilate (tk + dk)).carrier.card ≤
        (10 * m + 1) * (K.dilate (tk - dk)).carrier.card)
    (hinner : (K.dilate (tk - dk)).carrier.Nonempty)
    (hinc : (1 + 1 / 16384 : ℝ) * alpha ≤
      relativeDensity A (K.dilate (tk - dk)).carrier) :
    (1 + 1 / 32768 : ℝ) * alpha ≤
      relativeDensity A (K.dilate tk).carrier := by
  let Q := (K.dilate (tk - dk)).carrier
  let R := (K.dilate tk).carrier
  have hQR :
      (10 * m : ℝ) * R.card ≤ (10 * m + 1 : ℝ) * Q.card := by
    have hmono : R.card ≤ (K.dilate (tk + dk)).carrier.card :=
      Finset.card_le_card (CyclicBohr.Set.dilate_mono K htk0 (by linarith))
    have hregularR :
        (10 * m : ℝ) * (K.dilate (tk + dk)).carrier.card ≤
          (10 * m + 1 : ℝ) * Q.card := by
      exact_mod_cast hregular
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hmono)
      (by positivity)).trans hregularR
  have hcoef :
      (1 + 1 / 32768 : ℝ) * (10 * m + 1) ≤
        (1 + 1 / 16384 : ℝ) * (10 * m) := by
    have hmR : (8192 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    norm_num
    nlinarith [hmR]
  have hcompare :
      (1 + 1 / 32768 : ℝ) * alpha * R.card ≤
        (1 + 1 / 16384 : ℝ) * alpha * Q.card := by
    have hscaled :
        (10 * m : ℝ) *
            ((1 + 1 / 32768 : ℝ) * alpha * R.card) ≤
          (10 * m : ℝ) *
            ((1 + 1 / 16384 : ℝ) * alpha * Q.card) := by
      calc
        (10 * m : ℝ) * ((1 + 1 / 32768 : ℝ) * alpha * R.card) =
            ((1 + 1 / 32768 : ℝ) * alpha) *
              ((10 * m : ℝ) * R.card) := by ring
        _ ≤ ((1 + 1 / 32768 : ℝ) * alpha) *
              ((10 * m + 1 : ℝ) * Q.card) := by gcongr
        _ = ((1 + 1 / 32768 : ℝ) * (10 * m + 1)) *
              alpha * Q.card := by ring
        _ ≤ ((1 + 1 / 16384 : ℝ) * (10 * m)) *
              alpha * Q.card := by gcongr
        _ = (10 * m : ℝ) *
              ((1 + 1 / 16384 : ℝ) * alpha * Q.card) := by ring
    exact le_of_mul_le_mul_left hscaled (by positivity)
  have hQcard : (0 : ℝ) < Q.card := by exact_mod_cast hinner.card_pos
  have hRcard : (0 : ℝ) < R.card := by
    exact_mod_cast (K.dilate tk).card_pos
  have hincMul :
      (1 + 1 / 16384 : ℝ) * alpha * Q.card ≤ A.card := by
    unfold relativeDensity at hinc
    simpa only [Q] using ((le_div_iff₀ hQcard).mp hinc)
  unfold relativeDensity
  rw [le_div_iff₀ hRcard]
  exact hcompare.trans hincMul

/-- Package the elementary state fields after a density-increment branch.
Keeping this record construction out of the analytic dichotomy substantially
reduces elaboration of the latter. -/
private lemma exists_increment_state
    (s : State N m) (B : CyclicBohr.Set N) (A : Finset (ZMod N))
    {t delta beta : ℝ}
    (hradius : 0 < B.radius) (hrank : 0 < B.rank)
    (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1)
    (hdelta0 : 0 < delta) (hdeltat : delta < t)
    (hdeltaFormula : delta = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hA : A.Nonempty) (hAsub : A ⊆ (B.dilate t).carrier)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hfree : ThreeAPFree (A : Set (ZMod N)))
    (hgain : (1 + 1 / 32768 : ℝ) * s.beta ≤ beta)
    (hrankBound : (B.rank : ℝ) ≤ (s.B.rank : ℝ) +
      2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6)
    (hfloor : s.stepRadiusFloor ≤ B.radius) :
    ∃ s' : State N m, IncrementOutcome s s' := by
  let s' : State N m := {
    B := B
    t := t
    delta := delta
    beta := beta
    A := A
    radius_pos := hradius
    rank_pos := hrank
    t_lower := ht0
    t_upper := ht1
    delta_pos := hdelta0
    delta_lt := hdeltat
    delta_formula := hdeltaFormula
    regular := hregular
    A_nonempty := hA
    A_subset := hAsub
    beta_pos := hbeta0
    beta_le_one := hbeta1
    density_eq := hdensity
    threeAPFree := hfree }
  exact ⟨s', hgain, hrankBound, hfloor⟩

/-- Package the elementary state fields after the terminal branch. -/
private lemma exists_terminal_state
    (s : State N m) (B : CyclicBohr.Set N) (A : Finset (ZMod N))
    {t delta beta : ℝ}
    (hradius : 0 < B.radius) (hrank : 0 < B.rank)
    (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1)
    (hdelta0 : 0 < delta) (hdeltat : delta < t)
    (hdeltaFormula : delta = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hA : A.Nonempty) (hAsub : A ⊆ (B.dilate t).carrier)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hfree : ThreeAPFree (A : Set (ZMod N)))
    (hbetaLower : (1 - 1 / 8192 : ℝ) * s.beta ≤ beta)
    (hterminal : A.card ^ 2 < 2 * (B.dilate t).carrier.card)
    (hrankBound : (B.rank : ℝ) ≤ (s.B.rank : ℝ) +
      2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6)
    (hfloor : s.stepRadiusFloor ≤ B.radius) :
    ∃ st : State N m, TerminalOutcome s st := by
  let st : State N m := {
    B := B
    t := t
    delta := delta
    beta := beta
    A := A
    radius_pos := hradius
    rank_pos := hrank
    t_lower := ht0
    t_upper := ht1
    delta_pos := hdelta0
    delta_lt := hdeltat
    delta_formula := hdeltaFormula
    regular := hregular
    A_nonempty := hA
    A_subset := hAsub
    beta_pos := hbeta0
    beta_le_one := hbeta1
    density_eq := hdensity
    threeAPFree := hfree }
  exact ⟨st, hbetaLower, by simpa only [State.carrier] using hterminal,
    hrankBound, hfloor⟩

private lemma outer_increment_outcome
    (s : State N m) (J : CyclicBohr.Set N) {tj dj : ℝ}
    (hJradius : 0 < J.radius) (hJrank : 0 < J.rank)
    (htj0 : 1 / 2 ≤ tj) (htj1 : tj ≤ 1)
    (hdj : 0 < dj) (hdjtj : dj < tj)
    (hdjFormula : dj = (400 * (m : ℝ) * (J.rank : ℝ))⁻¹)
    (hJregular :
      (10 * m) * (J.dilate (tj + dj)).carrier.card ≤
        (10 * m + 1) * (J.dilate (tj - dj)).carrier.card)
    (hJrankState : J.rank = s.B.rank)
    (hFloorJ : s.stepRadiusFloor ≤ J.radius) (x : ZMod N)
    (hinc : (1 + (1 / 8192 : ℝ) / 2) * s.beta ≤
      (CyclicBohr.translatedSlice s.A (J.dilate tj).carrier x).card /
        ((J.dilate tj).carrier.card : ℝ)) :
    ∃ s' : State N m, IncrementOutcome s s' := by
  let P := (J.dilate tj).carrier
  let Anew := CyclicDensityIncrement.normalizedSlice s.A P x
  let betaNew := relativeDensity Anew P
  have hP : P.Nonempty := CyclicBohr.Set.carrier_nonempty _
  have hsub : Anew ⊆ P :=
    CyclicDensityIncrement.normalizedSlice_subset_right s.A P x
  have hinc' : (1 + 1 / 16384 : ℝ) * s.beta ≤ betaNew := by
    norm_num at hinc ⊢
    simpa [betaNew, relativeDensity, Anew, P,
      CyclicDensityIncrement.card_normalizedSlice_eq_card_translatedSlice]
      using hinc
  have hAnew : Anew.Nonempty :=
    nonempty_of_positive_density Anew P
      (mul_pos (by norm_num) s.beta_pos) hP hinc'
  have hgain : (1 + 1 / 32768 : ℝ) * s.beta ≤ betaNew :=
    hinc'.trans' (by nlinarith [s.beta_pos])
  have hRankNew : (J.rank : ℝ) ≤ (s.B.rank : ℝ) +
      2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6 := by
    rw [hJrankState]
    exact le_add_of_nonneg_right (by positivity)
  exact exists_increment_state s J Anew hJradius hJrank htj0 htj1
    hdj hdjtj hdjFormula hJregular hAnew hsub
    (relativeDensity_pos _ _ hAnew hP)
    (relativeDensity_le_one _ _ hsub) (relativeDensity_mul_card _ _ hP)
    (CyclicDensityIncrement.threeAPFree_normalizedSlice
      s.A P x s.threeAPFree) hgain hRankNew hFloorJ

private lemma inner_increment_outcome
    (s : State N m) (K : CyclicBohr.Set N) {tk dk : ℝ}
    (hm : 8192 ≤ m) (hKradius : 0 < K.radius) (hKrank : 0 < K.rank)
    (htk0 : 1 / 2 ≤ tk) (htk1 : tk ≤ 1)
    (hdk : 0 < dk) (hdktk : dk < tk)
    (hdkFormula : dk = (400 * (m : ℝ) * (K.rank : ℝ))⁻¹)
    (hKregular :
      (10 * m) * (K.dilate (tk + dk)).carrier.card ≤
        (10 * m + 1) * (K.dilate (tk - dk)).carrier.card)
    (hKrankState : K.rank = s.B.rank)
    (hFloorK : s.stepRadiusFloor ≤ K.radius) (x : ZMod N)
    (hinc : (1 + (1 / 8192 : ℝ) / 2) * s.beta ≤
      (CyclicBohr.translatedSlice s.A (K.dilate (tk - dk)).carrier x).card /
        ((K.dilate (tk - dk)).carrier.card : ℝ)) :
    ∃ s' : State N m, IncrementOutcome s s' := by
  let Q := (K.dilate (tk - dk)).carrier
  let Anew := CyclicDensityIncrement.normalizedSlice s.A Q x
  let R := (K.dilate tk).carrier
  let betaNew := relativeDensity Anew R
  have hQ : Q.Nonempty := CyclicBohr.Set.carrier_nonempty _
  have hQsubR : Q ⊆ R := by
    apply CyclicBohr.Set.dilate_mono K (sub_nonneg.mpr hdktk.le)
    linarith
  have hsub : Anew ⊆ R :=
    (CyclicDensityIncrement.normalizedSlice_subset_right s.A Q x).trans
      hQsubR
  have hincQ : (1 + 1 / 16384 : ℝ) * s.beta ≤
      relativeDensity Anew Q := by
    norm_num at hinc ⊢
    simpa [relativeDensity, Anew, Q,
      CyclicDensityIncrement.card_normalizedSlice_eq_card_translatedSlice]
      using hinc
  have hAnew : Anew.Nonempty :=
    nonempty_of_positive_density Anew Q
      (mul_pos (by norm_num) s.beta_pos) hQ hincQ
  have hgain : (1 + 1 / 32768 : ℝ) * s.beta ≤ betaNew := by
    simpa only [betaNew, R, Q] using
      density_gain_on_enlarged_regular_scale K Anew m hm
        (by linarith [htk0]) hdk s.beta_pos hKregular hQ hincQ
  have hRankNew : (K.rank : ℝ) ≤ (s.B.rank : ℝ) +
      2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6 := by
    rw [hKrankState]
    exact le_add_of_nonneg_right (by positivity)
  exact exists_increment_state s K Anew hKradius hKrank htk0 htk1
    hdk hdktk hdkFormula hKregular hAnew hsub
    (relativeDensity_pos _ _ hAnew (K.dilate tk).carrier_nonempty)
    (relativeDensity_le_one _ _ hsub)
    (relativeDensity_mul_card _ _ (K.dilate tk).carrier_nonempty)
    (CyclicDensityIncrement.threeAPFree_normalizedSlice
      s.A Q x s.threeAPFree) hgain hRankNew hFloorK

/-- The exact nested structural step.  All inclusions between the chosen
Bohr scales are stated explicitly; the following file constructs these
scales and proves their quantitative size bounds. -/
theorem exists_increment_or_terminal
    (hN : Odd N) (m : ℕ) (hm : 8192 ≤ m) (s : State N m)
    (J K H R : CyclicBohr.Set N)
    {tj dj tk dk u zeta vr eta : ℝ}
    (hJradius : 0 < J.radius) (hJrank : 0 < J.rank)
    (htj0 : 1 / 2 ≤ tj) (htj1 : tj ≤ 1)
    (hdj : 0 < dj) (hdjtj : dj < tj)
    (hdjFormula : dj = (400 * (m : ℝ) * (J.rank : ℝ))⁻¹)
    (hJregular :
      (10 * m) * (J.dilate (tj + dj)).carrier.card ≤
        (10 * m + 1) * (J.dilate (tj - dj)).carrier.card)
    (hKradius : 0 < K.radius) (hKrank : 0 < K.rank)
    (htk0 : 1 / 2 ≤ tk) (htk1 : tk ≤ 1)
    (hdk : 0 < dk) (hdktk : dk < tk)
    (hdkFormula : dk = (400 * (m : ℝ) * (K.rank : ℝ))⁻¹)
    (hKregular :
      (10 * m) * (K.dilate (tk + dk)).carrier.card ≤
        (10 * m + 1) * (K.dilate (tk - dk)).carrier.card)
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 1)
    (hzeta : 0 < zeta) (hzetau : zeta < u)
    (hHregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hvr0 : 1 / 2 ≤ vr) (hvr1 : vr ≤ 1)
    (heta : 0 < eta) (hetavr : eta < vr)
    (hRregular :
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card)
    (hJrankState : J.rank = s.B.rank)
    (hKrankState : K.rank = s.B.rank)
    (hRrankState : R.rank = s.B.rank)
    (hReferenceRadius : s.radiusReference.radius = (R.dilate eta).radius)
    (hFloorJ : s.stepRadiusFloor ≤ J.radius)
    (hFloorK : s.stepRadiusFloor ≤ K.radius)
    (hTestOuter :
      (K.dilate (tk - dk)).carrier ⊆ (J.dilate tj).carrier)
    (hOuterSmall :
      (J.dilate tj).carrier ⊆ (s.B.dilate s.delta).carrier)
    (hDoubleTestStable :
      ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
        (tk - dk)).carrier ⊆ (J.dilate dj).carrier)
    (hWeightInner :
      (H.dilate (u - zeta)).carrier ⊆
        ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
          (dk / 4)).carrier)
    (hWeightOuter :
      (H.dilate (u - zeta)).carrier ⊆ (J.dilate (dj / 4)).carrier)
    (hHsmall :
      (H.dilate zeta).carrier ⊆ (J.dilate (dj / 4)).carrier)
    (hHsmallInner :
      (H.dilate zeta).carrier ⊆
        ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
          (dk / 4)).carrier)
    (hRinnerOuter :
      (R.dilate (vr - eta)).carrier ⊆ (J.dilate (dj / 4)).carrier)
    (hRinnerInner :
      (R.dilate (vr - eta)).carrier ⊆
        ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
          (dk / 4)).carrier)
    (hRinnerH :
      (R.dilate (vr - eta)).carrier ⊆ (H.dilate zeta).carrier)
    (hRsmall :
      (R.dilate eta).carrier ⊆ (J.dilate (dj / 4)).carrier)
    (herror :
      3 * (1 / ((5 * m : ℕ) * ((1 - 1 / 8192 : ℝ) * s.beta))) ≤
        (1 / 16 : ℝ) / 4) :
    (∃ s' : State N m, IncrementOutcome s s') ∨
      ∃ st : State N m, TerminalOutcome s st := by
  let P := (J.dilate tj).carrier
  let Q := (K.dilate (tk - dk)).carrier
  have hP : P.Nonempty := CyclicBohr.Set.carrier_nonempty _
  have hQ : Q.Nonempty := CyclicBohr.Set.carrier_nonempty _
  have hQsubP : Q ⊆ P := by simpa [P, Q] using hTestOuter
  have hQsmall : Q ⊆ (s.B.dilate s.delta).carrier :=
    hQsubP.trans (by simpa [P] using hOuterSmall)
  have hmR : (8192 : ℝ) ≤ m := by exact_mod_cast hm
  have hscale : 4 ≤ ((10 * m : ℕ) : ℝ) * (1 / 8192 : ℝ) := by
    push_cast
    norm_num
    nlinarith
  have hinnerCenter :
      (s.B.dilate (s.t - s.delta)).carrier ⊆
        (s.B.dilate s.t).carrier :=
    CyclicBohr.Set.dilate_mono s.B (sub_nonneg.mpr s.delta_lt.le)
      (sub_le_self _ s.delta_pos.le)
  have hregularN :
      (10 * m) * (s.B.dilate (s.t + s.delta)).carrier.card ≤
        (10 * m + 1) * (s.B.dilate s.t).carrier.card :=
    s.regular.trans
      (Nat.mul_le_mul_left (10 * m + 1) (Finset.card_le_card hinnerCenter))
  obtain hgood | hPinc | hQinc :=
    CyclicLocalNarrowing.narrowing_dichotomy
      s.B s.A P Q (10 * m) (t := s.t) (delta := s.delta)
      (alpha := s.beta) (epsilon := (1 / 8192 : ℝ))
      (by positivity) (by linarith [s.t_lower]) s.delta_pos.le
      s.beta_pos (by norm_num) (by norm_num) hscale hregularN
      s.A_subset s.density_eq hP hQ hOuterSmall hQsmall
  · obtain ⟨x, _hx, hPgood, hQgood⟩ := hgood
    let Aout := CyclicDensityIncrement.normalizedSlice s.A P x
    let Atest := CyclicDensityIncrement.normalizedSlice s.A Q x
    let betaOut := relativeDensity Aout P
    have hAoutSub : Aout ⊆ P :=
      CyclicDensityIncrement.normalizedSlice_subset_right s.A P x
    have hAtestSub : Atest ⊆ Q :=
      CyclicDensityIncrement.normalizedSlice_subset_right s.A Q x
    have hAtestAout : Atest ⊆ Aout :=
      normalizedSlice_mono s.A P Q x hQsubP
    have hbetaGood : (1 - 1 / 8192 : ℝ) * s.beta ≤ betaOut := by
      simpa [betaOut, relativeDensity, Aout,
        CyclicDensityIncrement.card_normalizedSlice_eq_card_translatedSlice]
        using hPgood
    have hgammaGood : (1 - 1 / 8192 : ℝ) * s.beta ≤
        relativeDensity Atest Q := by
      simpa [relativeDensity, Atest,
        CyclicDensityIncrement.card_normalizedSlice_eq_card_translatedSlice]
        using hQgood
    have hlow0 : 0 < (1 - 1 / 8192 : ℝ) * s.beta :=
      mul_pos (by norm_num) s.beta_pos
    have hAout : Aout.Nonempty :=
      nonempty_of_positive_density Aout P hlow0 hP hbetaGood
    have hAtest : Atest.Nonempty :=
      nonempty_of_positive_density Atest Q hlow0 hQ hgammaGood
    have hbetaOut0 : 0 < betaOut := relativeDensity_pos Aout P hAout hP
    have hbetaOut1 : betaOut ≤ 1 := relativeDensity_le_one Aout P hAoutSub
    have hfreeOut : ThreeAPFree (Aout : Set (ZMod N)) :=
      CyclicDensityIncrement.threeAPFree_normalizedSlice
        s.A P x s.threeAPFree
    by_cases hcard : 2 * P.card ≤ Aout.card ^ 2
    · let K2 := CyclicTwoScaleLifting.doubleBohr hN K
      let C := Atest.image (2 • ·)
      let D := (K2.dilate (tk - dk)).carrier
      let W := (H.dilate (u - zeta)).carrier
      let V := (R.dilate (vr - eta)).carrier
      let gamma := relativeDensity C D
      have hK2radius : 0 < K2.radius := by simpa [K2] using hKradius
      have hK2rank : 0 < K2.rank := by simpa [K2] using hKrank
      have hDimage : D = Q.image (2 • ·) := by
        change (K2.dilate (tk - dk)).carrier = Q.image (2 • ·)
        rw [show K2.dilate (tk - dk) =
          CyclicTwoScaleLifting.doubleBohr hN (K.dilate (tk - dk)) by
            simp only [K2, CyclicTwoScaleLifting.doubleBohr_dilate]]
        rw [CyclicTwoScaleLifting.carrier_doubleBohr]
        change
          (K.dilate (tk - dk)).carrier.image
              (CyclicTwoScaleLifting.doubleEquiv hN) =
            (K.dilate (tk - dk)).carrier.image (2 • ·)
        apply Finset.image_congr
        intro z hz
        exact CyclicTwoScaleLifting.doubleEquiv_apply hN z
      have hDcard : D.card = Q.card := by
        rw [hDimage, CyclicTwoScaleLifting.card_image_double_eq hN]
      have hCcard : C.card = Atest.card := by
        exact CyclicTwoScaleLifting.card_image_double_eq hN Atest
      have hC : C.Nonempty := by
        rw [← Finset.card_pos, hCcard]
        exact hAtest.card_pos
      have hCD : C ⊆ D := by
        rw [hDimage]
        exact Finset.image_mono _ hAtestSub
      have hgammaEq : gamma = relativeDensity Atest Q := by
        unfold gamma relativeDensity
        rw [hCcard, hDcard]
      have hgamma0 : 0 < gamma := by
        rw [hgammaEq]
        exact relativeDensity_pos Atest Q hAtest hQ
      have hgamma1 : gamma ≤ 1 := by
        rw [hgammaEq]
        exact relativeDensity_le_one Atest Q hAtestSub
      let p := CyclicQuantitativeBounds.localMoment gamma
      have hp : p ≠ 0 :=
        CyclicQuantitativeBounds.localMoment_ne_zero hgamma0 hgamma1
      have hpEven : Even p := CyclicQuantitativeBounds.localMoment_even gamma
      have hgammaFactor : gamma⁻¹ ^ ((p : ℝ)⁻¹) ≤ 2 :=
        CyclicQuantitativeBounds.gamma_inv_rpow_inv_localMoment_le_two
          hgamma0 hgamma1
      have hK2regular :
          (10 * m) * (K2.dilate (tk + dk)).carrier.card ≤
            (10 * m + 1) * (K2.dilate (tk - dk)).carrier.card := by
        change
          (10 * m) *
              ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
                (tk + dk)).carrier.card ≤
            (10 * m + 1) *
              ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
                (tk - dk)).carrier.card
        simpa only [← CyclicTwoScaleLifting.doubleBohr_dilate,
          CyclicTwoScaleLifting.card_carrier_doubleBohr] using hKregular
      have hmain : (1 / 2 : ℝ) ≤
          |(P.card : ℝ) *
            ⟪μ_[ℝ] Aout ∗ᵈ μ_[ℝ] Aout, μ_[ℝ] C⟫_[ℝ] - 1| := by
        simpa [C] using
          CyclicTwoScaleLifting.half_le_abs_scaled_correlation_on_subset
            (G := ZMod N) (by simpa [ZMod.card] using hN)
            P Aout Atest hAtest hAtestAout hfreeOut hcard
      have hCstable : C ⊆ (J.dilate dj).carrier :=
        hCD.trans (by simpa [D, K2] using hDoubleTestStable)
      have hW : W.Nonempty := CyclicBohr.Set.carrier_nonempty _
      have hV : V.Nonempty := CyclicBohr.Set.carrier_nonempty _
      have herrorOut :
          3 * (1 / ((5 * m : ℕ) * betaOut)) ≤ (1 / 16 : ℝ) / 4 := by
        have hcoef0 : (0 : ℝ) < ((5 * m : ℕ) : ℝ) := by positivity
        have hdenlow : 0 <
            ((5 * m : ℕ) : ℝ) * ((1 - 1 / 8192 : ℝ) * s.beta) :=
          mul_pos hcoef0 hlow0
        have hdenle :
            ((5 * m : ℕ) : ℝ) * ((1 - 1 / 8192 : ℝ) * s.beta) ≤
              ((5 * m : ℕ) : ℝ) * betaOut :=
          mul_le_mul_of_nonneg_left hbetaGood hcoef0.le
        have hinv :
            1 / (((5 * m : ℕ) : ℝ) * betaOut) ≤
              1 / (((5 * m : ℕ) : ℝ) *
                ((1 - 1 / 8192 : ℝ) * s.beta)) :=
          one_div_le_one_div_of_le hdenlow hdenle
        exact (mul_le_mul_of_nonneg_left hinv (by norm_num)).trans herror
      have hlarge : (1 / 16 : ℝ) ≤
          ‖P.card •
            (CyclicRelativeLifting.relativeBalance Aout P ○ᵈ
              CyclicRelativeLifting.relativeBalance Aout P)‖_[p,
                CyclicPositiveDefiniteLifting.positiveDefiniteWeight W V] := by
        have hraw :=
          CyclicTwoScaleLifting.large_positiveDefinite_norm_of_two_scale_correlation_gap
            J K2 Aout C W V m p
            (t := tj) (delta := dj) (v := tk) (eta := dk)
            (alpha := betaOut) (gamma := gamma) (epsilon := (1 / 2 : ℝ))
            (by positivity) hp hpEven hbetaOut0 hgamma0 (by norm_num)
            hdj hdjtj hJregular hdk hdktk hK2regular hAout hC
            hAoutSub (by simpa [betaOut, P] using
              (relativeDensity_mul_card Aout P hP).le)
            hCstable hCD (by simpa [gamma, D] using
              (relativeDensity_mul_card C D
                (CyclicBohr.Set.carrier_nonempty _)).le)
            hgammaFactor hW hV
            (by simpa [W, K2] using hWeightInner)
            (by simpa [V, K2] using hRinnerInner)
            (herrorOut.trans (by norm_num)) hmain
        have hepsilon : (1 / 2 : ℝ) / 8 = 1 / 16 := by norm_num
        rw [hepsilon] at hraw
        simpa only [P] using hraw
      have hlogGamma : CyclicQuantitativeBounds.curLog gamma ≤
          4 * CyclicQuantitativeBounds.curLog s.beta := by
        apply CyclicQuantitativeBounds.curLog_le_four_of_fixed_narrowing
          s.beta_pos s.beta_le_one hgamma1
        rw [hgammaEq]
        exact hgammaGood
      have hlogBetaOut : CyclicQuantitativeBounds.curLog betaOut ≤
          4 * CyclicQuantitativeBounds.curLog s.beta :=
        CyclicQuantitativeBounds.curLog_le_four_of_fixed_narrowing
          s.beta_pos s.beta_le_one hbetaOut1 hbetaGood
      obtain ⟨Cbohr, vnext, xinext, y, hCradius0, hRrankC,
          hRankR, hRadiusC, hv0, hv1, hxi, hxi0, hxiv, hCregular, hCsmall,
          hslice, hfree, hdense⟩ :=
        CyclicQuantitativeBounds.exists_positive_density_increment_slice_with_controlled_rank
          J R Aout W V m p m
          (CyclicQuantitativeBounds.curLog s.beta)
          (t := tj) (delta := dj) (vr := vr) (eta := eta)
          (beta := betaOut) (by positivity) hp hbetaOut0 hbetaOut1
          hRradius hRrank (by positivity) hdj.le
          (sub_nonneg.mpr hdjtj.le) heta hetavr.le hJregular hRregular
          hAout hAoutSub
          (by simpa [betaOut, P] using relativeDensity_mul_card Aout P hP)
          hW hV rfl hWeightOuter hRinnerOuter hRsmall herrorOut hlarge
          hfreeOut
          (CyclicQuantitativeBounds.one_le_curLog s.beta_pos s.beta_le_one)
          hlogBetaOut
          (by
            intro p' q hp'bound hqFormula
            have hqGamma := CyclicQuantitativeBounds.local_q_le
              hgamma0 hgamma1 (by simpa only [p] using hp'bound) hqFormula
            calc
              (q : ℝ) ≤
                  2 ^ 24 * CyclicQuantitativeBounds.curLog gamma := hqGamma
              _ ≤ 2 ^ 24 *
                  (4 * CyclicQuantitativeBounds.curLog s.beta) := by gcongr
              _ = 2 ^ 26 * CyclicQuantitativeBounds.curLog s.beta := by
                norm_num
                ring)
          (by
            intro xshift A₁ A₂ U hA₁W hA₂V hUsub
            apply CyclicQuantitativeBounds.sifted_support_card_le_nine_mul_inner
              H A₁ A₂ V U xshift hzeta.le hzetau.le
            · simpa only [W] using hA₁W
            · simpa only [V] using hA₂V
            · simpa only [V] using hRinnerH
            · exact hUsub
            · exact hHregular)
      have hRankNew : (Cbohr.rank : ℝ) ≤ (s.B.rank : ℝ) +
          2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6 := by
        simpa only [hRrankState] using hRankR
      have hStepRadiusC : s.stepRadiusFloor ≤ Cbohr.radius :=
        s.stepRadiusFloor_le_of_controlled R Cbohr hRrankState
          hReferenceRadius hbetaGood (by
            simpa only [State.entropyBudget] using hRadiusC)
      let Anew :=
        CyclicDensityIncrement.normalizedSlice Aout
          (Cbohr.dilate vnext).carrier y
      let betaNew := relativeDensity Anew (Cbohr.dilate vnext).carrier
      have hdenseA : (1 + 1 / 1024 : ℝ) * betaOut ≤
          (Anew.card : ℝ) / (Cbohr.dilate vnext).carrier.card := by
        dsimp only [Anew]
        convert hdense using 1 <;> norm_num
      have hAnew : Anew.Nonempty := by
        apply nonempty_of_positive_density Anew
          (Cbohr.dilate vnext).carrier
          (alpha := (1 + 1 / 1024 : ℝ) * betaOut)
          (mul_pos (by norm_num) hbetaOut0)
          (Cbohr.dilate vnext).carrier_nonempty
        exact hdenseA
      have hbetaNew0 : 0 < betaNew :=
        relativeDensity_pos _ _ hAnew (Cbohr.dilate vnext).carrier_nonempty
      have hbetaNew1 : betaNew ≤ 1 := by
        apply relativeDensity_le_one
        simpa [Anew] using hslice
      have hgain : (1 + 1 / 32768 : ℝ) * s.beta ≤ betaNew := by
        have hnew : (1 + 1 / 1024 : ℝ) * betaOut ≤ betaNew := by
          simpa [betaNew, relativeDensity] using hdenseA
        calc
          (1 + 1 / 32768 : ℝ) * s.beta ≤
              (1 + 1 / 1024 : ℝ) *
                ((1 - 1 / 8192 : ℝ) * s.beta) := by
            nlinarith [s.beta_pos]
          _ ≤ (1 + 1 / 1024 : ℝ) * betaOut := by gcongr
          _ ≤ betaNew := hnew
      left
      exact exists_increment_state s Cbohr Anew hCradius0
        (hRrank.trans_le hRrankC) hv0 hv1 hxi0 hxiv hxi hCregular hAnew
        (by simpa [Anew] using hslice) hbetaNew0 hbetaNew1
        (relativeDensity_mul_card _ _ (Cbohr.dilate vnext).carrier_nonempty)
        (by simpa [Anew] using hfree) hgain hRankNew hStepRadiusC
    · right
      have hterminal : Aout.card ^ 2 < 2 * P.card := by omega
      exact exists_terminal_state s J Aout hJradius hJrank htj0 htj1
        hdj hdjtj hdjFormula hJregular hAout hAoutSub hbetaOut0 hbetaOut1
        (relativeDensity_mul_card _ _ hP) hfreeOut hbetaGood
        (by simpa only [P] using hterminal)
        (by
          rw [hJrankState]
          exact le_add_of_nonneg_right (by positivity)) hFloorJ
  · obtain ⟨x, hinc⟩ := hPinc
    left
    simpa only [P] using outer_increment_outcome s J hJradius hJrank
      htj0 htj1 hdj hdjtj hdjFormula hJregular hJrankState hFloorJ x hinc
  · obtain ⟨x, hinc⟩ := hQinc
    left
    simpa only [Q] using inner_increment_outcome s K hm hKradius hKrank
      htk0 htk1 hdk hdktk hdkFormula hKregular hKrankState hFloorK x hinc

end CyclicNestedDensityStep
end Erdos721
