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

import ErdosProblems.Erdos1165.ExternalProposition44
import ErdosProblems.Erdos1165.ExternalQuantitativeRenewal
import ErdosProblems.Erdos1165.ExternalGreenRenewal
import ErdosProblems.Erdos1165.ExternalGreenCoeff
import ErdosProblems.Erdos1165.ExternalHLOZArithmetic
import ErdosProblems.Erdos1165.ExternalSharpOnePoint
import ErdosProblems.Erdos1165.ExternalGreenTauberian
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The sharp external-walk one-point tail at the HLOZ scale

This file turns two coefficient estimates for the retained-block external
walk into the exact one-point local-time tail used in HLOZ Proposition 4.4.
The renewal comparison is made at a distant horizon
`exp(L + sqrt L)`, where `L` is the logarithm of the HLOZ time cutoff.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165.ExternalHLOZOnePoint

open ExternalWalk ExternalOnePoint LazyDecomposition
open Erdos1165.ExternalGreenRenewal
open ExternalQuantitativeRenewal ExternalProposition44
open Erdos1165.ExternalSharpOnePoint
open Erdos1165.QuantitativeRenewal

noncomputable section

/-- The sharp reciprocal coefficient of the retained-block external walk. -/
noncomputable def externalSharpCoefficient : ℝ :=
  15 / (16 * Real.pi)

/-- A distant comparison horizon for the finite renewal rectangle. -/
noncomputable def hlozComparisonHorizon44 (m : ℕ) : ℕ :=
  ⌈Real.exp (levelCutoffLog hlozDelta44 m +
    Real.sqrt (levelCutoffLog hlozDelta44 m))⌉₊

/-- Abelian parameter used beyond the distant renewal-comparison horizon.
The extra `sqrt L` separates it from `hlozComparisonHorizon44`, while its
logarithm still differs from the original HLOZ logarithmic scale only by a
lower-order term. -/
noncomputable def hlozAbelParameter44 (m : ℕ) : ℝ :=
  Real.exp (levelCutoffLog hlozDelta44 m +
    2 * Real.sqrt (levelCutoffLog hlozDelta44 m))

/-- The sublinear error allowed in the sharp truncated-Green estimate. -/
noncomputable def externalGreenErrorScale (N : ℕ) : ℝ :=
  32 * Real.log (N + 2) ^ (3 / 5 : ℝ)

/-- Denominator in the quantitative renewal lower bound. -/
noncomputable def hlozRenewalDenominator44 (m : ℕ) : ℝ :=
  1 + externalSharpCoefficient *
      (1 + Real.log (hlozComparisonHorizon44 m)) +
    externalGreenErrorScale (hlozComparisonHorizon44 m)

/-- Total numerator loss in the distant-horizon renewal bound. -/
noncomputable def hlozRenewalLoss44 (m : ℕ) : ℝ :=
  (externalSharpCoefficient + 2 / 5) *
    (hlozCutoff44 m : ℝ) / (hlozComparisonHorizon44 m + 1 : ℝ)

/-- The exact sharp truncated-Green input required below. -/
def HasSharpExternalGreenUpper (o : Orientation) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    externalTruncatedGreenCount o N ≤
      externalSharpCoefficient * Real.log (N + 2) +
        externalGreenErrorScale N

/-- The elementary uniform coefficient input used for the distant Green
increment. -/
def HasExternalReturnCoefficientUpper (o : Orientation) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ExternalRenewal.externalReturnProbability o n ≤
      2 / (5 * (n + 1) : ℝ)

lemma externalSharpCoefficient_pos : 0 < externalSharpCoefficient := by
  unfold externalSharpCoefficient
  positivity

lemma externalSharpCoefficient_nonneg : 0 ≤ externalSharpCoefficient :=
  externalSharpCoefficient_pos.le

lemma externalSharpCoefficient_lt_five_sixteenths :
    externalSharpCoefficient < 5 / 16 := by
  unfold externalSharpCoefficient
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * Real.pi)]
  nlinarith [Real.pi_gt_three]

lemma twenty_five_eighty_four_lt_externalSharpCoefficient :
    25 / 84 < externalSharpCoefficient := by
  unfold externalSharpCoefficient
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 84)
    (by positivity : (0 : ℝ) < 16 * Real.pi)]
  nlinarith [Real.pi_lt_d2]

lemma externalSharpCoefficient_le_one : externalSharpCoefficient ≤ 1 := by
  exact (externalSharpCoefficient_lt_five_sixteenths.trans (by norm_num)).le

lemma tendsto_hlozCutoffLog44 :
    Tendsto (fun m : ℕ ↦ levelCutoffLog hlozDelta44 m) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show ∀ᶠ m : ℕ in atTop,
      levelCutoffLeading m ≤ levelCutoffLog hlozDelta44 m by
        filter_upwards [] with m
        exact le_add_of_nonneg_right
          (levelCutoffCorrection_nonneg hlozDelta44 m))
  exact tendsto_levelCutoffLeading

/-- Powers of the HLOZ logarithmic scale absorb every fixed multiple of a
smaller power. -/
lemma eventually_const_mul_hlozLog_rpow_le (C a b : ℝ) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop,
      C * levelCutoffLog hlozDelta44 m ^ a ≤
        levelCutoffLog hlozDelta44 m ^ b := by
  let L : ℕ → ℝ := fun m ↦ levelCutoffLog hlozDelta44 m
  have ht : Tendsto (fun m : ℕ ↦ L m ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_hlozCutoffLog44
  filter_upwards [ht.eventually (eventually_ge_atTop C),
      tendsto_hlozCutoffLog44.eventually (eventually_ge_atTop 1)]
      with m hmPow hm
  have hL : 0 < L m := zero_lt_one.trans_le hm
  calc
    C * L m ^ a ≤ L m ^ (b - a) * L m ^ a := by
      exact mul_le_mul_of_nonneg_right hmPow (Real.rpow_nonneg hL.le _)
    _ = L m ^ b := by
      rw [mul_comm, ← Real.rpow_add hL]
      congr 1
      ring

lemma tendsto_hlozLog_mul_exp_neg_sqrt :
    Tendsto (fun m : ℕ ↦
      levelCutoffLog hlozDelta44 m *
        Real.exp (-Real.sqrt (levelCutoffLog hlozDelta44 m)))
      atTop (nhds 0) := by
  have hsqrt : Tendsto
      (fun m : ℕ ↦ Real.sqrt (levelCutoffLog hlozDelta44 m))
      atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_hlozCutoffLog44
  have h :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 1 (by norm_num)).comp
      hsqrt
  apply h.congr'
  filter_upwards [] with m
  let L := levelCutoffLog hlozDelta44 m
  have hL0 : 0 ≤ L := levelCutoffLog_nonneg hlozDelta44 m
  dsimp [L]
  rw [Real.rpow_two, Real.sq_sqrt hL0]
  congr 2
  ring

lemma hlozComparisonHorizon44_pos (m : ℕ) :
    0 < hlozComparisonHorizon44 m := by
  unfold hlozComparisonHorizon44
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

lemma exp_hlozComparisonExponent_le (m : ℕ) :
    Real.exp (levelCutoffLog hlozDelta44 m +
        Real.sqrt (levelCutoffLog hlozDelta44 m)) ≤
      (hlozComparisonHorizon44 m : ℝ) := by
  exact Nat.le_ceil _

lemma hlozComparisonHorizon44_cast_lt (m : ℕ) :
    (hlozComparisonHorizon44 m : ℝ) <
      Real.exp (levelCutoffLog hlozDelta44 m +
        Real.sqrt (levelCutoffLog hlozDelta44 m)) + 1 := by
  simpa [hlozComparisonHorizon44] using
    (Nat.ceil_lt_add_one (Real.exp_nonneg
      (levelCutoffLog hlozDelta44 m +
        Real.sqrt (levelCutoffLog hlozDelta44 m))))

lemma log_hlozComparisonHorizon44_lt (m : ℕ) :
    Real.log (hlozComparisonHorizon44 m) <
      levelCutoffLog hlozDelta44 m +
        Real.sqrt (levelCutoffLog hlozDelta44 m) + 1 := by
  let A := levelCutoffLog hlozDelta44 m +
    Real.sqrt (levelCutoffLog hlozDelta44 m)
  have hA : 0 ≤ A := add_nonneg
    (levelCutoffLog_nonneg hlozDelta44 m) (Real.sqrt_nonneg _)
  have hceil := hlozComparisonHorizon44_cast_lt m
  have hone : (1 : ℝ) ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  have htwo : ((hlozComparisonHorizon44 m : ℕ) : ℝ) <
      2 * Real.exp A := by
    dsimp [A] at hceil ⊢
    linarith
  have hpos : (0 : ℝ) < hlozComparisonHorizon44 m := by
    exact_mod_cast hlozComparisonHorizon44_pos m
  have hlog := Real.log_lt_log hpos htwo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hlogTwo : Real.log (2 : ℝ) < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  nlinarith

lemma log_hlozComparisonHorizon44_add_two_le (m : ℕ) :
    Real.log (hlozComparisonHorizon44 m + 2) ≤
      levelCutoffLog hlozDelta44 m +
        Real.sqrt (levelCutoffLog hlozDelta44 m) + 2 := by
  let A := levelCutoffLog hlozDelta44 m +
    Real.sqrt (levelCutoffLog hlozDelta44 m)
  have hA : 0 ≤ A := add_nonneg
    (levelCutoffLog_nonneg hlozDelta44 m) (Real.sqrt_nonneg _)
  have hceil := hlozComparisonHorizon44_cast_lt m
  have hone : (1 : ℝ) ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  have hfour : (((hlozComparisonHorizon44 m + 2 : ℕ) : ℝ)) <
      4 * Real.exp A := by
    push_cast
    dsimp [A] at hceil ⊢
    linarith
  have hpos : (0 : ℝ) < (hlozComparisonHorizon44 m + 2 : ℕ) := by
    positivity
  have hlog := Real.log_lt_log hpos hfour
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hlogFour : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
    have hlogTwo : Real.log (2 : ℝ) < 1 := by
      nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)]
    linarith
  have hlog' : Real.log (((hlozComparisonHorizon44 m + 2 : ℕ) : ℝ)) ≤
      A + 2 := by
    linarith
  simpa [A, Nat.cast_add, Nat.cast_ofNat] using hlog'

lemma hlozAbelParameter44_one_le (m : ℕ) :
    1 ≤ hlozAbelParameter44 m := by
  unfold hlozAbelParameter44
  rw [Real.one_le_exp_iff]
  exact add_nonneg (levelCutoffLog_nonneg hlozDelta44 m)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

@[simp] lemma log_hlozAbelParameter44 (m : ℕ) :
    Real.log (hlozAbelParameter44 m) =
      levelCutoffLog hlozDelta44 m +
        2 * Real.sqrt (levelCutoffLog hlozDelta44 m) := by
  simp [hlozAbelParameter44]

lemma hlozComparison_div_abel_le (m : ℕ) :
    (hlozComparisonHorizon44 m : ℝ) / hlozAbelParameter44 m ≤
      2 * Real.exp (-Real.sqrt (levelCutoffLog hlozDelta44 m)) := by
  let L := levelCutoffLog hlozDelta44 m
  let s := Real.sqrt L
  let M := hlozComparisonHorizon44 m
  let D := hlozAbelParameter44 m
  have hL0 : 0 ≤ L := levelCutoffLog_nonneg hlozDelta44 m
  have hA0 : 0 ≤ L + s := add_nonneg hL0 (Real.sqrt_nonneg _)
  have hceil := hlozComparisonHorizon44_cast_lt m
  have hone : (1 : ℝ) ≤ Real.exp (L + s) := Real.one_le_exp_iff.mpr hA0
  have hM : (M : ℝ) ≤ 2 * Real.exp (L + s) := by
    dsimp [L, s, M] at hceil hone ⊢
    linarith
  have hDpos : 0 < D := by
    dsimp [D, hlozAbelParameter44]
    positivity
  apply (div_le_iff₀ hDpos).2
  calc
    (M : ℝ) ≤ 2 * Real.exp (L + s) := hM
    _ = (2 * Real.exp (-s)) * D := by
      dsimp [D, hlozAbelParameter44]
      have hexp : Real.exp (L + s) =
          Real.exp (-s) * Real.exp (L + 2 * Real.sqrt L) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [s]
        ring
      rw [hexp]
      ring

lemma one_div_hlozAbelParameter44_le (m : ℕ)
    (hL : 0 < levelCutoffLog hlozDelta44 m) :
    1 / hlozAbelParameter44 m ≤
      1 / levelCutoffLog hlozDelta44 m := by
  let L := levelCutoffLog hlozDelta44 m
  have hD : L ≤ hlozAbelParameter44 m := by
    calc
      L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
      _ ≤ hlozAbelParameter44 m := by
        unfold hlozAbelParameter44
        exact Real.exp_le_exp.mpr
          (le_add_of_nonneg_right
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg L)))
  exact one_div_le_one_div_of_le hL hD

lemma tendsto_hlozComparisonHorizon44 :
    Tendsto hlozComparisonHorizon44 atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun m ↦ ?_)
    (tendsto_levelCutoffTime hlozDelta44)
  unfold hlozComparisonHorizon44 levelCutoffTime levelCutoff
  apply Nat.ceil_mono
  apply Real.exp_le_exp.mpr
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

lemma log_nat_add_two_le_one_add_log_nat_add_one (N : ℕ) :
    Real.log ((N : ℝ) + 2) ≤ 1 + Real.log ((N : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcast : (N : ℝ) + 2 ≤ 2 * ((N : ℝ) + 1) := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  calc
    Real.log ((N : ℝ) + 2) ≤ Real.log (2 * ((N : ℝ) + 1)) :=
      Real.log_le_log (by positivity) hcast
    _ = Real.log 2 + Real.log ((N : ℝ) + 1) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpos.ne']
    _ ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have hlogTwo : Real.log (2 : ℝ) < 1 := by
        nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (2 : ℝ) ≠ 1)]
      linarith

lemma returnCoefficientUpper_weakened {o : Orientation}
    (hq : HasExternalReturnCoefficientUpper o) (n : ℕ) (hn : 1 ≤ n) :
    ExternalRenewal.externalReturnProbability o n ≤
      (2 / 5 : ℝ) / n := by
  refine (hq n hn).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (n + 1)) hnR).2
  nlinarith

/-- The sharp Green bound supplies the global reciprocal remainder estimate
at the distant comparison horizon. -/
theorem eventually_externalRemainder_global44 (o : Orientation)
    (hgreen : HasSharpExternalGreenUpper o) :
    ∀ᶠ m : ℕ in atTop,
      externalReciprocalRemainderSum o externalSharpCoefficient
          (hlozComparisonHorizon44 m) ≤
        externalGreenErrorScale (hlozComparisonHorizon44 m) := by
  have hgreenM := tendsto_hlozComparisonHorizon44.eventually hgreen
  filter_upwards [hgreenM] with m hG
  let M := hlozComparisonHorizon44 m
  let E := externalGreenErrorScale M
  have hlog := log_nat_add_two_le_one_add_log_nat_add_one M
  have hG' : RenewalTail.truncatedGreen
        (ExternalRenewal.externalReturnProbability o) M ≤
      1 + externalSharpCoefficient * Real.log (M + 1) + E := by
    change ExternalRenewal.externalTruncatedGreenReal o M ≤ _
    rw [← ExternalGreenRenewal.externalTruncatedGreenCount_eq_renewal]
    calc
      externalTruncatedGreenCount o M ≤
          externalSharpCoefficient * Real.log (M + 2) + E := hG
      _ ≤ 1 + externalSharpCoefficient * Real.log (M + 1) + E := by
        have hc := externalSharpCoefficient_nonneg
        have hc1 := externalSharpCoefficient_le_one
        nlinarith [mul_le_mul_of_nonneg_left hlog hc]
  exact ExternalGreenCoeff.reciprocalRemainderSum_le_of_truncatedGreen_le
    (ExternalRenewal.externalReturnProbability o)
    externalSharpCoefficient E M
    (ExternalRenewal.externalReturnProbability_zero o)
    externalSharpCoefficient_nonneg hG'

/-- The reciprocal coefficient bound makes the accumulated-remainder
increment over the original cutoff uniformly tiny at the distant horizon. -/
theorem externalRemainder_increment44 (o : Orientation)
    (hq : HasExternalReturnCoefficientUpper o) (m : ℕ) :
    externalReciprocalRemainderSum o externalSharpCoefficient
          (hlozCutoff44 m + hlozComparisonHorizon44 m) -
        externalReciprocalRemainderSum o externalSharpCoefficient
          (hlozComparisonHorizon44 m) ≤
      (2 / 5 : ℝ) * (hlozCutoff44 m : ℝ) /
        (hlozComparisonHorizon44 m + 1 : ℝ) := by
  exact ExternalGreenCoeff.reciprocalRemainderSum_increment_le_of_reciprocal_upper
    (ExternalRenewal.externalReturnProbability o)
    externalSharpCoefficient (2 / 5) (hlozComparisonHorizon44 m)
    (hlozCutoff44 m) (ExternalRenewal.externalReturnProbability_zero o)
    externalSharpCoefficient_nonneg (by norm_num)
    (returnCoefficientUpper_weakened hq)

lemma eventually_externalGreenErrorScale_comparison44 :
    ∀ᶠ m : ℕ in atTop,
      externalGreenErrorScale (hlozComparisonHorizon44 m) ≤
        96 * levelCutoffLog hlozDelta44 m ^ (3 / 5 : ℝ) := by
  filter_upwards
      [tendsto_hlozCutoffLog44.eventually (eventually_ge_atTop 2)]
      with m hL
  let L := levelCutoffLog hlozDelta44 m
  let M := hlozComparisonHorizon44 m
  have hL0 : 0 ≤ L := zero_le_two.trans hL
  have hsqrt : Real.sqrt L ≤ L := (Real.sqrt_le_left hL0).2 (by nlinarith)
  have hlog : Real.log (M + 2) ≤ 3 * L := by
    have h := log_hlozComparisonHorizon44_add_two_le m
    dsimp [L, M] at h ⊢
    linarith
  have hlog0 : 0 ≤ Real.log (M + 2) := by
    apply Real.log_nonneg
    norm_cast
    omega
  have hpow := Real.rpow_le_rpow hlog0 hlog
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hthree : (3 : ℝ) ^ (3 / 5 : ℝ) ≤ 3 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ))
        (y := (3 / 5 : ℝ)) (z := 1) (by norm_num) (by norm_num))
  unfold externalGreenErrorScale
  calc
    32 * Real.log (M + 2) ^ (3 / 5 : ℝ) ≤
        32 * (3 * L) ^ (3 / 5 : ℝ) := by gcongr
    _ = 32 * (3 ^ (3 / 5 : ℝ) * L ^ (3 / 5 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hL0]
    _ ≤ 96 * L ^ (3 / 5 : ℝ) := by
      have hmul : 3 ^ (3 / 5 : ℝ) * L ^ (3 / 5 : ℝ) ≤
          3 * L ^ (3 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hthree
          (Real.rpow_nonneg hL0 (3 / 5 : ℝ))
      nlinarith

/-- The distant-horizon denominator has the sharp leading term
`(15/(16π)) L`; every other contribution is absorbed by `L^(5/8)/4`. -/
theorem eventually_hlozRenewalDenominator44 :
    ∀ᶠ m : ℕ in atTop,
      0 < hlozRenewalDenominator44 m ∧
      hlozRenewalDenominator44 m ≤
        externalSharpCoefficient * levelCutoffLog hlozDelta44 m +
          levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ) / 4 := by
  filter_upwards
      [tendsto_hlozCutoffLog44.eventually (eventually_ge_atTop 2),
       eventually_const_mul_hlozLog_rpow_le 16 (1 / 2) (5 / 8) (by norm_num),
       eventually_const_mul_hlozLog_rpow_le 48 0 (5 / 8) (by norm_num),
       eventually_const_mul_hlozLog_rpow_le 1536 (3 / 5) (5 / 8) (by norm_num),
       eventually_externalGreenErrorScale_comparison44]
      with m hL hsqrtAbs hconstAbs herrorAbs herror
  let L := levelCutoffLog hlozDelta44 m
  let M := hlozComparisonHorizon44 m
  let t := L ^ (5 / 8 : ℝ)
  have hL0 : 0 ≤ L := zero_le_two.trans hL
  have hlogM0 : 0 ≤ Real.log M := by
    apply Real.log_nonneg
    norm_cast
    exact hlozComparisonHorizon44_pos m
  have hE0 : 0 ≤ externalGreenErrorScale M := by
    unfold externalGreenErrorScale
    have harg : (1 : ℝ) ≤ (M : ℝ) + 2 := by
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (Real.log_nonneg harg) _)
  have hpos : 0 < hlozRenewalDenominator44 m := by
    unfold hlozRenewalDenominator44
    have hc0 := externalSharpCoefficient_nonneg
    have honeLog : 0 ≤ 1 + Real.log M := by linarith
    dsimp [M] at hlogM0 hE0 ⊢
    nlinarith [mul_nonneg hc0 honeLog]
  refine ⟨hpos, ?_⟩
  have hlog := (log_hlozComparisonHorizon44_lt m).le
  have hsqrtEq : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
  have hsqrtSmall : Real.sqrt L ≤ t / 16 := by
    rw [hsqrtEq]
    dsimp [L, t] at hsqrtAbs ⊢
    nlinarith
  have hconstSmall : (3 : ℝ) ≤ t / 16 := by
    have hLpow0 : L ^ (0 : ℝ) = 1 := Real.rpow_zero L
    rw [hLpow0] at hconstAbs
    dsimp [L, t] at hconstAbs ⊢
    nlinarith
  have herrorSmall : 96 * L ^ (3 / 5 : ℝ) ≤ t / 16 := by
    dsimp [L, t] at herrorAbs ⊢
    nlinarith
  have hc1 := externalSharpCoefficient_le_one
  have hc0 := externalSharpCoefficient_nonneg
  have ht0 : 0 ≤ t := Real.rpow_nonneg hL0 _
  have hrough : hlozRenewalDenominator44 m ≤
      externalSharpCoefficient * L + Real.sqrt L + 3 +
        96 * L ^ (3 / 5 : ℝ) := by
    unfold hlozRenewalDenominator44
    dsimp [L, M] at hlog ⊢
    change externalGreenErrorScale M ≤ 96 * L ^ (3 / 5 : ℝ) at herror
    nlinarith [mul_le_mul_of_nonneg_left hlog hc0,
      mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg L)]
  calc
    hlozRenewalDenominator44 m ≤
        externalSharpCoefficient * L + Real.sqrt L + 3 +
          96 * L ^ (3 / 5 : ℝ) := hrough
    _ ≤ externalSharpCoefficient * L + t / 4 := by
      have hsum := add_le_add (add_le_add hsqrtSmall hconstSmall) herrorSmall
      calc
        externalSharpCoefficient * L + Real.sqrt L + 3 +
            96 * L ^ (3 / 5 : ℝ) ≤
          externalSharpCoefficient * L + (t / 16 + t / 16 + t / 16) := by
            simpa only [add_assoc, add_left_comm, add_comm] using
              (add_le_add_left hsum (externalSharpCoefficient * L))
        _ ≤ externalSharpCoefficient * L + t / 4 := by
          ring_nf at *
          linarith
    _ = _ := by rfl

lemma hlozCutoff44_cast_le_three_exp (m : ℕ) :
    (hlozCutoff44 m : ℝ) ≤
      3 * Real.exp (levelCutoffLog hlozDelta44 m) := by
  have h := hlozCutoff44_cast_add_one_le m
  push_cast at h
  linarith

lemma hlozCutoff_div_comparison_le (m : ℕ) :
    (hlozCutoff44 m : ℝ) /
        (hlozComparisonHorizon44 m + 1 : ℝ) ≤
      3 * Real.exp (-Real.sqrt (levelCutoffLog hlozDelta44 m)) := by
  let L := levelCutoffLog hlozDelta44 m
  let M := hlozComparisonHorizon44 m
  change (hlozCutoff44 m : ℝ) / ((M : ℝ) + 1) ≤
    3 * Real.exp (-Real.sqrt L)
  have hM : Real.exp (L + Real.sqrt L) ≤ (M : ℝ) := by
    simpa [L, M] using exp_hlozComparisonExponent_le m
  have hden : Real.exp (L + Real.sqrt L) ≤ (M : ℝ) + 1 := by linarith
  have hdenPos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hdenPos).2
  calc
    (hlozCutoff44 m : ℝ) ≤ 3 * Real.exp L := by
      simpa [L] using hlozCutoff44_cast_le_three_exp m
    _ = 3 * Real.exp (-Real.sqrt L) *
        Real.exp (L + Real.sqrt L) := by
      have hexp : Real.exp L =
          Real.exp (-Real.sqrt L) * Real.exp (L + Real.sqrt L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ ≤ 3 * Real.exp (-Real.sqrt L) * ((M : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

/-- The total numerator loss is eventually at most `1/L`. -/
theorem eventually_hlozRenewalLoss44 :
    ∀ᶠ m : ℕ in atTop,
      0 ≤ hlozRenewalLoss44 m ∧
      hlozRenewalLoss44 m ≤
        1 / levelCutoffLog hlozDelta44 m := by
  have hsmall : ∀ᶠ m : ℕ in atTop,
      levelCutoffLog hlozDelta44 m *
          Real.exp (-Real.sqrt (levelCutoffLog hlozDelta44 m)) ≤ 1 / 3 :=
    tendsto_hlozLog_mul_exp_neg_sqrt.eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards
      [hsmall,
       tendsto_hlozCutoffLog44.eventually (eventually_gt_atTop 0)]
      with m hsmall hL
  let L := levelCutoffLog hlozDelta44 m
  have hratio0 : 0 ≤ (hlozCutoff44 m : ℝ) /
      (hlozComparisonHorizon44 m + 1 : ℝ) := by positivity
  have hcoef0 : 0 ≤ externalSharpCoefficient + 2 / 5 :=
    add_nonneg externalSharpCoefficient_nonneg (by norm_num)
  have hcoef1 : externalSharpCoefficient + 2 / 5 ≤ 1 := by
    nlinarith [externalSharpCoefficient_lt_five_sixteenths.le]
  have hloss0 : 0 ≤ hlozRenewalLoss44 m := by
    unfold hlozRenewalLoss44
    rw [mul_div_assoc]
    exact mul_nonneg hcoef0 hratio0
  refine ⟨hloss0, ?_⟩
  have hratio := hlozCutoff_div_comparison_le m
  have hbase : hlozRenewalLoss44 m ≤
      3 * Real.exp (-Real.sqrt L) := by
    unfold hlozRenewalLoss44
    dsimp [L] at hratio ⊢
    rw [mul_div_assoc]
    calc
      (externalSharpCoefficient + 2 / 5) *
          ((hlozCutoff44 m : ℝ) /
            (hlozComparisonHorizon44 m + 1 : ℝ)) ≤
        (hlozCutoff44 m : ℝ) /
            (hlozComparisonHorizon44 m + 1 : ℝ) := by
          nlinarith
      _ ≤ 3 * Real.exp (-Real.sqrt L) := hratio
  have hexp : 3 * Real.exp (-Real.sqrt L) ≤ 1 / L := by
    apply (le_div_iff₀ (by simpa [L] using hL)).2
    dsimp [L] at hsmall ⊢
    nlinarith
  exact hbase.trans hexp

lemma hlozOnePointThreshold_power_eq (m : ℕ)
    (hL : 0 < levelCutoffLog hlozDelta44 m) :
    levelCutoffLog hlozDelta44 m ^ (13 / 8 : ℝ) =
      levelCutoffLog hlozDelta44 m *
        levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ) := by
  let L := levelCutoffLog hlozDelta44 m
  change L ^ (13 / 8 : ℝ) = L * L ^ (5 / 8 : ℝ)
  calc
    L ^ (13 / 8 : ℝ) = L ^ ((1 : ℝ) + 5 / 8) := by norm_num
    _ = L ^ (1 : ℝ) * L ^ (5 / 8 : ℝ) := Real.rpow_add hL 1 (5 / 8)
    _ = _ := by rw [Real.rpow_one]

/-- Scale and integer-ceiling facts needed by the real tail arithmetic. -/
theorem eventually_hlozOnePointScale44 :
    ∀ᶠ m : ℕ in atTop,
      let L := levelCutoffLog hlozDelta44 m
      let t := L ^ (5 / 8 : ℝ)
      0 < L ∧ 8 * t ≤ L ∧ 10 ≤ t ∧
        1 ≤ hlozOnePointLevel44 m ∧
        (15 / (16 * Real.pi) : ℝ) * L ^ 2 -
            2 * L ^ (13 / 8 : ℝ) - 1 ≤
          ((hlozOnePointLevel44 m - 1 : ℕ) : ℝ) := by
  filter_upwards
      [tendsto_hlozCutoffLog44.eventually (eventually_gt_atTop 0),
       eventually_const_mul_hlozLog_rpow_le 8 (5 / 8) 1 (by norm_num),
       eventually_const_mul_hlozLog_rpow_le 10 0 (5 / 8) (by norm_num)]
      with m hL hscale hten
  let L := levelCutoffLog hlozDelta44 m
  let t := L ^ (5 / 8 : ℝ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hL.le _
  have hscale' : 8 * t ≤ L := by
    dsimp [L, t] at hscale ⊢
    simpa only [Real.rpow_one] using hscale
  have hten' : 10 ≤ t := by
    have hpow0 : L ^ (0 : ℝ) = 1 := Real.rpow_zero L
    dsimp [L, t] at hten ⊢
    rw [hpow0] at hten
    simpa using hten
  have hpower : L ^ (13 / 8 : ℝ) = L * t := by
    simpa [L, t] using hlozOnePointThreshold_power_eq m hL
  have hc : (25 / 84 : ℝ) ≤ externalSharpCoefficient :=
    twenty_five_eighty_four_lt_externalSharpCoefficient.le
  have htheta : 1 ≤
      externalSharpCoefficient * L ^ 2 - 2 * L ^ (13 / 8 : ℝ) := by
    rw [hpower]
    have hL0 := hL.le
    have hLt0 : 0 ≤ L * t := mul_nonneg hL0 ht0
    have hscaleMul : 8 * L * t ≤ L ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hscale' hL0
      nlinarith
    have hcSq : (25 / 84 : ℝ) * L ^ 2 ≤
        externalSharpCoefficient * L ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    have hL80 : (80 : ℝ) ≤ L := by
      calc
        (80 : ℝ) = 8 * 10 := by norm_num
        _ ≤ 8 * t := by gcongr
        _ ≤ L := hscale'
    have hLtLarge : (800 : ℝ) ≤ L * t := by
      have hmul := mul_le_mul hL80 hten' (by norm_num : (0 : ℝ) ≤ 10) hL.le
      norm_num at hmul ⊢
      exact hmul
    have hmain : (50 / 21 : ℝ) * (L * t) ≤
        externalSharpCoefficient * L ^ 2 := by
      calc
        (50 / 21 : ℝ) * (L * t) =
            (25 / 84 : ℝ) * (8 * L * t) := by ring
        _ ≤ (25 / 84 : ℝ) * L ^ 2 := by gcongr
        _ ≤ externalSharpCoefficient * L ^ 2 := hcSq
    nlinarith
  have hceil : hlozOnePointThresholdReal44 m ≤
      (hlozOnePointLevel44 m : ℝ) := by
    unfold hlozOnePointLevel44
    exact Nat.le_ceil _
  have hlevel : 1 ≤ hlozOnePointLevel44 m := by
    have hreal : (1 : ℝ) ≤ (hlozOnePointLevel44 m : ℝ) := by
      apply htheta.trans
      simpa [hlozOnePointThresholdReal44, externalSharpCoefficient] using hceil
    exact_mod_cast hreal
  have hr : externalSharpCoefficient * L ^ 2 -
        2 * L ^ (13 / 8 : ℝ) - 1 ≤
      ((hlozOnePointLevel44 m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlevel, Nat.cast_one]
    have hceil' : externalSharpCoefficient * L ^ 2 -
        2 * L ^ (13 / 8 : ℝ) ≤
        (hlozOnePointLevel44 m : ℝ) := by
      simpa [hlozOnePointThresholdReal44, externalSharpCoefficient, L] using hceil
    linarith
  dsimp [L, t]
  exact ⟨hL, hscale', hten', hlevel,
    by simpa [externalSharpCoefficient, L] using hr⟩

/-- The sharp Green upper bound and the elementary reciprocal coefficient
bound imply the exact HLOZ one-point tail used in Proposition 4.4. -/
theorem hlozSharpExternalOnePointTail44_of_coefficients (o : Orientation)
    (hgreen : HasSharpExternalGreenUpper o)
    (hq : HasExternalReturnCoefficientUpper o) :
    HLOZSharpExternalOnePointTail44 o := by
  have hremGlobal := eventually_externalRemainder_global44 o hgreen
  filter_upwards [hremGlobal, eventually_hlozRenewalDenominator44,
      eventually_hlozRenewalLoss44, eventually_hlozOnePointScale44]
      with m hremGlobal hden hloss hscale
  rcases hden with ⟨hDpos, hDupper⟩
  rcases hloss with ⟨heps0, hepsUpper⟩
  rcases hscale with ⟨hLpos, hscale, hten, hlevel, hr⟩
  let L := levelCutoffLog hlozDelta44 m
  let t := L ^ (5 / 8 : ℝ)
  let n := hlozCutoff44 m
  let M := hlozComparisonHorizon44 m
  let r := hlozOnePointLevel44 m - 1
  let c := externalSharpCoefficient
  let E := externalGreenErrorScale M
  let delta := (2 / 5 : ℝ) * (n : ℝ) / (M + 1 : ℝ)
  let eps := hlozRenewalLoss44 m
  let D := hlozRenewalDenominator44 m
  have hremIncrement := externalRemainder_increment44 o hq m
  have hLone : (1 : ℝ) ≤ L := by
    have ht0 : 0 ≤ t := Real.rpow_nonneg hLpos.le _
    nlinarith
  have hepsOne : eps ≤ 1 := by
    exact hepsUpper.trans ((div_le_one₀ hLpos).2 hLone)
  have hepsEq : c * (n : ℝ) / (M + 1 : ℝ) + delta = eps := by
    dsimp [c, n, M, delta, eps, hlozRenewalLoss44]
    ring
  have hdelta : c * (n : ℝ) / (M + 1 : ℝ) + delta ≤ 1 := by
    rw [hepsEq]
    exact hepsOne
  have htail := externalOriginLocalTime_tail_le_of_remainder
    o r n M c E delta externalSharpCoefficient_nonneg
    (by simpa [c, E, M] using hremGlobal)
    (by simpa [c, E, delta, n, M] using hremIncrement) hdelta
  have harith : (1 - eps) / D * (r : ℝ) ≥ L - 8 * t := by
    exact ExternalHLOZArithmetic.external_tail_lower_bound
      L t D eps r hLpos rfl hscale hten hDpos
      (by simpa [D, c, L, t, externalSharpCoefficient] using hDupper)
      heps0 hepsUpper (by simpa [r, L] using hr)
  have hlogM0 : 0 ≤ Real.log M := by
    apply Real.log_nonneg
    norm_cast
    exact hlozComparisonHorizon44_pos m
  have hE0 : 0 ≤ E := by
    dsimp [E, externalGreenErrorScale]
    have harg : (1 : ℝ) ≤ (M : ℝ) + 2 := by
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (Real.log_nonneg harg) _)
  have hDone : (1 : ℝ) ≤ D := by
    dsimp [D, hlozRenewalDenominator44, M, E]
    have honeLog : 0 ≤ 1 + Real.log (hlozComparisonHorizon44 m) := by
      dsimp [M] at hlogM0
      linarith
    nlinarith [mul_nonneg externalSharpCoefficient_nonneg honeLog]
  let escape := (1 - eps) / D
  have hescape0 : 0 ≤ escape := by
    dsimp [escape]
    exact div_nonneg (sub_nonneg.mpr hepsOne) hDpos.le
  have hescape1 : escape ≤ 1 := by
    apply (div_le_one₀ hDpos).2
    linarith
  have hpowReal : (1 - escape) ^ r ≤
      Real.exp (-L + 8 * t) := by
    calc
      (1 - escape) ^ r ≤ (Real.exp (-escape)) ^ r :=
        pow_le_pow_left₀ (sub_nonneg.mpr hescape1)
          (Real.one_sub_le_exp_neg escape) r
      _ = Real.exp (-(escape * (r : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (-L + 8 * t) := by
        apply Real.exp_le_exp.mpr
        dsimp [escape] at harith ⊢
        linarith
  have hrate : (ENNReal.ofReal (1 - escape)) ^ r ≤
      hlozOnePointRate44 m := by
    calc
      (ENNReal.ofReal (1 - escape)) ^ r =
          ENNReal.ofReal ((1 - escape) ^ r) := by
            symm
            exact ENNReal.ofReal_pow (sub_nonneg.mpr hescape1) r
      _ ≤ ENNReal.ofReal (Real.exp (-L + 8 * t)) :=
        ENNReal.ofReal_le_ofReal hpowReal
      _ = hlozOnePointRate44 m := by
        rfl
  have htail' : externalBlocks o {eta |
      r + 1 ≤ externalOriginLocalTime o eta n} ≤
      (ENNReal.ofReal (1 - escape)) ^ r := by
    rw [hepsEq] at htail
    have hDEq : 1 + c * (1 + Real.log (M : ℝ)) + E = D := by
      rfl
    rw [hDEq] at htail
    simpa [escape] using htail
  have hradd : r + 1 = hlozOnePointLevel44 m := by
    dsimp [r]
    exact Nat.sub_add_cancel hlevel
  simpa [n, hradd] using htail'.trans hrate

/-- The proved finite Tauberian estimate is exactly the sharp Green input
required by the renewal argument. -/
theorem hasSharpExternalGreenUpper (o : Orientation) :
    HasSharpExternalGreenUpper o := by
  simpa [HasSharpExternalGreenUpper, externalSharpCoefficient,
    externalGreenErrorScale] using
    (ExternalGreenTauberian.eventually_externalTruncatedGreenCount_le o)

/-- The checked recurrence for the external return coefficients supplies
the only pointwise input used over the distant comparison interval. -/
theorem hasExternalReturnCoefficientUpper (o : Orientation) :
    HasExternalReturnCoefficientUpper o := by
  intro n hn
  exact ExternalGreenCoeff.externalRenewalReturnProbability_le_two_fifths
    o n hn

/-- HLOZ (7.4), specialized to the exact cutoff, threshold, and error rate
used by Proposition 4.4. -/
theorem hlozSharpExternalOnePointTail44 (o : Orientation) :
    HLOZSharpExternalOnePointTail44 o :=
  hlozSharpExternalOnePointTail44_of_coefficients o
    (hasSharpExternalGreenUpper o) (hasExternalReturnCoefficientUpper o)

/-- Unconditional one-orientation form of HLOZ Proposition 4.4. -/
theorem eventually_hlozExternalThickCount_failure44 (o : Orientation) :
    ∀ᶠ m : ℕ in atTop,
      externalBlocks o {eta |
          hlozSiteBudget44 m < externalThickCount o eta
            (hlozCutoff44 m) (hlozThickLevel44 m)} <
        hlozFailureRate44 m :=
  ExternalProposition44.eventually_hloz_externalThickCount_failure44 o
    (hlozSharpExternalOnePointTail44 o)

end

end Erdos1165.ExternalHLOZOnePoint
