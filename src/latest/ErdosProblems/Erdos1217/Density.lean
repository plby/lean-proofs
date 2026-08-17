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

import ErdosProblems.Erdos1217.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# Erdős Problem 1217: the density transfer

This file proves the Abel-summation implication used to pass from positive
lower logarithmic density to positive doubly-harmonic upper density.  The
strong form keeps the sharp constant:

`lowerLogDensity A ≤ weightedRate A`.
-/

open Filter MeasureTheory Finset
open scoped BigOperators ENNReal Interval

namespace Erdos1217

section CofinalBridge

lemma lowerLogDensity_le_lowerLogDensityNat (A : Set ℕ) :
    lowerLogDensity A ≤ lowerLogDensityNat A := by
  unfold lowerLogDensity lowerLogDensityNat
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).liminf_le_liminf_comp
      (u := lowerLogDensityTerm A)
  have hterm : (fun N : ℕ ↦ lowerLogDensityTerm A (N : ℝ)) =
      lowerLogDensityTermNat A := by
    funext N
    simp [lowerLogDensityTerm, lowerLogDensityTermNat, harmonicMass, harmonicMassNat,
      positiveBelow, positiveBelowNat]
  rw [← hterm]
  simpa [Function.comp_def] using h

lemma weightedRateNat_le_weightedRate (A : Set ℕ) :
    weightedRateNat A ≤ weightedRate A := by
  unfold weightedRateNat weightedRate
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).limsup_comp_le_limsup
      (u := weightedTerm A)
  have hterm : (fun N : ℕ ↦ weightedTerm A (N : ℝ)) = weightedTermNat A := by
    funext N
    simp [weightedTerm, weightedTermNat, weightedMass, weightedMassNat,
      positiveBelow, positiveBelowNat]
  rw [← hterm]
  simpa [Function.comp_def] using h

private lemma tendsto_log_ratio_of_ratio {l : Filter ι} {u v : ι → ℝ}
    (huv : Tendsto (fun i ↦ u i / v i) l (nhds 1))
    (hv : Tendsto v l atTop) (hu_pos : ∀ᶠ i in l, 0 < u i)
    (hv_pos : ∀ᶠ i in l, 0 < v i) :
    Tendsto (fun i ↦ Real.log (u i) / Real.log (v i)) l (nhds 1) := by
  have hlogratio : Tendsto (fun i ↦ Real.log (u i / v i)) l (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp huv
  have hsmall : Tendsto (fun i ↦ Real.log (u i / v i) / Real.log (v i)) l (nhds 0) :=
    hlogratio.div_atTop (Real.tendsto_log_atTop.comp hv)
  have hmain := hsmall.add_const 1
  have heq : (fun i ↦ Real.log (u i / v i) / Real.log (v i) + 1) =ᶠ[l]
      fun i ↦ Real.log (u i) / Real.log (v i) := by
    filter_upwards [hu_pos, hv_pos, hv.eventually (eventually_gt_atTop 1)]
      with i hui hvi hvi1
    rw [Real.log_div hui.ne' hvi.ne']
    have hlogv : Real.log (v i) ≠ 0 := (Real.log_pos hvi1).ne'
    field_simp
    ring
  simpa only [zero_add] using hmain.congr' heq

private lemma tendsto_log_log_ceil_div :
    Tendsto (fun x : ℝ ↦
      Real.log (Real.log (⌈x⌉₊ : ℝ)) / Real.log (Real.log x)) atTop (nhds 1) := by
  have hceil : Tendsto (fun x : ℝ ↦ (⌈x⌉₊ : ℝ) / x) atTop (nhds 1) :=
    tendsto_nat_ceil_div_atTop
  have hlog : Tendsto (fun x : ℝ ↦ Real.log (⌈x⌉₊ : ℝ) / Real.log x)
      atTop (nhds 1) := by
    apply tendsto_log_ratio_of_ratio hceil tendsto_id
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact_mod_cast Nat.ceil_pos.mpr hx
    · exact eventually_gt_atTop 0
  apply tendsto_log_ratio_of_ratio hlog (Real.tendsto_log_atTop.comp tendsto_id)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact Real.log_pos <| hx.trans_le (Nat.le_ceil x)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact Real.log_pos hx

private noncomputable def ceilLogLogFactor (x : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.log (Real.log (⌈x⌉₊ : ℝ)) / Real.log (Real.log x))

private lemma tendsto_ceilLogLogFactor :
    Tendsto ceilLogLogFactor atTop (nhds 1) := by
  change Tendsto (fun x : ℝ ↦ ENNReal.ofReal
    (Real.log (Real.log (⌈x⌉₊ : ℝ)) / Real.log (Real.log x))) atTop (nhds 1)
  simpa using ENNReal.tendsto_ofReal tendsto_log_log_ceil_div

private lemma weightedTerm_eq_factor_mul_eventually (A : Set ℕ) :
    ∀ᶠ x : ℝ in atTop,
      weightedTerm A x = ceilLogLogFactor x * weightedTermNat A ⌈x⌉₊ := by
  have hloglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hceilTop : Tendsto (fun x : ℝ ↦ (⌈x⌉₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_ceil_atTop
  have hloglogceil : Tendsto (fun x : ℝ ↦ Real.log (Real.log (⌈x⌉₊ : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hceilTop)
  filter_upwards [hloglog.eventually (eventually_gt_atTop 0),
    hloglogceil.eventually (eventually_gt_atTop 0)] with x hx hceilx
  have hmass : weightedMass A x = weightedMassNat A ⌈x⌉₊ := by
    simp [weightedMass, weightedMassNat, positiveBelow, positiveBelowNat]
  rw [weightedTerm, weightedTermNat, hmass, ceilLogLogFactor]
  rw [← ENNReal.ofReal_mul (div_nonneg hceilx.le hx.le)]
  apply congrArg ENNReal.ofReal
  field_simp [hx.ne', hceilx.ne']

lemma weightedRate_le_weightedRateNat (A : Set ℕ) :
    weightedRate A ≤ weightedRateNat A := by
  let q : ℝ → ENNReal := ceilLogLogFactor
  let u : ℝ → ENNReal := fun x ↦ weightedTermNat A ⌈x⌉₊
  have hq : Tendsto q atTop (nhds 1) := tendsto_ceilLogLogFactor
  have hq_limsup : Filter.limsup q atTop = 1 := hq.limsup_eq
  have hu : Filter.limsup u atTop ≤ weightedRateNat A := by
    have h := (tendsto_nat_ceil_atTop :
      Tendsto (fun x : ℝ ↦ ⌈x⌉₊) atTop atTop).limsup_comp_le_limsup
        (u := weightedTermNat A)
    simpa [u, weightedRateNat, Function.comp_def] using h
  have hprod : Filter.limsup (q * u) atTop ≤
      Filter.limsup q atTop * Filter.limsup u atTop := by
    apply ENNReal.limsup_mul_le'
    · left
      simp [hq_limsup]
    · left
      simp [hq_limsup]
  unfold weightedRate
  calc
    Filter.limsup (weightedTerm A) atTop = Filter.limsup (q * u) atTop := by
      apply Filter.limsup_congr
      filter_upwards [weightedTerm_eq_factor_mul_eventually A] with x hx
      simpa [q, u, Pi.mul_apply] using hx
    _ ≤ Filter.limsup q atTop * Filter.limsup u atTop := hprod
    _ = Filter.limsup u atTop := by rw [hq_limsup, one_mul]
    _ ≤ weightedRateNat A := hu

/-- Real and natural half-open cutoffs give the same weighted limsup. -/
theorem weightedRate_eq_weightedRateNat (A : Set ℕ) :
    weightedRate A = weightedRateNat A :=
  le_antisymm (weightedRate_le_weightedRateNat A) (weightedRateNat_le_weightedRate A)

private lemma chainTerm_eq_factor_mul_eventually (c : ℕ → ℕ) :
    ∀ᶠ x : ℝ in atTop,
      chainTerm c x = ceilLogLogFactor x * chainTermNat c ⌈x⌉₊ := by
  have hloglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hceilTop : Tendsto (fun x : ℝ ↦ (⌈x⌉₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_ceil_atTop
  have hloglogceil : Tendsto (fun x : ℝ ↦ Real.log (Real.log (⌈x⌉₊ : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hceilTop)
  filter_upwards [hloglog.eventually (eventually_gt_atTop 0),
    hloglogceil.eventually (eventually_gt_atTop 0)] with x hx hceilx
  have hcount : chainCount c x = chainCountNat c ⌈x⌉₊ := by
    simp [chainCount, chainCountNat, positiveBelow, positiveBelowNat]
  rw [chainTerm, chainTermNat, hcount, ceilLogLogFactor]
  rw [← ENNReal.ofReal_mul (div_nonneg hceilx.le hx.le)]
  apply congrArg ENNReal.ofReal
  field_simp [hx.ne', hceilx.ne']

lemma chainRate_le_chainRateNat (c : ℕ → ℕ) : chainRate c ≤ chainRateNat c := by
  let q : ℝ → ENNReal := ceilLogLogFactor
  let u : ℝ → ENNReal := fun x ↦ chainTermNat c ⌈x⌉₊
  have hq : Tendsto q atTop (nhds 1) := tendsto_ceilLogLogFactor
  have hq_limsup : Filter.limsup q atTop = 1 := hq.limsup_eq
  have hu : Filter.limsup u atTop ≤ chainRateNat c := by
    have h := (tendsto_nat_ceil_atTop :
      Tendsto (fun x : ℝ ↦ ⌈x⌉₊) atTop atTop).limsup_comp_le_limsup
        (u := chainTermNat c)
    simpa [u, chainRateNat, Function.comp_def] using h
  have hprod : Filter.limsup (q * u) atTop ≤
      Filter.limsup q atTop * Filter.limsup u atTop := by
    apply ENNReal.limsup_mul_le'
    · left
      simp [hq_limsup]
    · left
      simp [hq_limsup]
  unfold chainRate
  calc
    Filter.limsup (chainTerm c) atTop = Filter.limsup (q * u) atTop := by
      apply Filter.limsup_congr
      filter_upwards [chainTerm_eq_factor_mul_eventually c] with x hx
      simpa [q, u, Pi.mul_apply] using hx
    _ ≤ Filter.limsup q atTop * Filter.limsup u atTop := hprod
    _ = Filter.limsup u atTop := by rw [hq_limsup, one_mul]
    _ ≤ chainRateNat c := hu

lemma chainRateNat_le_chainRate (c : ℕ → ℕ) : chainRateNat c ≤ chainRate c := by
  unfold chainRateNat chainRate
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).limsup_comp_le_limsup
      (u := chainTerm c)
  have hterm : (fun N : ℕ ↦ chainTerm c (N : ℝ)) = chainTermNat c := by
    funext N
    simp [chainTerm, chainTermNat, chainCount, chainCountNat, positiveBelow, positiveBelowNat]
  rw [← hterm]
  simpa [Function.comp_def] using h

/-- Real and natural half-open cutoffs give the same chain-count limsup. -/
theorem chainRate_eq_chainRateNat (c : ℕ → ℕ) : chainRate c = chainRateNat c :=
  le_antisymm (chainRate_le_chainRateNat c) (chainRateNat_le_chainRate c)

end CofinalBridge

section FiniteAbel

private noncomputable def harmonicCoeff (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then (n : ℝ)⁻¹ else 0

private lemma harmonicCoeff_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ harmonicCoeff A n := by
  simp only [harmonicCoeff]
  split_ifs <;> positivity

private lemma sum_harmonicCoeff_Icc (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Icc 0 N, harmonicCoeff A n = harmonicMassNat A (N + 1) := by
  classical
  rw [harmonicMassNat, positiveBelowNat]
  rw [sum_filter]
  change (∑ n ∈ Icc 0 N, if n ∈ A then (n : ℝ)⁻¹ else 0) =
    ∑ n ∈ Ico 1 (N + 1), if n ∈ A then (n : ℝ)⁻¹ else 0
  symm
  refine sum_subset ?_ ?_
  · intro n hn
    simp only [mem_Ico] at hn
    simp only [mem_Icc]
    omega
  · intro n hn hnot
    simp only [mem_Icc] at hn
    simp only [mem_Ico, not_and_or, not_lt] at hnot
    have hn0 : n = 0 := by omega
    subst n
    simp

private noncomputable def partialHarmonicMass (A : Set ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊t⌋₊, harmonicCoeff A n

private lemma finite_abel_inv_log (A : Set ℕ) {m N : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) :
    ∑ n ∈ Ioc m N, (Real.log (n : ℝ))⁻¹ * harmonicCoeff A n =
      (Real.log (N : ℝ))⁻¹ * partialHarmonicMass A N -
        (Real.log (m : ℝ))⁻¹ * partialHarmonicMass A m +
          ∫ t in Set.Ioc (m : ℝ) N,
            partialHarmonicMass A t / (t * Real.log t ^ 2) := by
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    (c := harmonicCoeff A) (f := fun t : ℝ ↦ (Real.log t)⁻¹) hmN
    (fun t ht ↦ by
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have ht2 : (2 : ℝ) ≤ t := hmR.trans ht.1
      exact Real.differentiableAt_inv_log (by linarith) (by linarith) (by linarith))
    (by
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
        (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have ht2 : (2 : ℝ) ≤ t := hmR.trans ht.1
      have ht0 : t ≠ 0 := by linarith
      have hlog : Real.log t ^ 2 ≠ 0 := by
        refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
        · linarith
        · linarith
      exact ContinuousAt.continuousWithinAt <| by fun_prop)
  have hIntegral :
      ∫ t in Set.Ioc (m : ℝ) N,
          deriv (fun t : ℝ ↦ (Real.log t)⁻¹) t * partialHarmonicMass A t =
        - ∫ t in Set.Ioc (m : ℝ) N,
          partialHarmonicMass A t / (t * Real.log t ^ 2) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [Real.deriv_inv_log_apply]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have hIntegral' :
      ∫ t in Set.Ioc (m : ℝ) N,
          deriv (fun t : ℝ ↦ (Real.log t)⁻¹) t *
            ∑ k ∈ Icc 0 ⌊t⌋₊, harmonicCoeff A k =
        - ∫ t in Set.Ioc (m : ℝ) N,
          (∑ k ∈ Icc 0 ⌊t⌋₊, harmonicCoeff A k) /
            (t * Real.log t ^ 2) := by
    simpa only [partialHarmonicMass] using hIntegral
  rw [hAbel]
  simp only [partialHarmonicMass, Nat.floor_natCast]
  rw [hIntegral']
  ring

private lemma integral_inv_mul_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (t * Real.log t) = Real.log (Real.log b) - Real.log (Real.log a) := by
  apply intervalIntegral.integral_deriv_eq_sub'
      (fun t : ℝ ↦ Real.log (Real.log t))
  · funext t
    rw [Real.deriv_log_log_apply]
    ring
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact Real.differentiableAt_log_log
      (by linarith [ht.1]) (by linarith [ht.1]) (by linarith [ht.1])
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ha.trans_le ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (ha.trans_le ht.1))
    exact ContinuousAt.continuousWithinAt <|
      continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog)

/-- Finite Abel summation in the precise form needed for the density passage. -/
private lemma weightedMassNat_lower_of_harmonic (A : Set ℕ) {M N : ℕ} {d : ℝ}
    (hM : 2 ≤ M) (hMN : M ≤ N) (hd : 0 ≤ d)
    (hH : ∀ K, M ≤ K → d * Real.log K ≤ harmonicMassNat A K) :
    d * (Real.log (Real.log N) - Real.log (Real.log M)) -
        harmonicMassNat A (M + 1) / Real.log M ≤ weightedMassNat A (N + 1) := by
  classical
  let c : ℕ → ℝ := harmonicCoeff A
  have hMreal : (1 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hM)
  have hNreal : (1 : ℝ) < N := hMreal.trans_le (by exact_mod_cast hMN)
  have habel := finite_abel_inv_log A hM hMN
  have hsum (K : ℕ) : ∑ k ∈ Icc 0 K, c k = harmonicMassNat A (K + 1) := by
    exact sum_harmonicCoeff_Icc A K
  have hsum_nonneg (K : ℕ) : 0 ≤ ∑ k ∈ Icc 0 K, c k :=
    sum_nonneg fun k hk ↦ harmonicCoeff_nonneg A k
  have hweighted :
      ∑ k ∈ Ioc M N, (Real.log (k : ℝ))⁻¹ * c k ≤ weightedMassNat A (N + 1) := by
    rw [weightedMassNat, positiveBelowNat]
    calc
      ∑ k ∈ Ioc M N, (Real.log (k : ℝ))⁻¹ * c k =
          ∑ k ∈ Ioc M N,
            if k ∈ A then doublyHarmonicWeight k else 0 := by
              apply sum_congr rfl
              intro k hk
              have hk2 : 2 ≤ k := hM.trans (mem_Ioc.mp hk).1.le
              simp only [c, harmonicCoeff, doublyHarmonicWeight, if_pos hk2]
              by_cases hkA : k ∈ A
              · simp only [if_pos hkA]
                rw [mul_inv]
                ring
              · simp only [if_neg hkA, mul_zero]
      _ ≤ ∑ k ∈ Ico 1 (N + 1),
            if k ∈ A then doublyHarmonicWeight k else 0 := by
              refine sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro k hk
                rw [mem_Ioc] at hk
                rw [mem_Ico]
                omega
              · intro k hk hkn
                split_ifs
                · simp only [doublyHarmonicWeight]
                  split_ifs <;> positivity
                · exact le_rfl
      _ = ∑ k ∈ (Ico 1 (N + 1)).filter (fun k ↦ k ∈ A),
            doublyHarmonicWeight k := by
              rw [sum_filter]
      _ = _ := rfl
  have hkernel_integrable : IntegrableOn (fun t : ℝ ↦ 1 / (t * Real.log t ^ 2))
      (Set.Icc (M : ℝ) N) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht1 : 1 < t := hMreal.trans_le ht.1
    have ht0 : t ≠ 0 := by positivity
    have hlog : Real.log t ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt (Real.log_pos ht1))
    exact continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)) (mul_ne_zero ht0 hlog)
  have hpositive_integrable : IntervalIntegrable
      (fun t : ℝ ↦ partialHarmonicMass A t / (t * Real.log t ^ 2)) volume M N := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast hMN)]
    simpa only [partialHarmonicMass, c, div_eq_mul_inv, one_mul, mul_comm] using
      integrableOn_mul_sum_Icc (m := 0) c (by positivity) hkernel_integrable
  have hmodel_integrable : IntervalIntegrable (fun t : ℝ ↦ d * (1 / (t * Real.log t)))
      volume M N := by
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    rw [Set.uIcc_of_le (by exact_mod_cast hMN)] at ht
    have ht0 : t ≠ 0 := by linarith [hMreal.trans_le ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (hMreal.trans_le ht.1))
    exact ContinuousAt.continuousWithinAt <| continuousAt_const.mul <|
      continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog)
  have hintegral : d * (Real.log (Real.log N) - Real.log (Real.log M)) ≤
      ∫ t in M..N, partialHarmonicMass A t / (t * Real.log t ^ 2) := by
    rw [← integral_inv_mul_log hMreal (by exact_mod_cast hMN),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by exact_mod_cast hMN)
      hmodel_integrable hpositive_integrable ?_
    intro t ht
    have ht1 : 1 < t := hMreal.trans_le ht.1
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hfloor : M ≤ ⌊t⌋₊ := by
      exact Nat.le_floor ht.1
    have hK : M ≤ ⌊t⌋₊ + 1 := hfloor.trans (Nat.le_succ _)
    have htK : t ≤ (⌊t⌋₊ + 1 : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one t).le
    have hlog_le : Real.log t ≤ Real.log (⌊t⌋₊ + 1 : ℕ) :=
      Real.log_le_log ht0 htK
    have hmass : d * Real.log t ≤ ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
      rw [hsum]
      exact (mul_le_mul_of_nonneg_left hlog_le hd).trans (hH _ hK)
    have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (sq_pos_of_pos hlogt)
    have heq : d * (1 / (t * Real.log t)) =
        d * Real.log t / (t * Real.log t ^ 2) := by
      field_simp
    rw [heq, partialHarmonicMass]
    exact div_le_div_of_nonneg_right hmass hden.le
  have hpartial_nat (K : ℕ) : partialHarmonicMass A K = harmonicMassNat A (K + 1) := by
    simp only [partialHarmonicMass, Nat.floor_natCast, sum_harmonicCoeff_Icc]
  rw [hpartial_nat N, hpartial_nat M,
    ← intervalIntegral.integral_of_le (by exact_mod_cast hMN)] at habel
  have hboundary : 0 ≤ (Real.log (N : ℝ))⁻¹ * harmonicMassNat A (N + 1) :=
    mul_nonneg (inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by omega : N ≠ 0))))) (by simpa [hsum] using hsum_nonneg N)
  calc
    d * (Real.log (Real.log N) - Real.log (Real.log M)) -
          harmonicMassNat A (M + 1) / Real.log M
        ≤ (Real.log (N : ℝ))⁻¹ * harmonicMassNat A (N + 1) -
            (Real.log (M : ℝ))⁻¹ * harmonicMassNat A (M + 1) +
              ∫ t in M..N, partialHarmonicMass A t / (t * Real.log t ^ 2) := by
          rw [div_eq_mul_inv]
          nlinarith [hintegral, hboundary]
    _ = ∑ k ∈ Ioc M N, (Real.log (k : ℝ))⁻¹ * c k := habel.symm
    _ ≤ _ := hweighted

end FiniteAbel

section DensityTransfer

private lemma log_log_succ_le_add_one {N : ℕ} (hN : 3 ≤ N) :
    Real.log (Real.log (N + 1 : ℕ)) ≤ Real.log (Real.log N) + 1 := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hsuccpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hNsq : N + 1 ≤ N ^ 2 := by nlinarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogsucc : 0 < Real.log (N + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N + 1))
  have hlog : Real.log (N + 1 : ℕ) ≤ 2 * Real.log N := by
    calc
      Real.log (N + 1 : ℕ) ≤ Real.log ((N : ℝ) ^ 2) := by
        apply Real.log_le_log hsuccpos
        exact_mod_cast hNsq
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  calc
    Real.log (Real.log (N + 1 : ℕ)) ≤ Real.log (2 * Real.log N) :=
      Real.log_le_log hlogsucc hlog
    _ = Real.log 2 + Real.log (Real.log N) := by rw [Real.log_mul] <;> positivity
    _ ≤ Real.log (Real.log N) + 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

private lemma lowerLogDensityNat_le_weightedRateNat (A : Set ℕ) :
    lowerLogDensityNat A ≤ weightedRateNat A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  have hrs : (s : ℝ) < (r : ℝ) := by exact_mod_cast hs
  have hrlower : (r : ENNReal) <
      Filter.liminf (lowerLogDensityTermNat A) atTop := by
    simpa [lowerLogDensityNat] using hr
  have heventual := eventually_lt_of_lt_liminf hrlower
  rcases eventually_atTop.mp heventual with ⟨M₀, hM₀⟩
  let M : ℕ := max M₀ 3
  have hM3 : 3 ≤ M := le_max_right _ _
  have hM2 : 2 ≤ M := (by omega : 2 ≤ 3).trans hM3
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hH : ∀ K, M ≤ K → (r : ℝ) * Real.log K ≤ harmonicMassNat A K := by
    intro K hMK
    have hterm := hM₀ K (hM₀M.trans hMK)
    have hratio : (r : ℝ) < harmonicMassNat A K / Real.log K := by
      simpa [lowerLogDensityTermNat] using hterm
    have hlogK : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) (hM3.trans hMK)))
    exact ((lt_div_iff₀ hlogK).mp hratio).le
  let C : ℝ := (r : ℝ) * Real.log (Real.log M) +
    harmonicMassNat A (M + 1) / Real.log M
  have hgap : 0 < (r : ℝ) - (s : ℝ) := sub_pos.mpr hrs
  have hloglog : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (C + (s : ℝ)) / ((r : ℝ) - (s : ℝ)) < Real.log (Real.log N) :=
    hloglog.eventually_gt_atTop _
  have hden_event : ∀ᶠ N : ℕ in atTop,
      0 < Real.log (Real.log (N + 1 : ℕ)) :=
    (hloglog.comp (tendsto_add_atTop_nat 1)).eventually (eventually_gt_atTop 0)
  have hterms : ∀ᶠ N : ℕ in atTop,
      (s : ENNReal) ≤ weightedTermNat A (N + 1) := by
    filter_upwards [hlarge, hden_event, eventually_ge_atTop M] with N hlargeN hden hMN
    have hN3 : 3 ≤ N := hM3.trans hMN
    have hfinite := weightedMassNat_lower_of_harmonic A hM2 hMN
      (show 0 ≤ (r : ℝ) by positivity) hH
    have hshift := log_log_succ_le_add_one hN3
    have hthreshold : C + (s : ℝ) <
        ((r : ℝ) - (s : ℝ)) * Real.log (Real.log N) := by
      nlinarith [(div_lt_iff₀ hgap).mp hlargeN]
    have hmass : (s : ℝ) * Real.log (Real.log (N + 1 : ℕ)) ≤
        weightedMassNat A (N + 1) := by
      have hs0 : (0 : ℝ) ≤ s := by positivity
      have hpre : (s : ℝ) * Real.log (Real.log (N + 1 : ℕ)) ≤
          (r : ℝ) * (Real.log (Real.log N) - Real.log (Real.log M)) -
            harmonicMassNat A (M + 1) / Real.log M := by
        dsimp [C] at hthreshold
        nlinarith [mul_le_mul_of_nonneg_left hshift hs0]
      exact hpre.trans hfinite
    have hratio : (s : ℝ) ≤
        weightedMassNat A (N + 1) / Real.log (Real.log (N + 1 : ℕ)) :=
      (le_div_iff₀ hden).2 hmass
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hratio
  have hs_shift : (s : ENNReal) ≤
      Filter.limsup (fun N : ℕ ↦ weightedTermNat A (N + 1)) atTop :=
    Filter.le_limsup_of_frequently_le' hterms.frequently
  have hsubsequence := (tendsto_add_atTop_nat 1).limsup_comp_le_limsup
    (u := weightedTermNat A)
  have hsubsequence' :
      Filter.limsup (fun N : ℕ ↦ weightedTermNat A (N + 1)) atTop ≤
        weightedRateNat A := hsubsequence
  exact hs_shift.trans hsubsequence'

/-- Abel summation transfers lower logarithmic density to doubly-harmonic
upper density, with no loss in the constant. -/
theorem lowerLogDensity_le_weightedRate (A : Set ℕ) :
    lowerLogDensity A ≤ weightedRate A :=
  (lowerLogDensity_le_lowerLogDensityNat A).trans <|
    (lowerLogDensityNat_le_weightedRateNat A).trans (weightedRateNat_le_weightedRate A)

/-- In particular, positive lower logarithmic density implies positive
doubly-harmonic upper density. -/
theorem weightedRate_pos_of_lowerLogDensity_pos {A : Set ℕ}
    (hA : 0 < lowerLogDensity A) : 0 < weightedRate A :=
  hA.trans_le (lowerLogDensity_le_weightedRate A)

end DensityTransfer

end Erdos1217
