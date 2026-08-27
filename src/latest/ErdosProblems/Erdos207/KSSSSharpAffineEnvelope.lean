/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSharpPowerBudgets
import ErdosProblems.Erdos207.SharpAffineClock

/-! # The explicit positive affine envelope for the initial density horizon -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem ksssEdgeDensity_nnreal_ratio
    (E : ℝ) (i : ℕ) (hE : 0 < E) (hclock : 3 * (i : ℝ) < E) :
    Real.toNNReal (ksssEdgeDensity E i) =
      (Real.toNNReal E - 3 * (i : ℝ≥0)) / Real.toNNReal E := by
  have hclockNN : 3 * (i : ℝ≥0) ≤ Real.toNNReal E := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, Real.coe_toNNReal _ hE.le] using hclock.le
  apply NNReal.eq
  rw [Real.coe_toNNReal (ksssEdgeDensity E i) (ksssEdgeDensity_pos hE hclock).le]
  simp only [NNReal.coe_div, NNReal.coe_sub hclockNN, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
    Real.coe_toNNReal _ hE.le, ksssEdgeDensity]

theorem ksssEdgeDensity_nnreal_clock
    (E : ℝ) (i : ℕ) (hE : 0 < E) (hclock : 3 * (i : ℝ) < E) :
    Real.toNNReal E * Real.toNNReal (ksssEdgeDensity E i) = Real.toNNReal E - 3 * (i : ℝ≥0) := by
  rw [ksssEdgeDensity_nnreal_ratio E i hE hclock]
  have hEN : Real.toNNReal E ≠ 0 := (Real.toNNReal_pos.mpr hE).ne'
  field_simp

def ksssSharpClockEnvelope (E : ℝ) (t b i : ℕ) : ℝ≥0 :=
  affineSurvivalEnvelope (Real.toNNReal E) (3 * (1 - 16 / (t : ℝ≥0) ^ (b + 1))) i

structure KSSSSharpClockEnvelopeBounds (E : ℝ) (t b n : ℕ) : Prop where
  initial : ksssSharpClockEnvelope E t b 0 = Real.toNNReal E
  positive : ∀ i, i ≤ n → 0 < ksssSharpClockEnvelope E t b i
  decreasing : ∀ i, i < n → ksssSharpClockEnvelope E t b (i + 1) ≤ ksssSharpClockEnvelope E t b i
  lower : ∀ i, i ≤ n → Real.toNNReal E - 3 * (i : ℝ≥0) ≤ ksssSharpClockEnvelope E t b i
  upper : ∀ i, i ≤ n → ksssSharpClockEnvelope E t b i ≤ 2 * (Real.toNNReal E - 3 * (i : ℝ≥0))
  decrement : ∀ i, i < n → ksssSharpClockEnvelope E t b i - ksssSharpClockEnvelope E t b (i + 1) =
    3 * (1 - 16 / (t : ℝ≥0) ^ (b + 1))
  final_ratio : ksssSharpClockEnvelope E t b n / ksssSharpClockEnvelope E t b 0 ≤
    2 * Real.toNNReal (ksssEdgeDensity E n)

theorem ksssSharpClockEnvelope_bounds
    (E : ℝ) (t b n : ℕ) (hE : 0 < E) (ht : 32 ≤ t)
    (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E n) :
    KSSSSharpClockEnvelopeBounds E t b n := by
  let eps : ℝ≥0 := 16 / (t : ℝ≥0) ^ (b + 1)
  have htR : (32 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hb := sharp_power_rounding_budgets t ((t : ℝ) ^ (b + 3)) ((t : ℝ) ^ 2) b htR le_rfl le_rfl
  have heps : eps ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    simp only [eps, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_one]
    linarith only [hb.2.1]
  have hp : 0 < ksssEdgeDensity E n := (by positivity : (0 : ℝ) < 1 / (t : ℝ) ^ b).trans_le hfloor
  have hclock : 3 * (n : ℝ) < E := by
    have h := (lt_div_iff₀ hE).mp hp
    linarith only [h]
  have hclockNN : 3 * (n : ℝ≥0) < Real.toNNReal E := by
    rw [← NNReal.coe_lt_coe]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, Real.coe_toNNReal _ hE.le] using hclock
  have hepsClock : eps * Real.toNNReal E ≤ Real.toNNReal E - 3 * (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    simp only [eps, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_ofNat, NNReal.coe_sub hclockNN.le, Real.coe_toNNReal _ hE.le]
    exact (le_div_iff₀ hE).mp (hb.2.2.2.2.1.trans hfloor)
  have hslope : 3 * (1 - eps) ≤ (3 : ℝ≥0) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (tsub_le_self : 1 - eps ≤ (1 : ℝ≥0)) (by norm_num)
  have hpositive : (n : ℝ≥0) * (3 * (1 - eps)) < Real.toNNReal E := by
    calc
      _ ≤ (n : ℝ≥0) * 3 := mul_le_mul_of_nonneg_left hslope zero_le
      _ = 3 * (n : ℝ≥0) := mul_comm _ _
      _ < _ := hclockNN
  have hcompare := fun i hi ↦ affineSurvivalEnvelope_clock_comparison (Real.toNNReal E) eps n i
    hclockNN heps hepsClock hi
  have hinitial : ksssSharpClockEnvelope E t b 0 = Real.toNNReal E := by
    simp only [ksssSharpClockEnvelope, affineSurvivalEnvelope, Nat.cast_zero, zero_mul, tsub_zero]
  refine ⟨hinitial, fun i hi ↦ affineSurvivalEnvelope_pos hpositive hi,
    fun i _ ↦ affineSurvivalEnvelope_antitone _ _ (Nat.le_succ i),
    fun i hi ↦ (hcompare i hi).1, fun i hi ↦ (hcompare i hi).2,
    fun i hi ↦ affineSurvivalEnvelope_sub_succ hpositive.le hi, ?_⟩
  rw [hinitial, ksssEdgeDensity_nnreal_ratio E n hE hclock]
  calc
    _ ≤ (2 * (Real.toNNReal E - 3 * (n : ℝ≥0))) / Real.toNNReal E :=
      div_le_div_of_nonneg_right (hcompare n le_rfl).2 zero_le
    _ = _ := by ring

end

end Erdos207
