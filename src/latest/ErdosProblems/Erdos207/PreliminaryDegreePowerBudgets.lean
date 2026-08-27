/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePreliminaryJointDegree
import ErdosProblems.Erdos207.InternalCoverRoundedBudgets

/-! # Explicit power budgets for preliminary degrees and link perturbation -/

namespace Erdos207

open scoped NNReal

theorem preliminary_rounded_degree_mean_power
    (t n u p r eta eta0 H K rate : ℝ≥0) (reserveExp b v c decay : ℕ)
    (ht : 1 ≤ t) (hu : 0 < u) (heta0 : 0 < eta0)
    (hp : 1 / t ^ b ≤ p) (hr : 1 / t ^ reserveExp ≤ r) (heta : eta0 ≤ eta)
    (hsize : n ≤ K * t ^ v * u) (hrate : rate ≤ H / t ^ c)
    (hgap : 2 * reserveExp + 2 * b + v + decay ≤ c) :
    2 * n * rate / (⌊r ^ 2 * p ^ 2 * eta * u / 256⌋₊ + 1 : ℝ≥0) ≤ (512 * H * K / eta0) / t ^ decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < p := (by positivity : 0 < 1 / t ^ b).trans_le hp
  have hr0 : 0 < r := (by positivity : 0 < 1 / t ^ reserveExp).trans_le hr
  have hetaPos : 0 < eta := heta0.trans_le heta
  have hfloor := (Nat.lt_floor_add_one (r ^ 2 * p ^ 2 * eta * u / 256)).le
  have hratio : t ^ (2 * reserveExp + 2 * b + v) / t ^ c ≤ 1 / t ^ decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ 2 * n * rate / (r ^ 2 * p ^ 2 * eta * u / 256) := div_le_div_of_nonneg_left zero_le (by positivity) hfloor
    _ ≤ 2 * (K * t ^ v * u) * (H / t ^ c) / ((1 / t ^ reserveExp) ^ 2 * (1 / t ^ b) ^ 2 * eta0 * u / 256) := by
      gcongr
    _ = (512 * H * K / eta0) * (t ^ (2 * reserveExp + 2 * b + v) / t ^ c) := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
      ring
    _ ≤ (512 * H * K / eta0) * (1 / t ^ decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem sourcePreliminaryDegreeFailure_power_le
    (N n d s R a B decay : ℕ) (t rate C error A : ℝ≥0)
    (ht : 1 ≤ t) (hN : (N : ℝ≥0) ≤ t ^ R) (hn : (n : ℝ≥0) ≤ t ^ R)
    (hmain : 2 * (n : ℝ≥0) * rate / (d + 1) ≤ A / t ^ a) (herror : error ≤ 1 / t ^ B)
    (hmainGap : R + decay ≤ a * s) (herrorGap : R * s + R + decay ≤ B) :
    sourcePreliminaryDegreeFailure N n d s rate C error ≤ (A ^ s + (2 * C) ^ s) / t ^ decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hmainTerm : (2 * (n : ℝ≥0) * rate / (d + 1)) ^ s ≤ A ^ s / t ^ (R + decay) := by
    calc
      _ ≤ (A / t ^ a) ^ s := pow_le_pow_left' hmain s
      _ = A ^ s / t ^ (a * s) := by rw [div_pow, pow_mul]
      _ ≤ _ := div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hmainGap)
  have herrorRatio : 2 * (n : ℝ≥0) * C / (d + 1) ≤ (2 * C) * t ^ R := by
    calc
      _ ≤ 2 * (n : ℝ≥0) * C / 1 :=
        div_le_div_of_nonneg_left zero_le zero_lt_one (le_add_of_nonneg_left zero_le)
      _ ≤ 2 * t ^ R * C := by rw [div_one]; gcongr
      _ = _ := by ring
  have herrorTerm := finite_moment_error_power_decay t error (2 * (n : ℝ≥0) * C / (d + 1))
    (2 * C) B R s (R + decay) ht herror herrorRatio (by omega)
  have hsingle : (2 * (n : ℝ≥0) * rate / (d + 1)) ^ s + (2 * (n : ℝ≥0) * C / (d + 1)) ^ s * error ≤
      (A ^ s + (2 * C) ^ s) / t ^ (R + decay) := by
    rw [add_div]
    exact add_le_add hmainTerm (by simpa only [mul_comm] using herrorTerm)
  unfold sourcePreliminaryDegreeFailure
  have hb := finite_polynomial_union_power_decay t N _ 1 (A ^ s + (2 * C) ^ s) R (R + decay) decay ht
    (by simpa only [one_mul] using hN) hsingle le_rfl
  simpa only [one_mul] using hb

theorem rounded_internal_degree_recenter
    (r p eta u epsilon : ℝ≥0) (hr : r ≤ 128 * epsilon * p * eta) :
    (2 * ⌊r ^ 2 * p ^ 2 * eta * u / 256⌋₊ : ℝ≥0) ≤ epsilon * r * p ^ 3 * eta ^ 2 * u := by
  have hf := Nat.floor_le (show (0 : ℝ≥0) ≤ r ^ 2 * p ^ 2 * eta * u / 256 from zero_le)
  have hbound : r ^ 2 * p ^ 2 * eta * u / 128 ≤ epsilon * r * p ^ 3 * eta ^ 2 * u := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 128)).mpr
    have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ r * p ^ 2 * eta * u from zero_le)
    convert hh using 1 <;> ring
  calc
    _ ≤ 2 * (r ^ 2 * p ^ 2 * eta * u / 256) := mul_le_mul_of_nonneg_left hf zero_le
    _ = r ^ 2 * p ^ 2 * eta * u / 128 := by ring
    _ ≤ _ := hbound

end Erdos207
