/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveRegularizationPowerScalars

/-! # Explicit power gaps supply the finite-order regularization inequalities -/

namespace Erdos207

open scoped NNReal

theorem powerRatio_ge_power
    (t n : ℝ≥0) (d r L : ℕ) (ht : 1 ≤ t) (hgap : d + r ≤ L) (hn : t ^ L ≤ n) :
    t ^ r ≤ n / t ^ d := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  apply (le_div_iff₀ (pow_pos ht0 d)).mpr
  calc
    t ^ r * t ^ d = t ^ (d + r) := by rw [pow_add]; ring
    _ ≤ t ^ L := pow_le_pow_right₀ ht hgap
    _ ≤ n := hn

theorem inversePower_density_ge_power
    (t sigma n : ℝ≥0) (w k r L : ℕ) (ht : 1 ≤ t)
    (hsigma : 1 / t ^ w ≤ sigma) (hgap : w * k + r ≤ L) (hn : t ^ L ≤ n) :
    t ^ r ≤ sigma ^ k * n :=
  (powerRatio_ge_power t n (w * k) r L ht hgap hn).trans
    (inversePower_density_lower t sigma n w k hsigma)

theorem power_ratio_le_inverse
    (t : ℝ≥0) (K v : ℕ) (ht : 1 ≤ t) (hgap : K + 1 ≤ v) :
    t ^ K / t ^ v ≤ 1 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  calc
    _ ≤ t ^ K / t ^ (K + 1) :=
      div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hgap)
    _ = _ := by rw [pow_succ]; field_simp

theorem regularization_degree_coefficient_power_small
    (t B sigma : ℝ≥0) (K v k : ℕ) (ht : 9 ≤ t) (hgap : K + 1 ≤ v)
    (hk : 1 ≤ k) (hB : B ≤ t ^ K) (hsigma : sigma ≤ 1 / t ^ v) :
    9 * B * sigma ^ k ≤ 1 := by
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 9).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hsigma1 : sigma ≤ 1 := hsigma.trans (div_le_self zero_le (one_le_pow₀ ht1))
  have hpow : sigma ^ k ≤ sigma := by
    simpa only [pow_one] using pow_le_pow_of_le_one (show 0 ≤ sigma from zero_le) hsigma1 hk
  calc
    _ ≤ 9 * t ^ K * (1 / t ^ v) := mul_le_mul (mul_le_mul_of_nonneg_left hB zero_le) (hpow.trans hsigma) zero_le zero_le
    _ = 9 * (t ^ K / t ^ v) := by ring
    _ ≤ 9 * (1 / t) := mul_le_mul_of_nonneg_left (power_ratio_le_inverse t K v ht1 hgap) zero_le
    _ = 9 / t := by ring
    _ ≤ 1 := (div_le_one ht0).mpr ht

theorem power_coefficient_absorption
    (t C B : ℝ≥0) (K D : ℕ) (ht : 1 ≤ t) (hC : C ≤ t) (hB : B ≤ t ^ K)
    (hgap : K + 1 ≤ D) : C * B ≤ t ^ D := by
  calc
    _ ≤ t * t ^ K := mul_le_mul hC hB zero_le zero_le
    _ = t ^ (K + 1) := by rw [pow_succ'];
    _ ≤ t ^ D := pow_le_pow_right₀ ht hgap

theorem power_amplitude_four
    (t : ℝ≥0) (D A : ℕ) (ht : 4 ≤ t) (hgap : D + 1 ≤ A) :
    4 * t ^ D ≤ t ^ A := by
  apply power_coefficient_absorption t 4 (t ^ D) D A
    ((by norm_num : (1 : ℝ≥0) ≤ 4).trans ht) ht le_rfl hgap

theorem regularization_auxiliary_size_from_power_mass
    (t n m sigma C : ℝ≥0) (_ht : 1 ≤ t) (hn : 1 ≤ n) (hC : 0 < C)
    (hCt : C ≤ t) (hdensity : t ^ 2 ≤ sigma * n) (hmass : sigma * n ^ 3 / C ≤ m) :
    t ≤ m := by
  apply le_trans _ hmass
  apply (le_div_iff₀ hC).mpr
  calc
    t * C ≤ t * t := mul_le_mul_of_nonneg_left hCt zero_le
    _ = t ^ 2 := by ring
    _ ≤ sigma * n := hdensity
    _ ≤ sigma * n ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      simpa only [pow_one] using pow_le_pow_right₀ hn (show 1 ≤ 3 by decide)

end Erdos207
