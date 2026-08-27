/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedMomentFailureBudget

/-! # Finite power-ratio budgets for reserve regularization -/

namespace Erdos207

open scoped NNReal

theorem inversePower_density_lower
    (t p n : ℝ≥0) (b k : ℕ) (hp : 1 / t ^ b ≤ p) :
    n / t ^ (b * k) ≤ p ^ k * n := by
  calc
    _ = (1 / t ^ b) ^ k * n := by rw [div_pow, one_pow, ← pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le hp k) zero_le

theorem powerRatio_ge_parameter
    (t n : ℝ≥0) (d L : ℕ) (ht : 1 ≤ t) (hL : d + 1 ≤ L) (hn : t ^ L ≤ n) :
    t ≤ n / t ^ d := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  apply (le_div_iff₀ (pow_pos ht0 d)).mpr
  calc
    _ = t ^ (d + 1) := by rw [pow_succ]; ring
    _ ≤ t ^ L := pow_le_pow_right₀ ht hL
    _ ≤ n := hn

theorem inversePower_mul_density_lower
    (t p n : ℝ≥0) (b c k : ℕ) (hp : 1 / t ^ b ≤ p) :
    n / t ^ (b * k + c) ≤ (1 / t ^ c) * (p ^ k * n) := by
  calc
    _ = (1 / t ^ c) * (n / t ^ (b * k)) := by rw [pow_add]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inversePower_density_lower t p n b k hp) zero_le

theorem inversePower_parameter_le_one_div
    (t : ℝ≥0) (c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) : 1 / t ^ c ≤ 1 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  apply div_le_div_of_nonneg_left zero_le ht0
  simpa only [pow_one] using pow_le_pow_right₀ ht hc

theorem inversePower_inner_margin
    (t p tau tau0 n u : ℝ≥0) (b a : ℕ)
    (ht : 1 ≤ t) (ha : 4 * b + 1 ≤ a)
    (hp : 1 / t ^ b ≤ p) (htau : tau0 ≤ tau)
    (hcoefficient : 1536 ≤ tau0 ^ 6 * t) (hinner : u ≤ n / t ^ a) :
    u ≤ p ^ 4 * tau ^ 6 * n / 1536 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hratio : 1 / t ≤ tau0 ^ 6 / 1536 := by
    apply (div_le_div_iff₀ ht0 (by norm_num : (0 : ℝ≥0) < 1536)).mpr
    simpa only [one_mul] using hcoefficient
  have hdensity : n / t ^ (4 * b) ≤ p ^ 4 * n := by
    simpa only [Nat.mul_comm b 4] using inversePower_density_lower t p n b 4 hp
  have htpow : tau0 ^ 6 ≤ tau ^ 6 := pow_le_pow_left₀ zero_le htau 6
  calc
    u ≤ n / t ^ a := hinner
    _ ≤ n / t ^ (4 * b + 1) :=
      div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht ha)
    _ = (n / t ^ (4 * b)) * (1 / t) := by rw [pow_succ]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (p ^ 4 * n) * (tau0 ^ 6 / 1536) := mul_le_mul' hdensity hratio
    _ ≤ (p ^ 4 * n) * (tau ^ 6 / 1536) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htpow zero_le) zero_le
    _ = _ := by ring

theorem inversePower_fourth_density_scale
    (t p tau tau0 n : ℝ≥0) (b L : ℕ)
    (ht : 1 ≤ t) (hL : 4 * b + 1 ≤ L) (hn : t ^ L ≤ n)
    (hp : 1 / t ^ b ≤ p) (htau : tau0 ≤ tau) :
    tau0 ^ 6 * t ≤ p ^ 4 * tau ^ 6 * n := by
  have hbase : t ≤ p ^ 4 * n :=
    (powerRatio_ge_parameter t n (b * 4) L ht (by omega) hn).trans
      (inversePower_density_lower t p n b 4 hp)
  calc
    _ ≤ tau0 ^ 6 * (p ^ 4 * n) := mul_le_mul_of_nonneg_left hbase zero_le
    _ ≤ tau ^ 6 * (p ^ 4 * n) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le htau 6) zero_le
    _ = _ := by ring

theorem inversePower_reserve_exponent_scale
    (t p tau tau0 n : ℝ≥0) (b c L : ℕ)
    (ht : 1 ≤ t) (hL : 4 * b + c + 1 ≤ L) (hn : t ^ L ≤ n)
    (hp : 1 / t ^ b ≤ p) (htau : tau0 ≤ tau) :
    tau0 ^ 6 * t ≤ (1 / t ^ c) * (p ^ 4 * tau ^ 6 * n) := by
  have hbase : t ≤ (1 / t ^ c) * (p ^ 4 * n) :=
    (powerRatio_ge_parameter t n (b * 4 + c) L ht (by omega) hn).trans
      (inversePower_mul_density_lower t p n b c 4 hp)
  calc
    _ ≤ tau0 ^ 6 * ((1 / t ^ c) * (p ^ 4 * n)) := mul_le_mul_of_nonneg_left hbase zero_le
    _ ≤ tau ^ 6 * ((1 / t ^ c) * (p ^ 4 * n)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le htau 6) zero_le
    _ = _ := by ring

theorem inversePower_triangle_sampling_exponent_scale
    (t p tau tau0 n : ℝ≥0) (b e L : ℕ)
    (ht : 1 ≤ t) (hL : 2 * b + 2 * e + 1 ≤ L) (hn : t ^ L ≤ n)
    (hp : 1 / t ^ b ≤ p) (htau : tau0 ≤ tau) :
    tau0 * t ≤ (1 / t ^ e) ^ 2 * (p ^ 2 * tau * n) := by
  have hbase : t ≤ (1 / t ^ (e * 2)) * (p ^ 2 * n) :=
    (powerRatio_ge_parameter t n (b * 2 + e * 2) L ht (by omega) hn).trans
      (inversePower_mul_density_lower t p n b (e * 2) 2 hp)
  calc
    _ ≤ tau0 * ((1 / t ^ (e * 2)) * (p ^ 2 * n)) := mul_le_mul_of_nonneg_left hbase zero_le
    _ ≤ tau * ((1 / t ^ (e * 2)) * (p ^ 2 * n)) := mul_le_mul_of_nonneg_right htau zero_le
    _ = _ := by rw [div_pow, one_pow, ← pow_mul]; ring

end Erdos207
