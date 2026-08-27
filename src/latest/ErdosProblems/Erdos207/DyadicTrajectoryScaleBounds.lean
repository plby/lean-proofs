/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RealPowerHierarchyArithmetic

/-! # Density and error comparisons on the integer power hierarchy -/

namespace Erdos207

theorem inverse_density_power_le
    (t p : ℝ) (b B : ℕ) (ht : 0 < t) (hp : 0 < p) (hfloor : 1 / t ^ b ≤ p) :
    1 / p ^ B ≤ t ^ (b * B) := by
  have hbase : 1 ≤ p * t ^ b := (div_le_iff₀ (pow_pos ht b)).mp hfloor
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbase B
  rw [one_pow, mul_pow, ← pow_mul] at hpow
  apply (div_le_iff₀ (pow_pos hp B)).mpr
  simpa only [mul_comm] using hpow

theorem density_error_power_upper
    (N t p : ℝ) (a b B : ℕ) (hN : 0 ≤ N) (ht : 0 < t) (hp : 0 < p)
    (hfloor : 1 / t ^ b ≤ p) :
    (N / t ^ a) / p ^ B ≤ N * t ^ (b * B) / t ^ a := by
  have h := mul_le_mul_of_nonneg_left (inverse_density_power_le t p b B ht hp hfloor)
    (div_nonneg hN (pow_nonneg ht.le a))
  calc
    _ = (N / t ^ a) * (1 / p ^ B) := by ring
    _ ≤ (N / t ^ a) * t ^ (b * B) := h
    _ = _ := by ring

theorem pair_polynomial_power_lower
    (N t p w r : ℝ) (b : ℕ) (hN : 0 ≤ N) (ht : 0 < t)
    (hp : 1 / t ^ b ≤ p) (hw : N / t ^ b ≤ w) (hr : 1 / t ≤ r) :
    N / t ^ (3 * b + 1) ≤ 3 * w * p ^ 2 * r := by
  have hp0 : 0 ≤ p := (by positivity : (0 : ℝ) ≤ 1 / t ^ b).trans hp
  have hw0 : 0 ≤ w := (div_nonneg hN (pow_nonneg ht.le b)).trans hw
  have hr0 : 0 ≤ r := (by positivity : (0 : ℝ) ≤ 1 / t).trans hr
  have hid : N / t ^ (3 * b + 1) = (N / t ^ b) * (1 / t ^ b) ^ 2 * (1 / t) := by
    have hexp : 3 * b + 1 = b + b * 2 + 1 := by omega
    rw [hexp, pow_add, pow_add, pow_one, div_pow, ← pow_mul]
    field_simp
  calc
    _ = (N / t ^ b) * (1 / t ^ b) ^ 2 * (1 / t) := hid
    _ ≤ w * p ^ 2 * r := by gcongr
    _ ≤ 3 * w * p ^ 2 * r := by nlinarith [mul_nonneg (mul_nonneg hw0 (sq_nonneg p)) hr0]

theorem power_ratio_error_le_quarter
    (N t e x : ℝ) (u v w : ℕ) (ht : 4 ≤ t) (hN : 0 ≤ N)
    (he : e ≤ N * t ^ u / t ^ v) (hx : N / t ^ w ≤ x) (hgap : u + w + 1 ≤ v) :
    e ≤ x / 4 := by
  have hscaled := real_coeff_mul_power_ratio_le (C := 4) (N := N) (t := t)
    (u := u) (v := v) (w := w) (by linarith) hN ht hgap
  have hmul := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 4)
  have hid : 4 * (N * t ^ u / t ^ v) = 4 * N * t ^ u / t ^ v := by ring
  rw [hid] at hmul
  linarith only [hmul, hscaled, hx]

theorem dyadic_pair_error_le_quarter
    (N t p w r : ℝ) (a b B : ℕ) (hN : 0 ≤ N) (ht : 4 ≤ t)
    (hp : 1 / t ^ b ≤ p) (hw : N / t ^ b ≤ w) (hr : 1 / t ≤ r)
    (hgap : b * B + 3 * b + 2 ≤ a) :
    (N / t ^ a) / p ^ B ≤ (3 * w * p ^ 2 * r) / 4 := by
  have htpos : 0 < t := by linarith
  have hppos : 0 < p := (by positivity : (0 : ℝ) < 1 / t ^ b).trans_le hp
  exact power_ratio_error_le_quarter N t _ _ (b * B) a (3 * b + 1) ht hN
    (density_error_power_upper N t p a b B hN htpos hppos hp)
    (pair_polynomial_power_lower N t p w r b hN htpos hp hw hr) (by omega)

end Erdos207
