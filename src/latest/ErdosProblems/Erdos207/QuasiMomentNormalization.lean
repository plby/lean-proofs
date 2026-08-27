/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMoment

/-! # Exact normalization at the future-pattern loss scale -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem boundedIntersectionMomentCoefficient_mono_left {d D s : ℕ} (h : d ≤ D) :
    boundedIntersectionMomentCoefficient d s ≤ boundedIntersectionMomentCoefficient D s := by
  unfold boundedIntersectionMomentCoefficient
  gcongr
  omega

theorem quasi_moment_main_normalization
    (C K p n epsilon eta : ℝ≥0) (m q d s : ℕ)
    (hp : 0 < p) (hn : 0 < n) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    C ^ (s*d) * (K * p ^ (m+1) * n) ^ s / (epsilon * p ^ m * eta ^ q * n) ^ s =
      (C ^ d * K * p / (epsilon * eta ^ q)) ^ s := by
  rw [Nat.mul_comm s d, pow_mul, ← mul_pow, ← div_pow]
  congr 1
  rw [pow_succ]
  field_simp

theorem quasi_moment_error_normalization
    (C b P R : ℝ≥0) (d s : ℕ) :
    C ^ (s*d) * (b * P ^ s) / R ^ s = b * (C ^ d * P / R) ^ s := by
  rw [div_pow, mul_pow, ← pow_mul]
  rw [Nat.mul_comm d s]
  ring

theorem quasi_moment_normalized_bound
    (C K p n epsilon eta b P : ℝ≥0) (m q d s : ℕ)
    (hp : 0 < p) (hn : 0 < n) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    C ^ (s*d) * ((K * p ^ (m+1) * n) ^ s + b * P ^ s) /
        (epsilon * p ^ m * eta ^ q * n) ^ s =
      (C ^ d * K * p / (epsilon * eta ^ q)) ^ s +
        b * (C ^ d * P / (epsilon * p ^ m * eta ^ q * n)) ^ s := by
  rw [mul_add, add_div, quasi_moment_main_normalization C K p n epsilon eta m q d s hp hn hepsilon heta,
    quasi_moment_error_normalization]

theorem normalized_local_inner_degree_ratio
    (n M sigma epsilon p eta : ℝ≥0) (h : ℕ) (hn : 0 < n) :
    2 * n * M * sigma / (epsilon * p ^ h * eta ^ (h^2) * n) =
      2 * M * sigma / (epsilon * p ^ h * eta ^ (h^2)) := by
  calc
    _ = (2 * M * sigma * n) / ((epsilon * p ^ h * eta ^ (h^2)) * n) := by ring
    _ = _ := mul_div_mul_right _ _ hn.ne'

theorem pattern_density_lower_bound
    (p eta : ℝ≥0) (hp : p ≤ 1) (heta : eta ≤ 1) {m q h : ℕ}
    (hm : m ≤ h) (hq : q ≤ h^2) : p ^ h * eta ^ (h^2) ≤ p ^ m * eta ^ q :=
  mul_le_mul (NNReal.pow_antitone_exp _ _ hm hp)
    (NNReal.pow_antitone_exp _ _ hq heta) zero_le zero_le

theorem quasi_normalized_scales_mono
    (C K Kmax p n epsilon eta b P : ℝ≥0) {m q d h D s : ℕ}
    (hC : 1 ≤ C) (hK : K ≤ Kmax) (hp : 0 < p) (hp1 : p ≤ 1)
    (hn : 0 < n) (hepsilon : 0 < epsilon) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hm : m ≤ h) (hq : q ≤ h^2) (hd : d ≤ D) :
    (C ^ d * K * p / (epsilon * eta ^ q)) ^ s +
        b * (C ^ d * P / (epsilon * p ^ m * eta ^ q * n)) ^ s ≤
      (C ^ D * Kmax * p / (epsilon * eta ^ (h^2))) ^ s +
        b * (C ^ D * P / (epsilon * p ^ h * eta ^ (h^2) * n)) ^ s := by
  have hpow := pow_le_pow_right₀ hC hd
  have hden : epsilon * eta ^ (h^2) ≤ epsilon * eta ^ q :=
    mul_le_mul_of_nonneg_left (NNReal.pow_antitone_exp _ _ hq heta1) zero_le
  have hden' : epsilon * p ^ h * eta ^ (h^2) * n ≤ epsilon * p ^ m * eta ^ q * n := by
    have hdensity := pattern_density_lower_bound p eta hp1 heta1 hm hq
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdensity (show 0 ≤ epsilon from zero_le)) (show 0 ≤ n from zero_le)
  apply add_le_add
  · apply pow_le_pow_left'
    exact div_le_div₀ zero_le (by gcongr) (by positivity) hden
  · apply mul_le_mul_of_nonneg_left _ zero_le
    apply pow_le_pow_left'
    exact div_le_div₀ zero_le (by gcongr) (by positivity) hden'

end

end Erdos207
