/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoverDownDensityScalars

/-! # The sharper density budget needed for sampled inner-edge collisions -/

namespace Erdos207

open scoped NNReal

theorem link_collision_mean_cancellation
    (degree overlap sigma d m a r p n u : ℝ≥0)
    (hr : 0 < r) (hp : 0 < p) (hu : 0 < u)
    (hdegree : degree ≤ d * r * p ^ 2 * u)
    (hoverlap : overlap ≤ m * r ^ 2 * n)
    (hsigma : sigma ≤ a / (r * p ^ 2 * u)) :
    degree * overlap * sigma ^ 2 ≤ d * m * (a ^ 2 * r * n / (p ^ 2 * u)) := by
  calc
    _ ≤ (d * r * p ^ 2 * u) * (m * r ^ 2 * n) * (a / (r * p ^ 2 * u)) ^ 2 := by gcongr
    _ = _ := by field_simp

theorem link_collision_mean_power_decay
    (t n u K A a r p : ℝ≥0) (f s b v h : ℕ)
    (ht : 1 ≤ t) (hu : 0 < u)
    (ha : a ≤ A * t ^ f) (hr : r ≤ 1 / t ^ s) (hp : 1 / t ^ b ≤ p)
    (hsize : n ≤ K * t ^ v * u) (hgap : f * 2 + v + b * 2 + h ≤ s) :
    a ^ 2 * r * n / (p ^ 2 * u) ≤ (A ^ 2 * K) / t ^ h := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < 1 / t ^ b := by positivity
  have hratio : t ^ (f * 2 + v + b * 2) / t ^ s ≤ 1 / t ^ h := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (A * t ^ f) ^ 2 * (1 / t ^ s) * (K * t ^ v * u) / ((1 / t ^ b) ^ 2 * u) := by
      gcongr
    _ = (A ^ 2 * K) * (t ^ (f * 2 + v + b * 2) / t ^ s) := by
      simp only [pow_add, pow_mul, mul_pow, div_pow, one_pow]
      field_simp
    _ ≤ (A ^ 2 * K) * (1 / t ^ h) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem link_marked_weight_ratio_power_le
    (t n u K A a p : ℝ≥0) (f s b v : ℕ)
    (ht : 1 ≤ t) (hu : 0 < u) (ha : a ≤ A * t ^ f)
    (hp : 1 / t ^ b ≤ p) (hsize : n ≤ K * t ^ v * u) :
    a * n / ((1 / t ^ s) * p ^ 2 * u) ≤ (A * K) * t ^ (f + v + s + b * 2) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < 1 / t ^ b := by positivity
  calc
    _ ≤ (A * t ^ f) * (K * t ^ v * u) / ((1 / t ^ s) * (1 / t ^ b) ^ 2 * u) := by gcongr
    _ = _ := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp

theorem link_marked_extension_power_decay
    (t n z w Z W : ℝ≥0) (zExp wExp q L h : ℕ) (ht : 1 ≤ t)
    (hn : t ^ L ≤ n) (hz : z ≤ Z * t ^ zExp) (hw : w ≤ W * t ^ wExp)
    (hgap : zExp + wExp * (q + 1) + h ≤ L) :
    z * w ^ (q + 1) / n ≤ (Z * W ^ (q + 1)) / t ^ h := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn0 : 0 < t ^ L := pow_pos ht0 _
  have hratio : t ^ (zExp + wExp * (q + 1)) / t ^ L ≤ 1 / t ^ h := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (Z * t ^ zExp) * (W * t ^ wExp) ^ (q + 1) / t ^ L := by gcongr
    _ = (Z * W ^ (q + 1)) * (t ^ (zExp + wExp * (q + 1)) / t ^ L) := by
      rw [pow_add t zExp (wExp * (q + 1)), pow_mul t wExp (q + 1), mul_pow]
      ring
    _ ≤ (Z * W ^ (q + 1)) * (1 / t ^ h) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

end Erdos207
