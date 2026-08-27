/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInputPowerScalars

/-! # Quantitative density cancellations for the two cover-down steps -/

namespace Erdos207

open scoped NNReal

theorem preliminary_survival_reserve_budget
    (t n u K H eta : ℝ≥0) (s c v : ℕ) (ht : 1 ≤ t)
    (hsize : n ≤ K * t ^ v * u) (heta : eta ≤ H / t ^ c) (hgap : 2 * s + v ≤ c) :
    eta * n ≤ (H * K) * (1 / t ^ s) ^ 2 * u := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hratio : t ^ v / t ^ c ≤ 1 / t ^ (2 * s) := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add, Nat.add_comm v (2 * s)] using
      pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (H / t ^ c) * (K * t ^ v * u) := mul_le_mul heta hsize zero_le zero_le
    _ = (H * K * u) * (t ^ v / t ^ c) := by ring
    _ ≤ (H * K * u) * (1 / t ^ (2 * s)) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm s 2]; ring

theorem preliminary_survival_le_reserve
    (t H eta : ℝ≥0) (s c : ℕ) (ht : 1 ≤ t) (hH : H ≤ t)
    (heta : eta ≤ H / t ^ c) (hgap : s + 1 ≤ c) :
    eta ≤ 1 / t ^ s := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  calc
    eta ≤ H / t ^ c := heta
    _ ≤ t / t ^ c := div_le_div_of_nonneg_right hH zero_le
    _ ≤ t / t ^ (s + 1) :=
      div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hgap)
    _ = _ := by rw [pow_succ]; field_simp

theorem correlated_cover_point_le
    (p r n u A B eta D : ℝ≥0) (hp : 0 < p) (hr : 0 < r) (hn : 0 < n) (hu : 0 < u)
    (hbudget : eta * n ≤ D * r ^ 2 * u) :
    A / (p ^ 2 * n) + eta * (B / (r ^ 2 * p ^ 2 * u)) ≤
      (A + B * D) / (p ^ 2 * n) := by
  have hratio : eta * n / (r ^ 2 * u) ≤ D :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_assoc] using hbudget)
  have hinternal : eta * (B / (r ^ 2 * p ^ 2 * u)) ≤ (B * D) / (p ^ 2 * n) := by
    apply (le_div_iff₀ (by positivity : 0 < p ^ 2 * n)).mpr
    calc
      _ = B * (eta * n / (r ^ 2 * u)) := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio zero_le
  simpa only [add_div] using add_le_add le_rfl hinternal

theorem triangle_point_density_cancellation
    (alpha p n factor : ℝ≥0) (hp : 0 < p) (hn : 0 < n)
    (halpha : alpha ≤ factor / (p ^ 2 * n)) :
    alpha * p ^ 3 ≤ factor * (p / n) := by
  calc
    _ ≤ (factor / (p ^ 2 * n)) * p ^ 3 := mul_le_mul_of_nonneg_right halpha zero_le
    _ = _ := by field_simp <;> ring

theorem link_sparsification_reserve_budget
    (t n u K : ℝ≥0) (s f v : ℕ) (ht : 1 ≤ t)
    (hsize : n ≤ K * t ^ v * u) (hgap : f + v ≤ s) :
    t ^ f * (1 / t ^ s) * n ≤ K * u := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hratio : t ^ (f + v) / t ^ s ≤ 1 :=
    (div_le_one (pow_pos ht0 _)).mpr (pow_le_pow_right₀ ht hgap)
  calc
    _ ≤ t ^ f * (1 / t ^ s) * (K * t ^ v * u) := mul_le_mul_of_nonneg_left hsize zero_le
    _ = (K * u) * (t ^ (f + v) / t ^ s) := by rw [pow_add]; ring
    _ ≤ (K * u) * 1 := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := mul_one _

theorem link_point_density_cancellation
    (alpha p r n u A scale D : ℝ≥0) (hp : 0 < p) (hr : 0 < r) (hn : 0 < n) (hu : 0 < u)
    (halpha : alpha ≤ A * scale / (r * p ^ 2 * u)) (hbudget : scale * r * n ≤ D * u) :
    alpha * p ^ 3 * r ^ 2 ≤ (A * D) * (p / n) := by
  have hratio : scale * r * n / u ≤ D := (div_le_iff₀ hu).mpr hbudget
  calc
    _ ≤ (A * scale / (r * p ^ 2 * u)) * p ^ 3 * r ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right halpha zero_le) zero_le
    _ = (A * (p / n)) * (scale * r * n / u) := by field_simp <;> ring
    _ ≤ (A * (p / n)) * D := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

theorem inversePower_triangle_point_le_one
    (t p n factor : ℝ≥0) (b L : ℕ) (ht : 1 ≤ t) (hp : 1 / t ^ b ≤ p)
    (hn : t ^ L ≤ n) (hfactor : factor ≤ t) (hgap : 2 * b + 1 ≤ L) :
    factor / (p ^ 2 * n) ≤ 1 := by
  have hmass : t ≤ p ^ 2 * n := by
    simpa only [pow_one] using
      inversePower_density_ge_power t p n b 2 1 L ht hp (by omega) hn
  have hpos : 0 < p ^ 2 * n := (zero_lt_one.trans_le ht).trans_le hmass
  exact (div_le_one hpos).mpr (hfactor.trans hmass)

theorem inversePower_link_point_le_one
    (t p u A : ℝ≥0) (b s f L : ℕ) (ht : 1 ≤ t) (hp : 1 / t ^ b ≤ p)
    (hu : t ^ L ≤ u) (hA : A ≤ t) (hgap : 2 * b + s + f + 1 ≤ L) :
    A * t ^ f / ((1 / t ^ s) * p ^ 2 * u) ≤ 1 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hmass : t ^ (f + 1) ≤ (1 / t ^ s) * (p ^ 2 * u) := by
    apply le_trans (powerRatio_ge_power t u (b * 2 + s) (f + 1) L ht (by omega) hu)
    exact inversePower_mul_density_lower t p u b s 2 hp
  have hden : 0 < (1 / t ^ s) * p ^ 2 * u := by
    rw [mul_assoc]
    exact (pow_pos ht0 _).trans_le hmass
  apply (div_le_one hden).mpr
  calc
    A * t ^ f ≤ t * t ^ f := mul_le_mul_of_nonneg_right hA zero_le
    _ = t ^ (f + 1) := (pow_succ' _ _).symm
    _ ≤ _ := by simpa only [mul_assoc] using hmass

end Erdos207
