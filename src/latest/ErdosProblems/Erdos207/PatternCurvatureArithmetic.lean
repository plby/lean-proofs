/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Uniform polynomial bounds for bounded-pattern derivatives -/

namespace Erdos207

def patternCurvatureBudget (h m : ℕ) (B₁ B₂ : ℝ) : ℝ :=
  9 * (h : ℝ) * (h - 1 : ℕ) + 6 * h * m * B₁ + (m : ℝ) ^ 2 * B₁ ^ 2 + m * B₂

theorem pattern_slope_polynomial_bound
    (h m : ℕ) (p r B₁ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hrB : r ≤ B₁) :
    |-(3 * (h : ℝ)) * p ^ (h - 1) - (m : ℝ) * p ^ h * r| ≤ 3 * h + m * B₁ := by
  have hpow : ∀ n : ℕ, p ^ n ≤ 1 := fun n ↦ by
    simpa only [one_pow] using pow_le_pow_left₀ hp hp1 n
  have hfirst : 3 * (h : ℝ) * p ^ (h - 1) ≤ 3 * h := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hpow (h - 1)) (by positivity : 0 ≤ 3 * (h : ℝ))
  have hsecond : (m : ℝ) * p ^ h * r ≤ m * B₁ := by
    have hpr : p ^ h * r ≤ B₁ := by
      simpa only [one_mul] using mul_le_mul (hpow h) hrB hr (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg m)
  have hneg : -(3 * (h : ℝ)) * p ^ (h - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (pow_nonneg hp _)
  have hnon : 0 ≤ (m : ℝ) * p ^ h * r := by positivity
  rw [abs_of_nonpos (by linarith only [hneg, hnon] :
    -(3 * (h : ℝ)) * p ^ (h - 1) - (m : ℝ) * p ^ h * r ≤ 0)]
  linarith only [hfirst, hsecond]

theorem pattern_curvature_polynomial_bound
    (h m : ℕ) (p r v B₁ B₂ : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hrB : r ≤ B₁) (hv : 0 ≤ v) (hvB : v ≤ B₂) :
    |9 * (h : ℝ) * (h - 1 : ℕ) * p ^ (h - 2) +
      6 * h * m * p ^ (h - 1) * r + (m : ℝ) ^ 2 * p ^ h * r ^ 2 - m * p ^ h * v| ≤
      patternCurvatureBudget h m B₁ B₂ := by
  have hpow : ∀ n : ℕ, p ^ n ≤ 1 := fun n ↦ by
    simpa only [one_pow] using pow_le_pow_left₀ hp hp1 n
  have hfirst : 9 * (h : ℝ) * (h - 1 : ℕ) * p ^ (h - 2) ≤ 9 * h * (h - 1 : ℕ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hpow (h - 2))
      (by positivity : 0 ≤ 9 * (h : ℝ) * (h - 1 : ℕ))
  have hpr : p ^ (h - 1) * r ≤ B₁ := by
    simpa only [one_mul] using mul_le_mul (hpow (h - 1)) hrB hr (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond : 6 * (h : ℝ) * m * p ^ (h - 1) * r ≤ 6 * h * m * B₁ := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpr (by positivity : 0 ≤ 6 * (h : ℝ) * m)
  have hpr2 : p ^ h * r ^ 2 ≤ B₁ ^ 2 := by
    simpa only [one_mul] using mul_le_mul (hpow h)
      (pow_le_pow_left₀ hr hrB 2) (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 1)
  have hthird : (m : ℝ) ^ 2 * p ^ h * r ^ 2 ≤ (m : ℝ) ^ 2 * B₁ ^ 2 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpr2 (sq_nonneg (m : ℝ))
  have hpv : p ^ h * v ≤ B₂ := by
    simpa only [one_mul] using mul_le_mul (hpow h) hvB hv (by norm_num : (0 : ℝ) ≤ 1)
  have hfourth : (m : ℝ) * p ^ h * v ≤ m * B₂ := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpv (Nat.cast_nonneg m)
  have habs := abs_sub
    (9 * (h : ℝ) * (h - 1 : ℕ) * p ^ (h - 2) +
      6 * h * m * p ^ (h - 1) * r + (m : ℝ) ^ 2 * p ^ h * r ^ 2)
    ((m : ℝ) * p ^ h * v)
  have hnon1 : 0 ≤ 9 * (h : ℝ) * (h - 1 : ℕ) * p ^ (h - 2) +
      6 * h * m * p ^ (h - 1) * r + (m : ℝ) ^ 2 * p ^ h * r ^ 2 := by positivity
  have hnon2 : 0 ≤ (m : ℝ) * p ^ h * v := by positivity
  rw [abs_of_nonneg hnon1, abs_of_nonneg hnon2] at habs
  dsimp only [patternCurvatureBudget]
  linarith only [habs, hfirst, hsecond, hthird, hfourth]

end Erdos207
