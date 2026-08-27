/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Clock-scaled monomial derivative bounds with zero-degree cases retained -/

namespace Erdos207

theorem monomial_slope_mul_clock_le
    (c : ℕ) (t E : ℝ) (ht : 0 ≤ t) (htE : t ≤ E) :
    |(c : ℝ) * t ^ (c - 1)| * E ≤ (c : ℝ) * E ^ c := by
  have hE : 0 ≤ E := ht.trans htE
  by_cases hc : c = 0
  · simp [hc]
  have hc1 : 1 ≤ c := by omega
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ (c : ℝ) * E ^ (c - 1) * E :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htE _) (Nat.cast_nonneg c)) hE
    _ = _ := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hc1]

theorem monomial_curvature_mul_clock_sq_le
    (c : ℕ) (t E : ℝ) (ht : 0 ≤ t) (htE : t ≤ E) :
    |(c : ℝ) * (c - 1 : ℕ) * t ^ (c - 2)| * E ^ 2 ≤ (c : ℝ) * (c - 1 : ℕ) * E ^ c := by
  by_cases hc : 2 ≤ c
  · rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (c : ℝ) * (c - 1 : ℕ) * E ^ (c - 2) * E ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htE _) (by positivity)) (sq_nonneg E)
      _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hc]
  · have hz : c - 1 = 0 := by omega
    simp [hz]

theorem power_slope_mul_clock_le
    (m : ℕ) (A A₁ M E C : ℝ)
    (hA : 0 ≤ A) (hAM : A ≤ M) (hE : 0 ≤ E) (_hC : 0 ≤ C)
    (hA₁ : |A₁| * E ≤ M * C) :
    |(m : ℝ) * A ^ (m - 1) * A₁| * E ≤ (m : ℝ) * M ^ m * C := by
  have hM : 0 ≤ M := hA.trans hAM
  by_cases hm : m = 0
  · simp [hm]
  have hm1 : 1 ≤ m := by omega
  calc
    _ = (m : ℝ) * A ^ (m - 1) * (|A₁| * E) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      ring
    _ ≤ (m : ℝ) * M ^ (m - 1) * (M * C) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAM _) (Nat.cast_nonneg m))
        hA₁ (mul_nonneg (abs_nonneg A₁) hE) (by positivity)
    _ = _ := by
      have he : M ^ (m - 1) * M = M ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm1]
      calc
        _ = (m : ℝ) * (M ^ (m - 1) * M) * C := by ring
        _ = _ := by rw [he]

theorem power_quadraticSlope_mul_clock_sq_le
    (m : ℕ) (A A₁ M E C : ℝ)
    (hA : 0 ≤ A) (hAM : A ≤ M) (hE : 0 ≤ E) (_hC : 0 ≤ C)
    (hA₁ : |A₁| * E ≤ M * C) :
    |(m : ℝ) * (m - 1 : ℕ) * A ^ (m - 2) * A₁ ^ 2| * E ^ 2 ≤
      (m : ℝ) * (m - 1 : ℕ) * M ^ m * C ^ 2 := by
  have hM : 0 ≤ M := hA.trans hAM
  by_cases hm : 2 ≤ m
  · have hs : (|A₁| * E) ^ 2 ≤ (M * C) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (abs_nonneg A₁) hE) hA₁ 2
    calc
      _ = (m : ℝ) * (m - 1 : ℕ) * A ^ (m - 2) * (|A₁| * E) ^ 2 := by
        rw [abs_of_nonneg (by positivity), mul_pow, sq_abs]
        ring
      _ ≤ (m : ℝ) * (m - 1 : ℕ) * M ^ (m - 2) * (M * C) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAM _) (by positivity)) hs
          (sq_nonneg _) (by positivity)
      _ = _ := by
        have he : M ^ (m - 2) * M ^ 2 = M ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
        rw [mul_pow]
        calc
          _ = (m : ℝ) * (m - 1 : ℕ) * (M ^ (m - 2) * M ^ 2) * C ^ 2 := by ring
          _ = _ := by rw [he]
  · have hz : m - 1 = 0 := by omega
    simp [hz]

end Erdos207
