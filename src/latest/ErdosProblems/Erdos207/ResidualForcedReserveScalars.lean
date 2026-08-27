/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualAdjoinScalars

/-! # Exact density cancellation when new triangles force reserve edges -/

namespace Erdos207

open scoped NNReal

theorem residualForcedReserveAdjoinPartitionTerm_le
    (p r alpha C factor b nInv oldScale newScale : ℝ≥0) (a s e t d h : ℕ)
    (hcard : d = s + t) (hC : 1 ≤ C) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (hscale : oldScale * (alpha * p ^ 3 * r ^ h) ^ t ≤ factor ^ t * newScale) :
    alpha ^ t * (C ^ (a + s + (3 * t + e) + h * t) *
      (p ^ (3 * t + e) * r ^ (h * t) * nInv ^ a * oldScale + b)) ≤
      (C ^ (3 + h) * factor) ^ (a + d + e) * (p ^ e * nInv ^ a * newScale + b) := by
  have hcExp : C ^ (a + s + (3 * t + e) + h * t) ≤ (C ^ (3 + h)) ^ (a + d + e) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hC
    rw [Nat.add_mul]
    have ht : t ≤ a + d + e := by omega
    have hht := Nat.mul_le_mul_left h ht
    omega
  have hfExp : factor ^ t ≤ factor ^ (a + d + e) := pow_le_pow_right₀ hfactor (by omega)
  have hbase : C ^ (a + s + (3 * t + e) + h * t) * factor ^ t ≤
      (C ^ (3 + h) * factor) ^ (a + d + e) := by
    rw [mul_pow]
    exact mul_le_mul hcExp hfExp zero_le zero_le
  have herror : alpha ^ t * b ≤ factor ^ t * b :=
    mul_le_mul_of_nonneg_right ((pow_le_one₀ zero_le halpha).trans (one_le_pow₀ hfactor)) zero_le
  have hmain : (p ^ e * nInv ^ a) * (oldScale * (alpha * p ^ 3 * r ^ h) ^ t) ≤
      factor ^ t * (p ^ e * nInv ^ a * newScale) := by
    calc
      _ ≤ (p ^ e * nInv ^ a) * (factor ^ t * newScale) := mul_le_mul_of_nonneg_left hscale zero_le
      _ = _ := by ring
  have hp : p ^ (3 * t + e) = (p ^ 3) ^ t * p ^ e := by rw [pow_add, pow_mul]
  calc
    _ = C ^ (a + s + (3 * t + e) + h * t) *
        ((p ^ e * nInv ^ a) * (oldScale * (alpha * p ^ 3 * r ^ h) ^ t) + alpha ^ t * b) := by
      rw [hp, pow_mul]
      simp only [mul_pow]
      ring
    _ ≤ C ^ (a + s + (3 * t + e) + h * t) *
        (factor ^ t * (p ^ e * nInv ^ a * newScale) + factor ^ t * b) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain herror) zero_le
    _ = (C ^ (a + s + (3 * t + e) + h * t) * factor ^ t) *
        (p ^ e * nInv ^ a * newScale + b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase zero_le

end Erdos207
