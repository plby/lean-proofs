/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Dimensionless polynomial bounds for the available trajectory -/

namespace Erdos207

theorem available_slope_polynomial_bound
    (p R B : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hR0 : 0 ≤ R) (hRB : R ≤ B) :
    |-9 * p ^ 2 - p ^ 3 * R| ≤ 9 + B := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith
  have hp3 : p ^ 3 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hp0 hp1 3
  have hprod : p ^ 3 * R ≤ B :=
    (mul_le_mul_of_nonneg_right hp3 hR0).trans (by simpa using hRB)
  have hprod0 : 0 ≤ p ^ 3 * R := mul_nonneg (pow_nonneg hp0 3) hR0
  rw [abs_of_nonpos (by nlinarith)]
  nlinarith

theorem available_curvature_polynomial_bound
    (p R V B₁ B₂ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hR0 : 0 ≤ R) (hRB : R ≤ B₁) (hV0 : 0 ≤ V) (hVB : V ≤ B₂) :
    |54 * p + 18 * p ^ 2 * R + p ^ 3 * R ^ 2 - p ^ 3 * V| ≤
      54 + 18 * B₁ + B₁ ^ 2 + B₂ := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith
  have hp3 : p ^ 3 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hp0 hp1 3
  have hpR : p ^ 2 * R ≤ B₁ :=
    (mul_le_mul_of_nonneg_right hp2 hR0).trans (by simpa using hRB)
  have hR2 : R ^ 2 ≤ B₁ ^ 2 := pow_le_pow_left₀ hR0 hRB 2
  have hpR2 : p ^ 3 * R ^ 2 ≤ B₁ ^ 2 :=
    (mul_le_mul_of_nonneg_right hp3 (sq_nonneg R)).trans (by simpa using hR2)
  have hpV : p ^ 3 * V ≤ B₂ :=
    (mul_le_mul_of_nonneg_right hp3 hV0).trans (by simpa using hVB)
  have hB₁ : 0 ≤ B₁ := hR0.trans hRB
  have hB₂ : 0 ≤ B₂ := hV0.trans hVB
  have hx : 0 ≤ 54 * p + 18 * p ^ 2 * R + p ^ 3 * R ^ 2 := by positivity
  have hv : 0 ≤ p ^ 3 * V := mul_nonneg (pow_nonneg hp0 3) hV0
  apply abs_le.mpr
  constructor <;> nlinarith

end Erdos207
