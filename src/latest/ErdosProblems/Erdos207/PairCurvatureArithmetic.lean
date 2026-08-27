/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # An explicit dimensionless bound for the pair-trajectory curvature -/

namespace Erdos207

theorem pair_curvature_polynomial_bound
    (p R V B₁ B₂ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hR0 : 0 ≤ R) (hRB : R ≤ B₁) (hV0 : 0 ≤ V) (hVB : V ≤ B₂) :
    |18 + 12 * p * R + p ^ 2 * R ^ 2 - p ^ 2 * V| ≤ 18 + 12 * B₁ + B₁ ^ 2 + B₂ := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith
  have hpR : p * R ≤ B₁ := (mul_le_mul_of_nonneg_right hp1 hR0).trans (by simpa using hRB)
  have hR2 : R ^ 2 ≤ B₁ ^ 2 := pow_le_pow_left₀ hR0 hRB 2
  have hpR2 : p ^ 2 * R ^ 2 ≤ B₁ ^ 2 :=
    (mul_le_mul_of_nonneg_right hp2 (sq_nonneg R)).trans (by simpa using hR2)
  have hpV : p ^ 2 * V ≤ B₂ :=
    (mul_le_mul_of_nonneg_right hp2 hV0).trans (by simpa using hVB)
  have hB₁ : 0 ≤ B₁ := hR0.trans hRB
  have hB₂ : 0 ≤ B₂ := hV0.trans hVB
  have hx : 0 ≤ 18 + 12 * p * R + p ^ 2 * R ^ 2 := by positivity
  have hv : 0 ≤ p ^ 2 * V := mul_nonneg (sq_nonneg p) hV0
  apply abs_le.mpr
  constructor <;> nlinarith

theorem pair_curvature_bracket_mul_clock_sq_le
    (E p r v B₁ B₂ : ℝ) (hE : 0 < E) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 ≤ r) (hrB : r * E ≤ B₁) (hv0 : 0 ≤ v) (hvB : v * E ^ 2 ≤ B₂) :
    |18 / E ^ 2 + 12 * p * r / E + p ^ 2 * r ^ 2 - p ^ 2 * v| * E ^ 2 ≤
      18 + 12 * B₁ + B₁ ^ 2 + B₂ := by
  have heq : (18 / E ^ 2 + 12 * p * r / E + p ^ 2 * r ^ 2 - p ^ 2 * v) * E ^ 2 =
      18 + 12 * p * (r * E) + p ^ 2 * (r * E) ^ 2 - p ^ 2 * (v * E ^ 2) := by
    field_simp <;> ring
  calc
    _ = |(18 / E ^ 2 + 12 * p * r / E + p ^ 2 * r ^ 2 - p ^ 2 * v) * E ^ 2| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg E)]
    _ = |18 + 12 * p * (r * E) + p ^ 2 * (r * E) ^ 2 - p ^ 2 * (v * E ^ 2)| := congrArg abs heq
    _ ≤ _ := pair_curvature_polynomial_bound p (r * E) (v * E ^ 2) B₁ B₂ hp0 hp1
      (mul_nonneg hr0 hE.le) hrB (mul_nonneg hv0 (sq_nonneg E)) hvB

end Erdos207
