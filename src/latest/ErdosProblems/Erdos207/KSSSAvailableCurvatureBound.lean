/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSAvailableCurvature
import ErdosProblems.Erdos207.AvailableCurvatureArithmetic

/-! # Uniform clock-scaled derivative bounds for available triangles -/

namespace Erdos207

noncomputable section

theorem ksssAvailableSlope_mul_clock_le
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t B₁ : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hB₁ : ksssPoissonRate orders a t * E₀ ≤ B₁) :
    |ksssAvailableSlope orders a E₀ A₀ t| * E₀ ≤ A₀ * (9 + B₁) := by
  let p := ksssEdgeDensity E₀ t
  let r := ksssPoissonRate orders a t
  let e := Real.exp (-ksssPoissonExponent orders a t)
  let b := (-9 / E₀) * p ^ 2 - p ^ 3 * r
  have hp0 : 0 ≤ p := (ksssEdgeDensity_pos hE hclock).le
  have hp1 : p ≤ 1 := ksssEdgeDensity_le_one hE ht
  have hr0 : 0 ≤ r := ksssPoissonRate_nonneg orders a ha ht
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (ksssPoissonExponent_nonneg orders a ha ht))
  have hB : 0 ≤ B₁ := (mul_nonneg hr0 hE.le).trans hB₁
  have heq : b * E₀ = -9 * p ^ 2 - p ^ 3 * (r * E₀) := by
    dsimp only [b]
    field_simp <;> ring
  have hb : |b| * E₀ ≤ 9 + B₁ := by
    calc
      _ = |b * E₀| := by rw [abs_mul, abs_of_pos hE]
      _ = |-9 * p ^ 2 - p ^ 3 * (r * E₀)| := congrArg abs heq
      _ ≤ _ := available_slope_polynomial_bound p (r * E₀) B₁ hp0 hp1 (mul_nonneg hr0 hE.le) hB₁
  have hscale : 0 ≤ A₀ * e := mul_nonneg hA he0
  calc
    _ = A₀ * e * (|b| * E₀) := by
      change |A₀ * e * b| * E₀ = _
      rw [abs_mul, abs_of_nonneg hscale]
      ring
    _ ≤ A₀ * e * (9 + B₁) := mul_le_mul_of_nonneg_left hb hscale
    _ ≤ A₀ * 1 * (9 + B₁) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 hA) (by positivity)
    _ = _ := by ring

theorem ksssAvailableCurvature_mul_clock_sq_le
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t B₁ B₂ : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hB₁ : ksssPoissonRate orders a t * E₀ ≤ B₁)
    (hB₂ : ksssPoissonCurvature orders a t * E₀ ^ 2 ≤ B₂) :
    |ksssAvailableCurvature orders a E₀ A₀ t| * E₀ ^ 2 ≤
      A₀ * (54 + 18 * B₁ + B₁ ^ 2 + B₂) := by
  let p := ksssEdgeDensity E₀ t
  let r := ksssPoissonRate orders a t
  let v := ksssPoissonCurvature orders a t
  let e := Real.exp (-ksssPoissonExponent orders a t)
  let b := 54 * p / E₀ ^ 2 + 18 * p ^ 2 * r / E₀ + p ^ 3 * r ^ 2 - p ^ 3 * v
  let C := 54 + 18 * B₁ + B₁ ^ 2 + B₂
  have hr0 : 0 ≤ r := ksssPoissonRate_nonneg orders a ha ht
  have hv0 : 0 ≤ v := ksssPoissonCurvature_nonneg orders a ha ht
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (ksssPoissonExponent_nonneg orders a ha ht))
  have heq : b * E₀ ^ 2 = 54 * p + 18 * p ^ 2 * (r * E₀) +
      p ^ 3 * (r * E₀) ^ 2 - p ^ 3 * (v * E₀ ^ 2) := by
    dsimp only [b]
    field_simp <;> ring
  have hb : |b| * E₀ ^ 2 ≤ C := by
    calc
      _ = |b * E₀ ^ 2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg E₀)]
      _ = |54 * p + 18 * p ^ 2 * (r * E₀) + p ^ 3 * (r * E₀) ^ 2 - p ^ 3 * (v * E₀ ^ 2)| := congrArg abs heq
      _ ≤ _ := available_curvature_polynomial_bound p (r * E₀) (v * E₀ ^ 2) B₁ B₂
        (ksssEdgeDensity_pos hE hclock).le (ksssEdgeDensity_le_one hE ht)
        (mul_nonneg hr0 hE.le) hB₁ (mul_nonneg hv0 (sq_nonneg E₀)) hB₂
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg b) (sq_nonneg E₀)).trans hb
  have hscale : 0 ≤ A₀ * e := mul_nonneg hA he0
  calc
    _ = A₀ * e * (|b| * E₀ ^ 2) := by
      change |A₀ * e * b| * E₀ ^ 2 = _
      rw [abs_mul, abs_of_nonneg hscale]
      ring
    _ ≤ A₀ * e * C := mul_le_mul_of_nonneg_left hb hscale
    _ ≤ A₀ * 1 * C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 hA) hC
    _ = _ := by ring

end

end Erdos207
