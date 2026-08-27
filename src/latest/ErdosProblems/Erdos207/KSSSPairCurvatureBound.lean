/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPairCurvature
import ErdosProblems.Erdos207.PairCurvatureArithmetic
import ErdosProblems.Erdos207.UnitStepTaylor

/-! # Uniform pair curvature and the resulting discrete-step error -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssPairCurvature_mul_clock_cube_le
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t B₁ B₂ : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hB₁ : ksssPoissonRate orders a t * E₀ ≤ B₁)
    (hB₂ : ksssPoissonCurvature orders a t * E₀ ^ 2 ≤ B₂) :
    |ksssPairCurvature orders a E₀ A₀ t| * E₀ ^ 3 ≤
      3 * A₀ * (18 + 12 * B₁ + B₁ ^ 2 + B₂) := by
  let p := ksssEdgeDensity E₀ t
  let r := ksssPoissonRate orders a t
  let v := ksssPoissonCurvature orders a t
  let e := Real.exp (-ksssPoissonExponent orders a t)
  let bracket := 18 / E₀ ^ 2 + 12 * p * r / E₀ + p ^ 2 * r ^ 2 - p ^ 2 * v
  let C := 18 + 12 * B₁ + B₁ ^ 2 + B₂
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (ksssPoissonExponent_nonneg orders a ha ht))
  have hbracket : |bracket| * E₀ ^ 2 ≤ C :=
    pair_curvature_bracket_mul_clock_sq_le E₀ p r v B₁ B₂ hE
      (ksssEdgeDensity_pos hE hclock).le (ksssEdgeDensity_le_one hE ht)
      (ksssPoissonRate_nonneg orders a ha ht) hB₁
      (ksssPoissonCurvature_nonneg orders a ha ht) hB₂
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg bracket) (sq_nonneg E₀)).trans hbracket
  have hscale : 0 ≤ (3 * A₀ / E₀) * e := mul_nonneg (div_nonneg (by positivity) hE.le) he0
  have hid : |ksssPairCurvature orders a E₀ A₀ t| * E₀ ^ 3 =
      (3 * A₀) * e * (|bracket| * E₀ ^ 2) := by
    change |(3 * A₀ / E₀) * e * bracket| * E₀ ^ 3 = _
    rw [abs_mul, abs_of_nonneg hscale]
    field_simp <;> ring
  calc
    _ = (3 * A₀) * e * (|bracket| * E₀ ^ 2) := hid
    _ ≤ (3 * A₀) * e * C := mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (3 * A₀) * 1 * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 (by positivity)) hC
    _ = _ := by ring

theorem ksssPairCurvature_le_of_coefficient_bounds
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d) :
    |ksssPairCurvature orders a E₀ A₀ t| ≤
      (3 * A₀ * (18 + 12 * (∑ d ∈ orders, (d : ℝ) * b d) +
        (∑ d ∈ orders, (d : ℝ) * b d) ^ 2 +
          (∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d))) / E₀ ^ 3 := by
  apply (le_div_iff₀ (pow_pos hE 3)).mpr
  exact ksssPairCurvature_mul_clock_cube_le orders a E₀ A₀ t _ _ hE hA ht hclock ha
    (ksssPoissonRate_mul_clock_le_sum orders a b horders ha hab ht (by linarith))
    (ksssPoissonCurvature_mul_clock_sq_le_sum orders a b ha hab ht (by linarith))

theorem ksssPairTrajectory_unitStep_error_le
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t C : ℝ)
    (hE : E₀ ≠ 0) (hC : 0 ≤ C)
    (hcurv : ∀ u ∈ Set.Icc t (t + 1), |ksssPairCurvature orders a E₀ A₀ u| ≤ C) :
    |ksssPairTrajectory orders a E₀ A₀ (t + 1) - ksssPairTrajectory orders a E₀ A₀ t -
      ksssPairSlope orders a E₀ A₀ t| ≤ C := by
  exact unitStep_taylor_error_le _ _ _ t C hC
    (fun u _ ↦ hasDerivAt_ksssPairTrajectory_slope orders a E₀ A₀ u)
    (fun u _ ↦ hasDerivAt_ksssPairSlope orders a E₀ A₀ u hE) hcurv

theorem ksssPairTrajectory_unitStep_error_le_coefficients
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * (t + 1) < E₀)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d) :
    |ksssPairTrajectory orders a E₀ A₀ (t + 1) - ksssPairTrajectory orders a E₀ A₀ t -
      ksssPairSlope orders a E₀ A₀ t| ≤
      (3 * A₀ * (18 + 12 * (∑ d ∈ orders, (d : ℝ) * b d) +
        (∑ d ∈ orders, (d : ℝ) * b d) ^ 2 +
          (∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d))) / E₀ ^ 3 := by
  have hb : ∀ d ∈ orders, 0 ≤ b d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hB₁ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * b d := sum_nonneg fun d hd ↦
    mul_nonneg (Nat.cast_nonneg d) (hb d hd)
  have hB₂ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d := sum_nonneg fun d hd ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg _)) (hb d hd)
  apply ksssPairTrajectory_unitStep_error_le orders a E₀ A₀ t _ hE.ne' (by positivity)
  intro u hu
  exact ksssPairCurvature_le_of_coefficient_bounds orders a b E₀ A₀ u hE hA
    (ht.trans hu.1) (by have h := hu.2; linarith) horders ha hab

theorem ksssPairSlope_eq_source_drift
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d) (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0) :
    ksssPairSlope orders a E₀ A₀ t = -(3 / (E₀ * ksssEdgeDensity E₀ t)) *
      (ksssThreatTrajectory orders a E₀ A₀ t - ksssPairTrajectory orders a E₀ A₀ t) :=
  (hasDerivAt_ksssPairTrajectory_slope orders a E₀ A₀ t).unique
    (hasDerivAt_ksssPairTrajectory orders a E₀ A₀ t horders hE hp)

end

end Erdos207
