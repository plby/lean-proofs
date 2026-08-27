/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternTrajectory
import ErdosProblems.Erdos207.PatternCurvatureArithmetic
import ErdosProblems.Erdos207.UnitStepTaylor

/-! # Clock-scaled curvature and the discrete extension-target error -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssPatternCurvature_mul_clock_sq_le
    (orders : Finset ℕ) (a : ℕ → ℝ) (E M time B₁ B₂ : ℝ) (h m : ℕ)
    (hE : 0 < E) (hM : 0 ≤ M) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hB₁ : ksssPoissonRate orders a time * E ≤ B₁)
    (hB₂ : ksssPoissonCurvature orders a time * E ^ 2 ≤ B₂) :
    |ksssPatternCurvature orders a E M h m time| * E ^ 2 ≤ M * patternCurvatureBudget h m B₁ B₂ := by
  let p := ksssEdgeDensity E time
  let r := ksssPoissonRate orders a time
  let v := ksssPoissonCurvature orders a time
  let expTerm := Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time)
  let bracket := 9 * (h : ℝ) * (h - 1 : ℕ) / E ^ 2 * p ^ (h - 2) +
    6 * (h : ℝ) * m / E * p ^ (h - 1) * r + (m : ℝ) ^ 2 * p ^ h * r ^ 2 - m * p ^ h * v
  let C := patternCurvatureBudget h m B₁ B₂
  have hr : 0 ≤ r := ksssPoissonRate_nonneg orders a ha ht
  have hv : 0 ≤ v := ksssPoissonCurvature_nonneg orders a ha ht
  have he0 : 0 ≤ expTerm := (Real.exp_pos _).le
  have he1 : expTerm ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m))
      (ksssPoissonExponent_nonneg orders a ha ht))
  have hid : bracket * E ^ 2 =
      9 * (h : ℝ) * (h - 1 : ℕ) * p ^ (h - 2) +
        6 * h * m * p ^ (h - 1) * (r * E) + (m : ℝ) ^ 2 * p ^ h * (r * E) ^ 2 -
          m * p ^ h * (v * E ^ 2) := by
    dsimp only [bracket]
    field_simp
    <;> ring
  have hb : |bracket| * E ^ 2 ≤ C := by
    calc
      _ = |bracket * E ^ 2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg E)]
      _ = _ := congrArg abs hid
      _ ≤ _ := pattern_curvature_polynomial_bound h m p (r * E) (v * E ^ 2) B₁ B₂
        (ksssEdgeDensity_pos hE hclock).le (ksssEdgeDensity_le_one hE ht)
        (mul_nonneg hr hE.le) hB₁ (mul_nonneg hv (sq_nonneg E)) hB₂
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg bracket) (sq_nonneg E)).trans hb
  have hscale : 0 ≤ M * expTerm := mul_nonneg hM he0
  calc
    _ = M * expTerm * (|bracket| * E ^ 2) := by
      change |M * expTerm * bracket| * E ^ 2 = _
      rw [abs_mul, abs_of_nonneg hscale]
      ring
    _ ≤ M * expTerm * C := mul_le_mul_of_nonneg_left hb hscale
    _ ≤ M * 1 * C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 hM) hC
    _ = _ := by ring

theorem ksssPatternCurvature_le_coefficients
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E M time : ℝ) (h m : ℕ)
    (hE : 0 < E) (hM : 0 ≤ M) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E ^ d ≤ b d) :
    |ksssPatternCurvature orders a E M h m time| ≤
      M * patternCurvatureBudget h m (∑ d ∈ orders, (d : ℝ) * b d)
        (∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d) / E ^ 2 := by
  apply (le_div_iff₀ (pow_pos hE 2)).mpr
  exact ksssPatternCurvature_mul_clock_sq_le orders a E M time _ _ h m hE hM ht hclock ha
    (ksssPoissonRate_mul_clock_le_sum orders a b horders ha hab ht (by linarith))
    (ksssPoissonCurvature_mul_clock_sq_le_sum orders a b ha hab ht (by linarith))

theorem ksssPatternTrajectory_unitStep_error_le_coefficients
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E M time : ℝ) (h m : ℕ)
    (hE : 0 < E) (hM : 0 ≤ M) (ht : 0 ≤ time) (hclock : 3 * (time + 1) < E)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E ^ d ≤ b d) :
    |ksssPatternTrajectory orders a E M h m (time + 1) - ksssPatternTrajectory orders a E M h m time -
      ksssPatternSlope orders a E M h m time| ≤
      M * patternCurvatureBudget h m (∑ d ∈ orders, (d : ℝ) * b d)
        (∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d) / E ^ 2 := by
  have hb : ∀ d ∈ orders, 0 ≤ b d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hB₁ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * b d := sum_nonneg fun d hd ↦
    mul_nonneg (Nat.cast_nonneg d) (hb d hd)
  have hB₂ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d := sum_nonneg fun d hd ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg _)) (hb d hd)
  refine unitStep_taylor_error_le _ _ _ time _ ?_
    (fun u _ ↦ hasDerivAt_ksssPatternTrajectory orders a E M h m u)
    (fun u _ ↦ hasDerivAt_ksssPatternSlope orders a E M h m u hE.ne') ?_
  · dsimp only [patternCurvatureBudget]
    positivity
  · intro u hu
    exact ksssPatternCurvature_le_coefficients orders a b E M u h m hE hM
      (ht.trans hu.1) (by have h := hu.2; linarith) horders ha hab

end

end Erdos207
