/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteRealExpectation
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # Centering raw increments by a trajectory and a growing error envelope -/

namespace Erdos207

theorem centered_step_drift_nonpos
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (σ df de slope D C : ℝ) (hσ : |σ| = 1)
    (hraw : |L.expectationReal X - slope| ≤ D)
    (hdisc : |df - slope| ≤ C) (henv : D + C ≤ de) :
    L.expectationReal (fun ω ↦ σ * (X ω - df) - de) ≤ 0 := by
  have hd : |L.expectationReal X - df| ≤ D + C := by
    simpa only [sub_self, sub_zero] using abs_difference_error_le hraw hdisc
  rw [FiniteLaw.expectationReal_sub, FiniteLaw.expectationReal_const_mul,
    FiniteLaw.expectationReal_sub, FiniteLaw.expectationReal_const, FiniteLaw.expectationReal_const]
  have hbound : σ * (L.expectationReal X - df) ≤ D + C := by
    calc
      _ ≤ |σ * (L.expectationReal X - df)| := le_abs_self _
      _ = |L.expectationReal X - df| := by rw [abs_mul, hσ, one_mul]
      _ ≤ _ := hd
  linarith

theorem centered_step_abs_le
    (σ x df de : ℝ) (hσ : |σ| = 1) :
    |σ * (x - df) - de| ≤ |x| + |df| + |de| := by
  calc
    _ ≤ |σ * (x - df)| + |de| := abs_sub _ _
    _ = |x - df| + |de| := by rw [abs_mul, hσ, one_mul]
    _ ≤ _ := add_le_add (abs_sub _ _) le_rfl

theorem centered_step_sq_le
    (σ x df de : ℝ) (hσ : |σ| = 1) :
    (σ * (x - df) - de) ^ 2 ≤ 2 * x ^ 2 + 2 * (|df| + |de|) ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg (σ * (x - df) - de)) (centered_step_abs_le σ x df de hσ) 2
  rw [sq_abs] at h
  have hs := sq_nonneg (|x| - (|df| + |de|))
  have hx := sq_abs x
  nlinarith

theorem centered_step_secondMoment_le
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (σ df de v : ℝ) (hσ : |σ| = 1) (hraw : L.expectationReal (fun ω ↦ X ω ^ 2) ≤ v) :
    L.expectationReal (fun ω ↦ (σ * (X ω - df) - de) ^ 2) ≤
      2 * v + 2 * (|df| + |de|) ^ 2 := by
  calc
    _ ≤ L.expectationReal (fun ω ↦ 2 * X ω ^ 2 + 2 * (|df| + |de|) ^ 2) :=
      L.expectationReal_mono (fun ω ↦ centered_step_sq_le σ (X ω) df de hσ)
    _ = 2 * L.expectationReal (fun ω ↦ X ω ^ 2) + 2 * (|df| + |de|) ^ 2 := by
      rw [FiniteLaw.expectationReal_add, FiniteLaw.expectationReal_const_mul,
        FiniteLaw.expectationReal_const]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hraw (by norm_num)) le_rfl

end Erdos207
