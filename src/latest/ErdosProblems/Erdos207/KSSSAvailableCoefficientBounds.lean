/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSAvailableCurvatureBound

/-! # Uniform value and derivative budgets from the finite coefficient bounds -/

namespace Erdos207

open Finset

noncomputable section

def ksssAvailableSlopeBudget (orders : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  9 + ∑ d ∈ orders, (d : ℝ) * b d

def ksssAvailableCurvatureBudget (orders : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  54 + 18 * (∑ d ∈ orders, (d : ℝ) * b d) +
    (∑ d ∈ orders, (d : ℝ) * b d) ^ 2 + ∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d

theorem ksssAvailable_derivative_budgets_nonneg
    (orders : Finset ℕ) (b : ℕ → ℝ) (hb : ∀ d ∈ orders, 0 ≤ b d) :
    0 ≤ ksssAvailableSlopeBudget orders b ∧ 0 ≤ ksssAvailableCurvatureBudget orders b := by
  have hB₁ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * b d := sum_nonneg fun d hd ↦
    mul_nonneg (Nat.cast_nonneg d) (hb d hd)
  have hB₂ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d := sum_nonneg fun d hd ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg _)) (hb d hd)
  dsimp only [ksssAvailableSlopeBudget, ksssAvailableCurvatureBudget]
  constructor <;> positivity

theorem ksssAvailable_uniform_value_derivative_bounds
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d) :
    0 ≤ ksssAvailableTrajectory orders a E₀ A₀ t ∧
      ksssAvailableTrajectory orders a E₀ A₀ t ≤ A₀ ∧
      |ksssAvailableSlope orders a E₀ A₀ t| * E₀ ≤ A₀ * ksssAvailableSlopeBudget orders b ∧
      |ksssAvailableCurvature orders a E₀ A₀ t| * E₀ ^ 2 ≤ A₀ * ksssAvailableCurvatureBudget orders b := by
  have hp0 := (ksssEdgeDensity_pos hE hclock).le
  have hp1 := ksssEdgeDensity_le_one hE ht
  have hr := ksssPoissonRate_mul_clock_le_sum orders a b horders ha hab ht (by linarith)
  have hv := ksssPoissonCurvature_mul_clock_sq_le_sum orders a b ha hab ht (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [ksssAvailableTrajectory]
    positivity
  · refine (ksssAvailableTrajectory_bounds orders a b ha hab hE hA ht hclock).2.trans ?_
    have hp3 : ksssEdgeDensity E₀ t ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hp0 hp1 3
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp3 hA
  · exact ksssAvailableSlope_mul_clock_le orders a E₀ A₀ t _ hE hA ht hclock ha hr
  · exact ksssAvailableCurvature_mul_clock_sq_le orders a E₀ A₀ t _ _ hE hA ht hclock ha hr hv

end

end Erdos207
