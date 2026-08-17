/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos230.Correction
import ErdosProblems.Erdos230.Grid

/-!
# Whole-circle unimodular rounding for Erdős Problem 230

This combines the finite-grid Rademacher correction with the elementary
grid interpolation estimate.
-/

namespace Erdos230

open scoped BigOperators

noncomputable section

open Correction

/-- The monomial phase on the `G`-point period-one grid. -/
def gridPhase {n G : ℕ} (i : Fin (n + 1)) (j : Fin G) : ℂ :=
  periodicPoint ((j : ℕ) / (G : ℝ)) ^ i.1

@[simp]
theorem norm_gridPhase {n G : ℕ} (i : Fin (n + 1)) (j : Fin G) :
    ‖gridPhase i j‖ = 1 := by
  simp [gridPhase]

/-- Round coefficients in the closed unit disk to the unit circle.  The
random estimate controls the correction on the `G`-point grid, and the
second summand is the explicit interpolation loss. -/
theorem exists_unit_rounding_circle_defect {n G : ℕ}
    (a : Fin (n + 1) → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hG : 0 < G) {R : ℝ} (hR : 0 < R)
    (hsmall : G *
      (4 * Real.exp (-R ^ 2 / (8 * defect a))) < 1) :
    ∃ b : Fin (n + 1) → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ theta : ℝ,
        ‖normalizedZerothValue b theta - normalizedZerothValue a theta‖ <
          4 * Real.pi * (n + 1) * n / G + R := by
  obtain ⟨b, hb, hgrid⟩ := exists_unit_rounding_grid_defect
    a ha gridPhase (fun i j => (norm_gridPhase i j).le) hR (by simpa using hsmall)
  refine ⟨b, hb, ?_⟩
  intro theta
  let c : Fin (n + 1) → ℂ := fun i => b i - a i
  have hc : ∀ i, ‖c i‖ ≤ 2 := by
    intro i
    dsimp [c]
    calc
      ‖b i - a i‖ ≤ ‖b i‖ + ‖a i‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hb i).le (ha i)
      _ = 2 := by norm_num
  have hcirc := norm_normalizedZerothValue_lt_of_grid c hc hG R
    (fun j => by
      simpa [c, normalizedZerothValue, gridPhase] using hgrid j) theta
  rw [normalizedZerothValue, normalizedZerothValue,
    ← Finset.sum_sub_distrib]
  simpa [c, normalizedZerothValue, sub_mul] using hcirc

/-- The zero-defect case needs no random correction. -/
theorem exists_unit_rounding_circle_of_defect_eq_zero {n : ℕ}
    (a : Fin (n + 1) → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hzero : defect a = 0) :
    ∃ b : Fin (n + 1) → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ theta : ℝ,
        ‖normalizedZerothValue b theta - normalizedZerothValue a theta‖ = 0 := by
  refine ⟨a, fun i => norm_eq_one_of_defect_eq_zero a ha hzero i, ?_⟩
  intro theta
  simp

end

end Erdos230
