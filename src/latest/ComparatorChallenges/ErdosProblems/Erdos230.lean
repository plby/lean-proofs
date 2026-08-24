/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos230

def IsUnimodular {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i, ‖a i‖ = 1

noncomputable def phasePoly {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial (i.1 + 1) (a i)

def circleValues {n : ℕ} (a : Fin n → ℂ) : Set ℝ :=
  {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖(phasePoly a).eval z‖}

noncomputable def circleMaximum {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  sSup (circleValues a)

theorem not_erdos_230 :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n →
        ∀ a : Fin n → ℂ, IsUnimodular a →
          (1 + c) * Real.sqrt n ≤ circleMaximum a) := by
  sorry

end Erdos230
