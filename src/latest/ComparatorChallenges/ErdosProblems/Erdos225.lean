/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Set

/-!
# Erdős Problem 225

This file formalizes the trigonometric-polynomial statement through its
equivalent algebraic form: the roots of the associated algebraic polynomial
lie on the complex unit circle.
-/

namespace Erdos225

/-- The algebraic polynomial associated to the coefficient list. -/
noncomputable def coeffPolynomial (n : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k

/-- The trigonometric polynomial on the real line. -/
noncomputable def trigPolynomial (n : ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    c k * Complex.exp (Complex.I * ((k : ℂ) * (θ : ℂ)))

/-- Exact algebraic root condition corresponding to real angular roots. -/
def RootsOnUnitCircle (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.IsRoot z → ‖z‖ = 1

theorem erdos_225
    (n : ℕ) (c : ℕ → ℂ) (hn : 0 < n) (hcn : c n ≠ 0) (hc0 : c 0 ≠ 0)
    (hroots : RootsOnUnitCircle (coeffPolynomial n c))
    (hmax :
      (∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖trigPolynomial n c θ‖ ≤ 1) ∧
      ∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖trigPolynomial n c θ‖ = 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖trigPolynomial n c θ‖) ≤ 4 := by
  sorry

end Erdos225
