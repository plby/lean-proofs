import Mathlib

/-!
# Erdős Problem 225

This file formalizes the trigonometric-polynomial statement through its
equivalent algebraic form: the roots of the associated algebraic polynomial
lie on the complex unit circle.
-/

namespace Erdos225

open scoped BigOperators Interval Topology
open Set MeasureTheory Filter

/-- The algebraic polynomial associated to the coefficient list. -/
noncomputable def coeffPolynomial (n : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k

/-- The trigonometric polynomial on the real line. -/
noncomputable def trigPolynomial (n : ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    c k * Complex.exp (Complex.I * ((k : ℂ) * (θ : ℂ)))

/-- The entire extension whose zeros are required to be real. -/
noncomputable def entireTrigPolynomial (n : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    c k * Complex.exp (Complex.I * ((k : ℂ) * z))

/-- Exact algebraic root condition corresponding to real angular roots. -/
def RootsOnUnitCircle (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.IsRoot z → ‖z‖ = 1

/-- All zeros of the entire angular extension are real. -/
def OnlyRealAngularRoots (n : ℕ) (c : ℕ → ℂ) : Prop :=
  ∀ z : ℂ, entireTrigPolynomial n c z = 0 → z.im = 0

@[simp]


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
