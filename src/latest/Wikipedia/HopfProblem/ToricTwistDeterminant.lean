import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# The determinant of a time-dependent diagonal coordinate change

For the time function `z ↦ z₀ z₁ z₂`, the derivative of a diagonal rescaling
depending on time is a diagonal matrix plus a rank-one correction.  Its
determinant has only a constant term and a term linear in that correction.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

/-- The determinant identity for a diagonal rescaling whose coefficients depend
on the product of the three coordinates.  No coordinate is required to be
nonzero, so the formula also applies on the central fibre. -/
theorem det_diagonal_add_timeGradient (a b z : Fin 3 → ℂ) :
    Matrix.det (Matrix.of fun i j => (if i = j then a i else 0) +
      (b i * z i) * (![z 1 * z 2, z 0 * z 2, z 0 * z 1] : Fin 3 → ℂ) j) =
    a 0 * a 1 * a 2 + (z 0 * z 1 * z 2) *
      (b 0 * a 1 * a 2 + a 0 * b 1 * a 2 + a 0 * a 1 * b 2) := by
  simp [Matrix.det_fin_three]
  ring

end Wikipedia.HopfProblem.ToricSpace
