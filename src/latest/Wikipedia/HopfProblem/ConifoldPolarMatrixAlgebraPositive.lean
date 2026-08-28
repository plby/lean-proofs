import Wikipedia.HopfProblem.ConifoldPolarDefs
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positivity for the explicit polar matrix factor

The matrix `M * M.conjTranspose + 1` is positive definite for every matrix `M`.
Multiplication by a positive real scalar preserves this property, as required by
the explicit normalized formula for the polar factor.
-/

noncomputable section

open scoped ComplexOrder

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- Adding the identity to `M * M.conjTranspose` makes it positive definite. -/
theorem posDef_self_mul_conjTranspose_add_one (M : MatrixSpace) :
    (M * M.conjTranspose + (1 : MatrixSpace)).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_self_mul_conjTranspose M) Matrix.PosDef.one

/-- The positive real normalization of `M * M.conjTranspose + 1` is positive definite. -/
theorem posDef_smul_self_mul_conjTranspose_add_one (M : MatrixSpace) {a : ℝ}
    (ha : 0 < a) :
    ((a : ℂ) • (M * M.conjTranspose + (1 : MatrixSpace))).PosDef :=
  (posDef_self_mul_conjTranspose_add_one M).smul (Complex.zero_lt_real.mpr ha)

end Wikipedia.HopfProblem.ConifoldPolar
