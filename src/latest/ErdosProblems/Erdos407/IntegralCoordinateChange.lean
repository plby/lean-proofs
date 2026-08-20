/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.DeterminantGap
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Integral inverse coordinate changes

The auxiliary-polynomial argument is formulated with integral coordinate
matrices.  A rational nonsingular family of local forms supplies such a
matrix by clearing the common denominator of the inverse form matrix.  This
file records that construction and, crucially, proves that its rational
image is still nonsingular.
-/

namespace Erdos407.PadicSubspace

open scoped Matrix

noncomputable section

/-- The positive common denominator of the inverse local form matrix. -/
def inverseFormDenominator {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23) : ℕ :=
  ((formMatrix L v)⁻¹).den

/-- The inverse local form matrix with all rational denominators cleared. -/
def integralInverseFormMatrix {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23) :
    Matrix (Fin n) (Fin n) ℤ :=
  ((formMatrix L v)⁻¹).num

theorem inverseFormDenominator_ne_zero {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (v : Place23) : inverseFormDenominator L v ≠ 0 :=
  Matrix.den_ne_zero ((formMatrix L v)⁻¹)

@[simp] theorem integralInverseFormMatrix_div_den {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (v : Place23) (i j : Fin n) :
    (integralInverseFormMatrix L v i j : ℚ) / inverseFormDenominator L v =
      (formMatrix L v)⁻¹ i j := by
  exact Matrix.num_div_den ((formMatrix L v)⁻¹) i j

/-- Clearing denominators only rescales the inverse form matrix by a fixed
nonzero rational number. -/
theorem integralInverseFormMatrix_map_eq_smul {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23) :
    (integralInverseFormMatrix L v).map (Int.castRingHom ℚ) =
      (inverseFormDenominator L v : ℚ) • (formMatrix L v)⁻¹ := by
  ext i j
  change (integralInverseFormMatrix L v i j : ℚ) =
    (inverseFormDenominator L v : ℚ) * (formMatrix L v)⁻¹ i j
  have hden : (inverseFormDenominator L v : ℚ) ≠ 0 := by
    exact_mod_cast inverseFormDenominator_ne_zero L v
  have h := (div_eq_iff hden).mp
    (integralInverseFormMatrix_div_den L v i j)
  simpa [mul_comm] using h

/-- The denominator-cleared inverse remains nonsingular over `ℚ`. -/
theorem integralInverseFormMatrix_det_ne_zero {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    (hL : IsNonsingularFamily L) (v : Place23) :
    ((integralInverseFormMatrix L v).map (Int.castRingHom ℚ)).det ≠ 0 := by
  rw [integralInverseFormMatrix_map_eq_smul, Matrix.det_smul]
  apply mul_ne_zero
  · apply pow_ne_zero
    exact_mod_cast inverseFormDenominator_ne_zero L v
  · exact ((formMatrix L v).isUnit_nonsing_inv_det
      (isUnit_iff_ne_zero.mpr (formMatrix_det_ne_zero hL v))).ne_zero

end

end Erdos407.PadicSubspace
