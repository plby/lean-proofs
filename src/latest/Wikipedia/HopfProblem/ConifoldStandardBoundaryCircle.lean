import Wikipedia.HopfProblem.ConifoldStandardBoundaryAlgebra
import Mathlib.Topology.Instances.Matrix

/-!
# The standard right-circle action on conifold matrices

The action is literal right multiplication by `diag (u⁻¹, u)`.  Unit complex
numbers preserve both determinant and squared Frobenius norm, and the
adjoint-adjugate deformation commutes with this matrix action.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- The diagonal matrix `diag(u⁻¹, u)`, with determinant one for unit `u`. -/
def circleDiagonal (u : ℂ) : MatrixSpace := Matrix.diagonal ![u⁻¹, u]

/-- Literal right multiplication by the standard diagonal circle matrix. -/
def rightCircle (u : ℂ) (M : MatrixSpace) : MatrixSpace := M * circleDiagonal u

theorem circleDiagonal_entries (u : ℂ) :
    circleDiagonal u = !![u⁻¹, 0; 0, u] := by
  simp [circleDiagonal, Matrix.diagonal_fin_two]

theorem rightCircle_apply (u : ℂ) (M : MatrixSpace) (i j : Fin 2) :
    rightCircle u M i j = M i j * ![u⁻¹, u] j :=
  Matrix.mul_diagonal _ _ _ _

theorem rightCircle_entries (u : ℂ) (M : MatrixSpace) :
    rightCircle u M = !![M 0 0 * u⁻¹, M 0 1 * u;
      M 1 0 * u⁻¹, M 1 1 * u] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rightCircle_apply]

private theorem unit_ne_zero (u : ℂ) (hu : ‖u‖ = 1) : u ≠ 0 := by
  intro h
  simp [h] at hu

private theorem unit_normSq (u : ℂ) (hu : ‖u‖ = 1) : Complex.normSq u = 1 := by
  simp [Complex.normSq_eq_norm_sq, hu]

private theorem unit_conj (u : ℂ) (hu : ‖u‖ = 1) : conj u = u⁻¹ := by
  simp [Complex.inv_def, unit_normSq u hu]

theorem det_circleDiagonal (u : ℂ) (hu : ‖u‖ = 1) :
    (circleDiagonal u).det = 1 := by
  simp [circleDiagonal_entries, Matrix.det_fin_two, unit_ne_zero u hu]

theorem det_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    (rightCircle u M).det = M.det := by
  rw [rightCircle, Matrix.det_mul, det_circleDiagonal u hu, mul_one]

theorem frobeniusSq_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    frobeniusSq (rightCircle u M) = frobeniusSq M := by
  simp [frobeniusSq_entries, rightCircle_apply, Complex.normSq_mul, unit_normSq u hu]

theorem adjointAdjugate_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    adjointAdjugate (rightCircle u M) = rightCircle u (adjointAdjugate M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjointAdjugate_entries, rightCircle_apply, unit_conj u hu]

theorem rightCircle_add (u : ℂ) (M N : MatrixSpace) :
    rightCircle u (M + N) = rightCircle u M + rightCircle u N :=
  Matrix.add_mul _ _ _

theorem rightCircle_smul (a : ℝ) (u : ℂ) (M : MatrixSpace) :
    rightCircle u ((a : ℂ) • M) = (a : ℂ) • rightCircle u M :=
  Matrix.smul_mul _ _ _

theorem smul_rightCircle (a : ℝ) (u : ℂ) (M : MatrixSpace) :
    (a : ℂ) • rightCircle u M = rightCircle u ((a : ℂ) • M) :=
  (rightCircle_smul a u M).symm

theorem deform_rightCircle (a : ℝ) (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    deform a (rightCircle u M) = rightCircle u (deform a M) := by
  rw [deform, adjointAdjugate_rightCircle u hu, smul_rightCircle, ← rightCircle_add]
  rfl

@[simp] theorem rightCircle_one (M : MatrixSpace) : rightCircle 1 M = M := by
  ext i j
  fin_cases j <;> simp [rightCircle_apply]

theorem rightCircle_mul (u v : ℂ) (M : MatrixSpace) :
    rightCircle (u * v) M = rightCircle u (rightCircle v M) := by
  ext i j
  fin_cases j <;> simp [rightCircle_apply, mul_assoc, mul_comm]

theorem rightCircle_inv_rightCircle (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    rightCircle u⁻¹ (rightCircle u M) = M := by
  rw [← rightCircle_mul, inv_mul_cancel₀ (unit_ne_zero u hu), rightCircle_one]

theorem rightCircle_rightCircle_inv (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    rightCircle u (rightCircle u⁻¹ M) = M := by
  rw [← rightCircle_mul, mul_inv_cancel₀ (unit_ne_zero u hu), rightCircle_one]

theorem continuous_rightCircle (u : ℂ) : Continuous (rightCircle u) :=
  continuous_id.matrix_mul continuous_const

end Wikipedia.HopfProblem.ConifoldStandardBoundary
