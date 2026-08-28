import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Orthogonal permutation matrices and actual matrix conjugation -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def permutationUnitary (e : Equiv.Perm N) : unitary (Matrix N N ℝ) :=
  ⟨e.permMatrix ℝ, by
    constructor <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, mul_inv_cancel, inv_mul_cancel, Matrix.permMatrix_one]⟩

theorem permutation_conjugation (e : Equiv.Perm N) (A : Matrix N N ℝ) :
    (permutationUnitary e).val * A * (permutationUnitary e).val.transpose = A.submatrix e e := by
  change e.permMatrix ℝ * A * (e.permMatrix ℝ).transpose = _
  rw [Matrix.transpose_permMatrix]
  change e.toPEquiv.toMatrix * A * (e⁻¹).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem permutation_conjugation_diagonal (e : Equiv.Perm N) (μ : N → ℝ) :
    (permutationUnitary e).val * Matrix.diagonal μ * (permutationUnitary e).val.transpose =
      Matrix.diagonal (μ ∘ e) := by
  rw [permutation_conjugation, Matrix.submatrix_diagonal_equiv]

end Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
