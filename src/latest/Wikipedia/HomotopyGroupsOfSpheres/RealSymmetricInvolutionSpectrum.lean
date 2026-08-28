import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
import Mathlib.Analysis.Matrix.Spectrum

/-! # Real symmetric involutions have an orthogonal eigenbasis with eigenvalues plus or minus one -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem symmetric_diagonalization (A : Matrix N N ℝ) (hsym : A.transpose = A) :
    ∃ (U : unitary (Matrix N N ℝ)) (μ : N → ℝ),
      A = U.val * Matrix.diagonal μ * U.val.transpose ∧ A.trace = ∑ a, μ a := by
  have hA : A.IsHermitian := by
    change star A = A
    rw [star_eq_transpose, hsym]
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_, hA.trace_eq_sum_eigenvalues⟩
  simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
    Function.id_comp, star_eq_transpose] using hA.spectral_theorem

theorem symmetric_involution_diagonalization (A : Matrix N N ℝ)
    (hsym : A.transpose = A) (hsq : A * A = 1) :
    ∃ (U : unitary (Matrix N N ℝ)) (μ : N → ℝ),
      (∀ a, μ a = 1 ∨ μ a = -1) ∧
      A = U.val * Matrix.diagonal μ * U.val.transpose ∧ A.trace = ∑ a, μ a := by
  have hA : A.IsHermitian := by
    change star A = A
    rw [star_eq_transpose, hsym]
  let U := hA.eigenvectorUnitary
  let μ := hA.eigenvalues
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix N N ℝ) (star U) A = Matrix.diagonal μ := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hD : Matrix.diagonal μ * Matrix.diagonal μ = 1 := by
    have he := congrArg (Unitary.conjStarAlgAut ℝ (Matrix N N ℝ) (star U)) hsq
    rw [map_mul, map_one, hdiag] at he
    exact he
  have hsign (a : N) : μ a = 1 ∨ μ a = -1 := by
    have he := congrArg (fun B : Matrix N N ℝ ↦ B a a) hD
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at he
    exact mul_self_eq_one_iff.mp he
  refine ⟨U, μ, hsign, ?_, ?_⟩
  · simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
      Function.id_comp, star_eq_transpose] using hA.spectral_theorem
  · exact hA.trace_eq_sum_eigenvalues

end Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
