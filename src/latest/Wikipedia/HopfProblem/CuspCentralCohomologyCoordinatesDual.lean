import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDual
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Matrix pullback in integral dual coordinates

The dual coordinates are evaluations on the inverse images of the actual
standard basis.  Precomposition therefore has the transpose matrix of
the original linear map.  This linear-algebra helper does not identify
cohomology with a formal dual or identify pullback with inverse transport.
-/

noncomputable section

open scoped BigOperators Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open Elliptic.HigherHomology

variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Precomposition acts by the transpose of the proved original matrix. -/
theorem intDualCoordinatesOfEquiv_comp_matrix
    (e : M ≃ₗ[ℤ] (Fin k → ℤ)) (L : M →ₗ[ℤ] M)
    (A : Matrix (Fin k) (Fin k) ℤ)
    (hL : ∀ x, e (L x) = A *ᵥ e x) (φ : M →ₗ[ℤ] ℤ) :
    intDualCoordinatesOfEquiv e (φ.comp L) = A.transpose *ᵥ intDualCoordinatesOfEquiv e φ := by
  funext i
  rw [intDualCoordinatesOfEquiv_apply, LinearMap.comp_apply,
    intDualCoordinatesOfEquiv_evaluate e φ, hL, LinearEquiv.apply_symm_apply]
  simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  change (∑ j, intDualCoordinatesOfEquiv e φ j * A j i) =
    ∑ j, A j i * intDualCoordinatesOfEquiv e φ j
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end Wikipedia.HopfProblem.CuspCentralCohomology
