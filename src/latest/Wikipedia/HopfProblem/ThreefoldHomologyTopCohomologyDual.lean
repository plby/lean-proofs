import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Evaluation-dual coordinates for an actual infinite cyclic module

The equivalence is precomposition with the inverse of the original
integer marking, followed by evaluation at one. Its evaluation formula
keeps the original marking abstract, so applying it to the geometric
top-homology equivalence does not expand the underlying constructions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- The integer dual marking induced by an actual cyclic-module marking. -/
def cyclicDualEquiv (e : M ≃ₗ[ℤ] ℤ) : (M →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ :=
  e.symm.dualMap.trans (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ)

@[simp] theorem cyclicDualEquiv_apply (e : M ≃ₗ[ℤ] ℤ) (φ : M →ₗ[ℤ] ℤ) :
    cyclicDualEquiv e φ = φ (e.symm 1) := rfl

end Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyAlgebra
