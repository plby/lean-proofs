import Wikipedia.HopfProblem.Lattice
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraReduction
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degree-zero and determinant-lattice difference operators

The degree-zero lattice operators are identities. The top determinant
operators are also identities, because both actual lattice monodromy
matrices have determinant one. Their two-input difference operators
therefore vanish, with literal kernels `ℤ × ℤ` and cokernels `ℤ`.

These are integral lattice calculations. No identification with actual
top-degree singular homology is asserted in this file.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

open TrianglePeriodFamilyHomologyAlgebra

/-- The first actual lattice monodromy preserves the determinant lattice. -/
@[simp] theorem det_A₁ : A₁.det = 1 := by
  rw [A₁_eq_transpose_sq, Matrix.det_transpose, Matrix.det_pow, det_T₁, one_pow]

/-- The second actual lattice monodromy preserves the determinant lattice. -/
@[simp] theorem det_A₂ : A₂.det = 1 := by
  rw [A₂_eq_transpose_cube, Matrix.det_transpose, Matrix.det_pow, det_T₂, one_pow]

/-- The literal difference operator on the degree-zero integral lattice. -/
def deltaZero : (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  delta (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

@[simp] theorem deltaZero_eq_zero : deltaZero = 0 := by
  apply LinearMap.ext
  intro x
  simp [deltaZero, delta_apply]

/-- The literal difference operator on the fourth determinant lattice,
using the determinants of the actual `A₁` and `A₂` matrices. -/
def deltaFour : (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  delta (A₁.det • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
    (A₂.det • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

@[simp] theorem deltaFour_eq_zero : deltaFour = 0 := by
  rw [deltaFour, det_A₁, det_A₂, one_smul]
  exact deltaZero_eq_zero

/-- The degree-zero kernel is the full two-coordinate integral module. -/
def kernelZeroEquiv : LinearMap.ker deltaZero ≃ₗ[ℤ] (ℤ × ℤ) :=
  ({ toFun x := x.val
     invFun x := ⟨x, by simp⟩
     left_inv _ := Subtype.ext rfl
     right_inv _ := rfl
     map_add' _ _ := rfl
   } : LinearMap.ker deltaZero ≃+ (ℤ × ℤ)).toIntLinearEquiv

@[simp] theorem kernelZeroEquiv_apply (x : LinearMap.ker deltaZero) :
    kernelZeroEquiv x = x.val := rfl

@[simp] theorem kernelZeroEquiv_symm_apply_val (x : ℤ × ℤ) :
    (kernelZeroEquiv.symm x : ℤ × ℤ) = x := rfl

/-- The determinant-lattice kernel is the full two-coordinate integral module. -/
def kernelFourEquiv : LinearMap.ker deltaFour ≃ₗ[ℤ] (ℤ × ℤ) :=
  ({ toFun x := x.val
     invFun x := ⟨x, by simp⟩
     left_inv _ := Subtype.ext rfl
     right_inv _ := rfl
     map_add' _ _ := rfl
   } : LinearMap.ker deltaFour ≃+ (ℤ × ℤ)).toIntLinearEquiv

@[simp] theorem kernelFourEquiv_apply (x : LinearMap.ker deltaFour) :
    kernelFourEquiv x = x.val := rfl

@[simp] theorem kernelFourEquiv_symm_apply_val (x : ℤ × ℤ) :
    (kernelFourEquiv.symm x : ℤ × ℤ) = x := rfl

/-- The actual degree-zero quotient cokernel, with the unchanged integer coordinate. -/
def cokernelZeroEquiv : (ℤ ⧸ LinearMap.range deltaZero) ≃ₗ[ℤ] ℤ :=
  ((LinearMap.range deltaZero).quotEquivOfEqBot (by simp)).toAddEquiv.toIntLinearEquiv

@[simp] theorem cokernelZeroEquiv_mk (z : ℤ) :
    cokernelZeroEquiv (Submodule.Quotient.mk z) = z := rfl

@[simp] theorem cokernelZeroEquiv_symm_apply (z : ℤ) :
    cokernelZeroEquiv.symm z = Submodule.Quotient.mk z := rfl

/-- The actual determinant-lattice quotient cokernel, with the unchanged integer coordinate. -/
def cokernelFourEquiv : (ℤ ⧸ LinearMap.range deltaFour) ≃ₗ[ℤ] ℤ :=
  ((LinearMap.range deltaFour).quotEquivOfEqBot (by simp)).toAddEquiv.toIntLinearEquiv

@[simp] theorem cokernelFourEquiv_mk (z : ℤ) :
    cokernelFourEquiv (Submodule.Quotient.mk z) = z := rfl

@[simp] theorem cokernelFourEquiv_symm_apply (z : ℤ) :
    cokernelFourEquiv.symm z = Submodule.Quotient.mk z := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice
