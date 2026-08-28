import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExact
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Integral kernel ranks from an infinite-cyclic cokernel

Submodules of finite free integral modules are finite and free. Integral
rank-nullity then computes the kernel rank when the actual quotient
cokernel has been identified with the integers. These statements do not
replace integral image calculations by rational ones.
-/

noncomputable section

universe u

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  [Module ℤ M] [Module ℤ N]

/-- Every kernel in a finite integral module is finitely generated. -/
theorem kernel_finite_of_finite [Module.Finite ℤ M] (f : M →ₗ[ℤ] N) :
    Module.Finite ℤ (LinearMap.ker f) := inferInstance

/-- Every kernel in a finite free integral module is free over the integers. -/
theorem kernel_free_of_finite_free [Module.Finite ℤ M] [Module.Free ℤ M]
    (f : M →ₗ[ℤ] N) : Module.Free ℤ (LinearMap.ker f) := by
  let := kernel_finite_of_finite f
  infer_instance

/-- Integral rank-nullity for a map with an actual infinite-cyclic quotient cokernel. -/
theorem kernel_finrank_add_of_cokernelEquiv [Module.Finite ℤ M] [Module.Finite ℤ N]
    (f : M →ₗ[ℤ] N) (e : (N ⧸ LinearMap.range f) ≃ₗ[ℤ] ℤ) :
    Module.finrank ℤ (LinearMap.ker f) + Module.finrank ℤ N =
      Module.finrank ℤ M + 1 := by
  have hsource := (LinearMap.ker f).finrank_quotient_add_finrank
  have htarget := (LinearMap.range f).finrank_quotient_add_finrank
  have hquot : Module.finrank ℤ (M ⧸ LinearMap.ker f) =
      Module.finrank ℤ (LinearMap.range f) := f.quotKerEquivRange.finrank_eq
  have hcoker : Module.finrank ℤ (N ⧸ LinearMap.range f) = 1 := by
    rw [e.finrank_eq]
    simp
  omega

/-- An actual kernel of a finite free integral module, once its integral
rank is proved, is linearly equivalent to the corresponding finite lattice. -/
def kernelEquivOfFinrankEq [Module.Finite ℤ M] [Module.Free ℤ M]
    (f : M →ₗ[ℤ] N) (r : ℕ) (hr : Module.finrank ℤ (LinearMap.ker f) = r) :
    LinearMap.ker f ≃ₗ[ℤ] (Fin r → ℤ) := by
  let := kernel_finite_of_finite f
  let := kernel_free_of_finite_free f
  apply LinearEquiv.ofFinrankEq
  simpa using hr

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice
