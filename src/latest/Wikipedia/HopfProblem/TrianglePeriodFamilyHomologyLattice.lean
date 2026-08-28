import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeOdd
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeTwo
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeEven
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeRankAlgebra

/-!
# Finite free integral kernels of the actual monodromy-difference maps

The exact integral image computations give infinite-cyclic quotient
cokernels. Integral rank-nullity and freeness of submodules over the
integers therefore give kernel ranks five, seven, and five. The final
equivalences concern the actual kernels of the literal lattice matrices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

/-- The actual degree-one difference kernel is finitely generated over the integers. -/
theorem kernelOne_finite : Module.Finite ℤ (LinearMap.ker deltaOne) :=
  kernel_finite_of_finite deltaOne

/-- The actual degree-two difference kernel is finitely generated over the integers. -/
theorem kernelTwo_finite : Module.Finite ℤ (LinearMap.ker deltaTwo) :=
  kernel_finite_of_finite deltaTwo

/-- The actual degree-three difference kernel is finitely generated over the integers. -/
theorem kernelThree_finite : Module.Finite ℤ (LinearMap.ker deltaThree) :=
  kernel_finite_of_finite deltaThree

/-- The actual degree-one difference kernel is free over the integers. -/
theorem kernelOne_free : Module.Free ℤ (LinearMap.ker deltaOne) :=
  kernel_free_of_finite_free deltaOne

/-- The actual degree-two difference kernel is free over the integers. -/
theorem kernelTwo_free : Module.Free ℤ (LinearMap.ker deltaTwo) :=
  kernel_free_of_finite_free deltaTwo

/-- The actual degree-three difference kernel is free over the integers. -/
theorem kernelThree_free : Module.Free ℤ (LinearMap.ker deltaThree) :=
  kernel_free_of_finite_free deltaThree

/-- The integral kernel rank in degree one is five. -/
theorem kernelOne_finrank : Module.finrank ℤ (LinearMap.ker deltaOne) = 5 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaOne cokernelOneEquiv
  norm_num [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

/-- The integral kernel rank in degree two is seven. -/
theorem kernelTwo_finrank : Module.finrank ℤ (LinearMap.ker deltaTwo) = 7 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaTwo cokernelTwoEquiv
  norm_num [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

/-- The integral kernel rank in degree three is five. -/
theorem kernelThree_finrank : Module.finrank ℤ (LinearMap.ker deltaThree) = 5 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaThree cokernelThreeEquiv
  norm_num [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

/-- The actual degree-one integral kernel is a rank-five free lattice. -/
def kernelOneEquiv : LinearMap.ker deltaOne ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  kernelEquivOfFinrankEq deltaOne 5 kernelOne_finrank

/-- The actual degree-two integral kernel is a rank-seven free lattice. -/
def kernelTwoEquiv : LinearMap.ker deltaTwo ≃ₗ[ℤ] (Fin 7 → ℤ) :=
  kernelEquivOfFinrankEq deltaTwo 7 kernelTwo_finrank

/-- The actual degree-three integral kernel is a rank-five free lattice. -/
def kernelThreeEquiv : LinearMap.ker deltaThree ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  kernelEquivOfFinrankEq deltaThree 5 kernelThree_finrank

/-- The degree-zero difference kernel is finite over the integers. -/
theorem kernelZero_finite : Module.Finite ℤ (LinearMap.ker deltaZero) :=
  kernel_finite_of_finite deltaZero

/-- The degree-zero difference kernel is free over the integers. -/
theorem kernelZero_free : Module.Free ℤ (LinearMap.ker deltaZero) :=
  kernel_free_of_finite_free deltaZero

/-- The degree-zero difference kernel has integral rank two. -/
theorem kernelZero_finrank : Module.finrank ℤ (LinearMap.ker deltaZero) = 2 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaZero cokernelZeroEquiv
  norm_num [Module.finrank_prod] at h
  omega

/-- The determinant-lattice difference kernel is finite over the integers. -/
theorem kernelFour_finite : Module.Finite ℤ (LinearMap.ker deltaFour) :=
  kernel_finite_of_finite deltaFour

/-- The determinant-lattice difference kernel is free over the integers. -/
theorem kernelFour_free : Module.Free ℤ (LinearMap.ker deltaFour) :=
  kernel_free_of_finite_free deltaFour

/-- The determinant-lattice difference kernel has integral rank two. -/
theorem kernelFour_finrank : Module.finrank ℤ (LinearMap.ker deltaFour) = 2 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaFour cokernelFourEquiv
  norm_num [Module.finrank_prod] at h
  omega

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice
