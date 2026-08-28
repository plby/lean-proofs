import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsExterior
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsTop
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsHomology
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsExact

/-!
# The integral single-monodromy quotient and its exact-kernel criterion

The actual exterior-square and exterior-cube quotients are free of ranks
four and two. The same holds for the actual singular-homology action of
the cusp matrix on the coordinate four-torus. Thus a surjective invariant
map to a finite free group of the corresponding rank has precisely the
monodromy-difference image as its kernel.

All invariance and surjectivity hypotheses remain explicit. This file
does not assert the existence or properties of a geometric specialization.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

open PeriodTorusHigherHomologyExterior PeriodTorusHigherHomology SingularMayerVietoris

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

/-- Invariance annihilates the range of the actual action minus identity. -/
theorem range_difference_le_ker_of_invariant (A : M →ₗ[ℤ] M) (f : M →ₗ[ℤ] N)
    (h : ∀ x, f (A x) = f x) :
    LinearMap.range (A - LinearMap.id) ≤ LinearMap.ker f := by
  rintro x ⟨y, rfl⟩
  change f (A y - y) = 0
  rw [map_sub, h, sub_self]

section EqualRank

variable [Module.Free ℤ N] [Module.Finite ℤ N]

/-- Exact relations for a surjection from the actual exterior square. -/
theorem exteriorSquare_kernel_eq (f : latticeExterior 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range exteriorSquareDifference ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 4) :
    LinearMap.ker f = LinearMap.range exteriorSquareDifference :=
  kernel_eq_of_quotient_equiv _ exteriorSquareCoinvariantEquiv f hf hS hrank

/-- Exact relations for a surjection from the actual exterior cube. -/
theorem exteriorCube_kernel_eq (f : latticeExterior 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range exteriorCubeDifference ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 2) :
    LinearMap.ker f = LinearMap.range exteriorCubeDifference :=
  kernel_eq_of_quotient_equiv _ exteriorCubeCoinvariantEquiv f hf hS hrank

theorem exteriorSquare_kernel_eq_of_invariant (f : latticeExterior 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv : ∀ x, f (exteriorPower.map 2 M₀.mulVecLin x) = f x)
    (hrank : Module.finrank ℤ N = 4) :
    LinearMap.ker f = LinearMap.range exteriorSquareDifference :=
  exteriorSquare_kernel_eq f hf
    (range_difference_le_ker_of_invariant _ f hinv) hrank

theorem exteriorCube_kernel_eq_of_invariant (f : latticeExterior 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv : ∀ x, f (exteriorPower.map 3 M₀.mulVecLin x) = f x)
    (hrank : Module.finrank ℤ N = 2) :
    LinearMap.ker f = LinearMap.range exteriorCubeDifference :=
  exteriorCube_kernel_eq f hf
    (range_difference_le_ker_of_invariant _ f hinv) hrank

/-- Exact degree-two relations for an actual torus-homology surjection. -/
theorem torusTwo_kernel_eq (f : SingularHomology (ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range (torusDifference 2) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 4) :
    LinearMap.ker f = LinearMap.range (torusDifference 2) :=
  kernel_eq_of_quotient_equiv _ torusTwoCoinvariantEquiv f hf hS hrank

/-- Exact degree-three relations for an actual torus-homology surjection. -/
theorem torusThree_kernel_eq (f : SingularHomology (ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range (torusDifference 3) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 2) :
    LinearMap.ker f = LinearMap.range (torusDifference 3) :=
  kernel_eq_of_quotient_equiv _ torusThreeCoinvariantEquiv f hf hS hrank

theorem torusTwo_kernel_eq_of_invariant
    (f : SingularHomology (ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv : ∀ x, f (singularHomologyMap (torusMatrixMap M₀) 2 x) = f x)
    (hrank : Module.finrank ℤ N = 4) :
    LinearMap.ker f = LinearMap.range (torusDifference 2) :=
  torusTwo_kernel_eq f hf (range_difference_le_ker_of_invariant _ f hinv) hrank

theorem torusThree_kernel_eq_of_invariant
    (f : SingularHomology (ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv : ∀ x, f (singularHomologyMap (torusMatrixMap M₀) 3 x) = f x)
    (hrank : Module.finrank ℤ N = 2) :
    LinearMap.ker f = LinearMap.range (torusDifference 3) :=
  torusThree_kernel_eq f hf (range_difference_le_ker_of_invariant _ f hinv) hrank

/-- The actual degree-two quotient map induced by the specified surjection. -/
def torusTwoDescendedEquiv (f : SingularHomology (ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range (torusDifference 2) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 4) : TorusCoinvariants 2 ≃ₗ[ℤ] N :=
  quotientLiftEquiv _ torusTwoCoinvariantEquiv f hf hS hrank

/-- The actual degree-three quotient map induced by the specified surjection. -/
def torusThreeDescendedEquiv (f : SingularHomology (ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range (torusDifference 3) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 2) : TorusCoinvariants 3 ≃ₗ[ℤ] N :=
  quotientLiftEquiv _ torusThreeCoinvariantEquiv f hf hS hrank

@[simp] theorem torusTwoDescendedEquiv_mk
    (f : SingularHomology (ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range (torusDifference 2) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 4) (x : SingularHomology (ProductTorus 4) 2) :
    torusTwoDescendedEquiv f hf hS hrank (Submodule.Quotient.mk x) = f x := rfl

@[simp] theorem torusThreeDescendedEquiv_mk
    (f : SingularHomology (ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hS : LinearMap.range (torusDifference 3) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 2) (x : SingularHomology (ProductTorus 4) 3) :
    torusThreeDescendedEquiv f hf hS hrank (Submodule.Quotient.mk x) = f x := rfl

end EqualRank

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants
