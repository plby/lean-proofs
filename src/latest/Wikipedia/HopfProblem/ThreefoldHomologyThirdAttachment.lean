import Wikipedia.HopfProblem.ThreefoldHomologyThirdResidualCriteria
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelation

/-!
# The original third attachment is an integral isomorphism

The actual finite covers, shears, and full cusp involution evaluate the
complete original positive reference relation as the primitive positive
third-fibre class.  Its genuine residual coefficient is therefore one.
The exact native kernel and cokernel calculations now prove bijectivity
of both the actual native relation and the original signed star map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris CapElimination

/-- The actual full geometric reference relation has its original positive unit coefficient. -/
theorem referenceFibreCoefficient_eq_one : referenceFibreCoefficient = 1 :=
  (referenceFibreCoefficient_eq_iff 1).mpr
    TrianglePeriodFamily.Boundary.ThirdRelation.referenceClasses_regular

/-- Primitivity comes from the actual full attachment calculation. -/
theorem referenceFibreCoefficient_isUnit : IsUnit referenceFibreCoefficient := by
  rw [referenceFibreCoefficient_eq_one]
  exact isUnit_one

/-- The full original native cap-kernel regular relation is an integral isomorphism. -/
theorem nativeCapKernelRegularMap_three_bijective :
    Function.Bijective (nativeCapKernelRegularMap 3) :=
  nativeCapKernelRegularMap_three_bijective_iff.mpr referenceFibreCoefficient_isUnit

theorem nativeCapKernelRegularMap_three_injective :
    Function.Injective (nativeCapKernelRegularMap 3) :=
  nativeCapKernelRegularMap_three_bijective.injective

theorem nativeCapKernelRegularMap_three_surjective :
    Function.Surjective (nativeCapKernelRegularMap 3) :=
  nativeCapKernelRegularMap_three_bijective.surjective

/-- The bundled equivalence has the original actual regular relation as its forward map. -/
def nativeThirdRegularEquiv :
    (∀ i : Puncture, NativeCapKernel i 3) ≃ₗ[ℤ] SingularHomology SpecialRegularFamily 3 :=
  LinearEquiv.ofBijective (nativeCapKernelRegularMap 3)
    nativeCapKernelRegularMap_three_bijective

@[simp] theorem nativeThirdRegularEquiv_toLinearMap :
    nativeThirdRegularEquiv.toLinearMap = nativeCapKernelRegularMap 3 := rfl

/-- Bijectivity of the literal original signed third attachment map. -/
theorem starLeft_three_bijective : Function.Bijective (starLeftHomologyMap 3) :=
  starLeft_three_bijective_iff.mpr referenceFibreCoefficient_isUnit

theorem starLeft_three_injective : Function.Injective (starLeftHomologyMap 3) :=
  starLeft_three_bijective.injective

theorem starLeft_three_surjective : Function.Surjective (starLeftHomologyMap 3) :=
  starLeft_three_bijective.surjective

/-- The original signed star map, bundled without altering either coefficient or sign. -/
def starLeftThirdEquiv : StarOverlapHomology 3 ≃ₗ[ℤ] StarPairHomology 3 :=
  LinearEquiv.ofBijective (starLeftHomologyMap 3) starLeft_three_bijective

@[simp] theorem starLeftThirdEquiv_toLinearMap :
    starLeftThirdEquiv.toLinearMap = starLeftHomologyMap 3 := rfl

@[simp] theorem starLeftThirdEquiv_apply (a : StarOverlapHomology 3) :
    starLeftThirdEquiv a = starLeftHomologyMap 3 a := rfl

theorem starLeft_three_kernel_eq_bot : LinearMap.ker (starLeftHomologyMap 3) = ⊥ :=
  LinearMap.ker_eq_bot.mpr starLeft_three_injective

theorem starLeft_three_range_eq_top : LinearMap.range (starLeftHomologyMap 3) = ⊤ :=
  LinearMap.range_eq_top.mpr starLeft_three_surjective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree
