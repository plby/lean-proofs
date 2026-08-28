import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationHorizontal
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationCuspBoundary
import Wikipedia.HopfProblem.CuspNegation

/-!
# The complete actual third-degree attaching relation

The original cap-kernel reference tuple has all three positive entries.
Its entire regular-family image is the original positive `γ,u,w` fibre
class. The proof combines the actual elliptic finite covers and vertical
shears with fibre negation on the genuine full cusp cap. The horizontal
remainder vanishes by the actual source exact sequence and the genuine
negation action, not by an assigned residual coordinate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus Homology
open SpecialPeriods.Threefold.Homology.CapElimination
open SpecialPeriods.Threefold.Homology.ThirdDegree

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual full-cap involution fixes the original cusp cap-kernel contribution. -/
theorem referenceClasses_cusp_regular_negation :
    singularHomologyMap (familyNegation Dsp) 3
        (boundaryRegularHomologyMap none 3 (referenceClasses none).val) =
      boundaryRegularHomologyMap none 3 (referenceClasses none).val :=
  cuspNegation_capKernel_regular_fixed CuspNegation.boundaryNeg
    CuspNegation.boundaryNeg_mk CuspNegation.specialCapMap CuspNegation.boundaryToFilling_neg
    (referenceClasses none)

/-- The complete genuine regular relation is the primitive positive original fibre generator. -/
theorem referenceClasses_regular :
    nativeCapKernelRegularMap 3 referenceClasses = thirdFibreCyclicMap 1 :=
  referenceClasses_regular_of_cusp_negation referenceClasses_cusp_regular_negation

/-- The same equality uses the literal original fibre inclusion and ordered exterior-cube mark. -/
theorem referenceClasses_regular_fibre :
    nativeCapKernelRegularMap 3 referenceClasses =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3
        (FlatTorus.singularH3Coordinates.symm ![1, 0, 0, 0]) := by
  rw [referenceClasses_regular, thirdFibreCyclicMap_apply]

/-- Expanded into the three original positive attachment coefficients. -/
theorem referenceClasses_regular_sum :
    boundaryRegularHomologyMap none 3 (referenceClasses none).val +
        boundaryRegularHomologyMap (some .three) 3 (referenceClasses (some .three)).val +
        boundaryRegularHomologyMap (some .four) 3 (referenceClasses (some .four)).val =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3
        (FlatTorus.singularH3Coordinates.symm ![1, 0, 0, 0]) := by
  classical
  rw [← referenceClasses_regular_fibre, nativeCapKernelRegularMap_apply, Fintype.sum_option]
  have hu : (Finset.univ : Finset Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Kind.three ≠ .four)]
  abel

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
