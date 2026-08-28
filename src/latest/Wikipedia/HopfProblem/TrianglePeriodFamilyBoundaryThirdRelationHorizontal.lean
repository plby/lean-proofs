import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationElliptic
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationDetection
import Wikipedia.HopfProblem.ThreefoldHomologyThirdFibre

/-!
# Detection of the remaining original horizontal third-degree term

The actual finite-cover calculations give the entire elliptic terms,
including their fibre corrections. The original source relation leaves
the sum of the horizontal terms in the genuine fibre image. Fibre
negation then detects this remainder, once the original cusp class is
proved invariant through its actual cap extension.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus Homology
open SpecialPeriods.Threefold.Homology.CapElimination
open SpecialPeriods.Threefold.Homology.ThirdDegree

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The genuine common regular fibre agrees with the original primitive cyclic inclusion. -/
theorem regularGammaUW_eq_thirdFibreCyclicMap : regularGammaUW = thirdFibreCyclicMap 1 := by
  rw [thirdFibreCyclicMap_apply]
  rfl

theorem regularGammaUW_source_eq_zero : sourceKernelProjection Dsp 2 regularGammaUW = 0 := by
  rw [regularGammaUW_eq_thirdFibreCyclicMap]
  exact thirdFibreCyclicMap_source_eq_zero 1

/-- The actual original cusp contribution and the two unchanged elliptic horizontal classes. -/
def horizontalRemainder : SingularHomology (Dsp).Space 3 :=
  boundaryRegularHomologyMap none 3 (referenceClasses none).val +
    ellipticHorizontal .three + ellipticHorizontal .four

/-- The full original positive tuple has exactly the proved fibre correction `4 - 3 = 1`. -/
theorem referenceClasses_regular_split :
    nativeCapKernelRegularMap 3 referenceClasses = horizontalRemainder + regularGammaUW := by
  classical
  rw [nativeCapKernelRegularMap_apply, Fintype.sum_option]
  have hu : (Finset.univ : Finset Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Kind.three ≠ .four),
    referenceClasses_three_regular, referenceClasses_four_regular]
  unfold horizontalRemainder
  abel

/-- The actual source maps vanish on the horizontal remainder. -/
theorem horizontalRemainder_source_eq_zero :
    sourceKernelProjection Dsp 2 horizontalRemainder = 0 := by
  have h := referenceClasses_source_eq_zero
  change sourceKernelProjection Dsp 2
    (nativeCapKernelRegularMap 3 referenceClasses) = 0 at h
  rw [referenceClasses_regular_split, map_add, regularGammaUW_source_eq_zero, add_zero] at h
  exact h

/-- Fixing the original cusp image fixes the complete horizontal remainder. -/
theorem horizontalRemainder_negation
    (hC : singularHomologyMap (familyNegation Dsp) 3
      (boundaryRegularHomologyMap none 3 (referenceClasses none).val) =
        boundaryRegularHomologyMap none 3 (referenceClasses none).val) :
    singularHomologyMap (familyNegation Dsp) 3 horizontalRemainder = horizontalRemainder := by
  unfold horizontalRemainder
  rw [map_add, map_add, hC, ellipticHorizontal_negation, ellipticHorizontal_negation]

/-- Actual negation and actual source exactness determine the complete regular relation. -/
theorem referenceClasses_regular_of_cusp_negation
    (hC : singularHomologyMap (familyNegation Dsp) 3
      (boundaryRegularHomologyMap none 3 (referenceClasses none).val) =
        boundaryRegularHomologyMap none 3 (referenceClasses none).val) :
    nativeCapKernelRegularMap 3 referenceClasses = thirdFibreCyclicMap 1 := by
  have hzero : horizontalRemainder = 0 :=
    negation_fixed_source_zero Dsp horizontalRemainder
      (horizontalRemainder_negation hC) horizontalRemainder_source_eq_zero
  rw [referenceClasses_regular_split, hzero, zero_add, regularGammaUW_eq_thirdFibreCyclicMap]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
