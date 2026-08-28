import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopSourceBasic
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSource

/-!
# Genuine degree-three surface-cover columns in the original marking

The positive top fibre class maps to the primitive first surface axis.
The positive split-circle cross product has the actual norm index as its
second coordinate.  Its first coordinate is retained as the actual shear
of the existing surface marking; no value or divisibility of that shear
is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling MappingTorusHomology

/-- The original third-homology covering shear in the unchanged surface marking. -/
def sourceShearThree (j : Kind) : ℤ :=
  surfaceH3Equiv j (specialLocalData j).centralPeriod
    (singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) 0

/-- The actual positive top fibre input gives the primitive first surface coordinate. -/
theorem surfaceCover_splitFibreClassThree (j : Kind) :
    surfaceH3Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 3 (splitFibreClassThree j)) = ![1, 0] := by
  change mappingTorusH3Equiv j
    (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod 3
      (singularHomologyMap (surfaceCover j) 3 (splitFibreClassThree j))) = _
  rw [splitFibreClassThree, surfaceCover_split_section, mappingTorusH3Equiv_fibre,
    splitFibreInputThree_coordinates]

/-- The actual Wang connecting coordinate of the positive-circle class is
the proved second-homology norm index, with its positive sign. -/
theorem surfaceCover_splitCircleClassThree_second (j : Kind) :
    surfaceH3Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) 1 =
      fibreNormIndex j := by
  change mappingTorusH3Equiv j
    (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod 3
      (singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j))) 1 = _
  rw [mappingTorusH3Equiv_boundary, splitCircleClassThree, surfaceCover_split_cross_wang]
  change fibreHomologyNormTwoCoordinate j splitFibreInputTwo = _
  rw [fibreHomologyNormTwoCoordinate_apply, splitFibreInputTwo,
    LinearEquiv.apply_symm_apply]
  simp only [Matrix.cons_val_zero, mul_one]

/-- The complete original covering column, retaining its actual first coordinate. -/
theorem surfaceCover_splitCircleClassThree (j : Kind) :
    surfaceH3Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) =
      ![sourceShearThree j, (fibreNormIndex j : ℤ)] := by
  ext i
  fin_cases i
  · rfl
  · exact surfaceCover_splitCircleClassThree_second j

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
