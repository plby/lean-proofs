import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSourceBasic
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitClasses

/-!
# Genuine surface-cover columns in the existing surface markings

The first columns are primitive fibre classes.  The second columns are
the original positive circle cross products, with their actual covering
indices.  Their first coordinates are retained, since the existing
surface markings choose a splitting of the Wang extension.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling MappingTorusHomology

/-- The original first-homology covering shear in the existing surface marking. -/
def sourceShearOne (j : Kind) : ℤ :=
  surfaceH1Equiv j (specialLocalData j).centralPeriod
    (singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) 0

/-- The original second-homology covering shear in the existing surface marking. -/
def sourceShearTwo (j : Kind) : ℤ :=
  surfaceH2Equiv j (specialLocalData j).centralPeriod
    (singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) 0

theorem surfaceCover_splitFibreClassOne (j : Kind) :
    surfaceH1Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j)) = ![1, 0] := by
  change mappingTorusH1Equiv j
    (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod 1
      (singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j))) = _
  rw [splitFibreClassOne, surfaceCover_split_section, mappingTorusH1Equiv_fibre,
    splitFibreInputOne, LinearEquiv.apply_symm_apply, fibreCoinvariantCoordinate_section]

theorem surfaceCover_splitCircleClassOne_second (j : Kind) :
    surfaceH1Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) 1 = j.order := by
  change mappingTorusH1Equiv j
    (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod 1
      (singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j))) 1 = _
  rw [mappingTorusH1Equiv_boundary, splitCircleClassOne, surfaceCover_split_cross_wang,
    fibreHomologyNorm_zero, torusH0Coordinates_pointClass, mul_one]

theorem surfaceCover_splitCircleClassOne (j : Kind) :
    surfaceH1Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) =
      ![sourceShearOne j, (j.order : ℤ)] := by
  ext i
  fin_cases i
  · rfl
  · exact surfaceCover_splitCircleClassOne_second j

theorem surfaceCover_splitFibreClassTwo (j : Kind) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 2 (splitFibreClassTwo j)) = ![1, 0] := by
  change mappingTorusH2Equiv j
    (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod 2
      (singularHomologyMap (surfaceCover j) 2 (splitFibreClassTwo j))) = _
  rw [splitFibreClassTwo, surfaceCover_split_section, mappingTorusH2Equiv_fibre,
    splitFibreInputTwo, LinearEquiv.apply_symm_apply]
  rfl

theorem surfaceCover_splitCircleClassTwo_second (j : Kind) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) 1 =
      fibreNormIndex j := by
  change mappingTorusH2Equiv j
    (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod 2
      (singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j))) 1 = _
  rw [mappingTorusH2Equiv_boundary, splitCircleClassTwo, surfaceCover_split_cross_wang]
  change fibreHomologyNormOneCoordinate j splitFibreInputOne = _
  rw [fibreHomologyNormOneCoordinate_apply, splitFibreInputOne,
    LinearEquiv.apply_symm_apply, fibreCoinvariantCoordinate_section, mul_one]

theorem surfaceCover_splitCircleClassTwo (j : Kind) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) =
      ![sourceShearTwo j, (fibreNormIndex j : ℤ)] := by
  ext i
  fin_cases i
  · rfl
  · exact surfaceCover_splitCircleClassTwo_second j

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
