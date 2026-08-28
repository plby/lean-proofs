import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopTransfer
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopSource
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopSplit
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangAlgebra
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopLattice

/-!
# The genuine degree-four cap-kernel Wang columns

The actual two covering classes have known original third-exterior
coordinates.  Their finite norms, together with the exact covering index,
determine the whole cap-kernel Wang map in the unchanged surface marking.
The order-four twist sign and the actual covering shear are retained.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The actual positive fibre top class has the full finite-order norm. -/
theorem originalAffineNorm_splitFibreClassThree (j : Kind) :
    FlatTorus.singularH3Coordinates (originalAffineNorm j 3 (splitFibreClassThree j)) =
      (j.order : ℤ) • ![0, 0, 0, 1] := by
  rw [originalAffineNorm_h3_coordinates, splitFibreClassThree_coordinates]
  cases j
  · rw [originalNormMatrixThree_three]
    decide
  · rw [originalNormMatrixThree_four]
    decide

/-- The original split-circle norm has its genuine signed horizontal vector. -/
theorem originalAffineNorm_splitCircleClassThree (j : Kind) :
    FlatTorus.singularH3Coordinates (originalAffineNorm j 3 (splitCircleClassThree j)) =
      match j with
      | .three => ![3, -1, 2, 0]
      | .four => ![-4, 2, -2, 0] := by
  rw [originalAffineNorm_h3_coordinates, splitCircleClassThree_coordinates]
  cases j
  · rw [originalNormMatrixThree_three]
    decide
  · rw [originalNormMatrixThree_four]
    decide

/-- The exact finite-cover column identity for the actual degree-four Wang map. -/
theorem h3Coordinates_cover_columns (j : Kind) (a : SingularHomology (S j) 3) :
    (fibreNormIndex j : ℤ) • h3Coordinates j a =
      ((fibreNormIndex j : ℤ) * surfaceH3Equiv j (specialLocalData j).centralPeriod a 0 -
          sourceShearThree j * surfaceH3Equiv j (specialLocalData j).centralPeriod a 1) •
        FlatTorus.singularH3Coordinates (originalAffineNorm j 3 (splitFibreClassThree j)) +
      surfaceH3Equiv j (specialLocalData j).centralPeriod a 1 •
        FlatTorus.singularH3Coordinates (originalAffineNorm j 3 (splitCircleClassThree j)) := by
  have h := map_cover_columns (surfaceH3Equiv j (specialLocalData j).centralPeriod)
    (h3Coordinates j)
    (singularHomologyMap (surfaceCover j) 3 (splitFibreClassThree j))
    (singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) a
    (sourceShearThree j) (fibreNormIndex j : ℤ)
    (surfaceCover_splitFibreClassThree j) (surfaceCover_splitCircleClassThree j)
  simpa only [h3Coordinates_surfaceCover] using h

/-- The exact four original coordinates for the order-three cap-kernel Wang map. -/
theorem h3Coordinates_three (a : SingularHomology (S .three) 3) :
    h3Coordinates .three a =
      ![3 * surfaceH3Equiv .three (specialLocalData .three).centralPeriod a 1,
        -surfaceH3Equiv .three (specialLocalData .three).centralPeriod a 1,
        2 * surfaceH3Equiv .three (specialLocalData .three).centralPeriod a 1,
        3 * surfaceH3Equiv .three (specialLocalData .three).centralPeriod a 0 -
          3 * sourceShearThree .three *
            surfaceH3Equiv .three (specialLocalData .three).centralPeriod a 1] := by
  have h := h3Coordinates_cover_columns .three a
  rw [originalAffineNorm_splitFibreClassThree, originalAffineNorm_splitCircleClassThree] at h
  simp only [fibreNormIndex_three, Nat.cast_one, one_smul, one_mul] at h
  rw [h]
  ext i
  fin_cases i <;> simp [Kind.order] <;> ring

/-- The exact four original coordinates for the order-four cap-kernel Wang map.
The factor two is cancelled integrally, without dividing a chosen class. -/
theorem h3Coordinates_four (a : SingularHomology (S .four) 3) :
    h3Coordinates .four a =
      ![-2 * surfaceH3Equiv .four (specialLocalData .four).centralPeriod a 1,
        surfaceH3Equiv .four (specialLocalData .four).centralPeriod a 1,
        -surfaceH3Equiv .four (specialLocalData .four).centralPeriod a 1,
        4 * surfaceH3Equiv .four (specialLocalData .four).centralPeriod a 0 -
          2 * sourceShearThree .four *
            surfaceH3Equiv .four (specialLocalData .four).centralPeriod a 1] := by
  have h := h3Coordinates_cover_columns .four a
  rw [originalAffineNorm_splitFibreClassThree, originalAffineNorm_splitCircleClassThree] at h
  ext i
  have hi := congrFun h i
  fin_cases i
  all_goals
    simp [fibreNormIndex_four, Kind.order] at hi ⊢
    linarith only [hi]

/-- The actual map is the two-column integer matrix in the original unchanged markings. -/
theorem h3Coordinates_formula (j : Kind) (a : SingularHomology (S j) 3) :
    h3Coordinates j a = topWangMatrix j (sourceShearThree j) *ᵥ
      surfaceH3Equiv j (specialLocalData j).centralPeriod a := by
  cases j
  · rw [h3Coordinates_three, topWangMatrix_mulVec_three]
  · rw [h3Coordinates_four, topWangMatrix_mulVec_four]

/-- Equality of the genuine degree-four cap-kernel coefficient as an integral linear map. -/
theorem h3Coordinates_conjugate (j : Kind) :
    (h3Coordinates j).comp
      (surfaceH3Equiv j (specialLocalData j).centralPeriod).symm.toLinearMap =
        (topWangMatrix j (sourceShearThree j)).mulVecLin := by
  apply LinearMap.ext
  intro a
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Matrix.mulVecLin_apply] using
    h3Coordinates_formula j ((surfaceH3Equiv j (specialLocalData j).centralPeriod).symm a)

/-- The formula applies to the literal inverse of the actual filling-cap kernel equivalence. -/
theorem capKernel_wang_h3_coordinates (j : Kind) (a : SingularHomology (S j) 3) :
    FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) 3
          ((EllipticCapProduct.boundaryCapKernelEquiv j 3).symm a).val) =
      topWangMatrix j (sourceShearThree j) *ᵥ
        surfaceH3Equiv j (specialLocalData j).centralPeriod a :=
  h3Coordinates_formula j a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
