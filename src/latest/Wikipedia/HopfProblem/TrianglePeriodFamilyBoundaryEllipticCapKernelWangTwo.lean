import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangColumns
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitNorm

/-!
# The actual degree-three elliptic cap-kernel Wang map

The two original six-coordinate output columns are the invariant fibre
pair and `twist ∧ δ`.  The genuine covering shear remains in the second
column of the existing surface marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The original invariant fibre pair in the ordered six-minor marking. -/
def fibreInvariantPairVector (j : Kind) : Fin 6 → ℤ :=
  ![0, 0, 0, fibreSquareKernelVector j 0,
    fibreSquareKernelVector j 1, fibreSquareKernelVector j 2]

/-- The original `twist ∧ δ` vector, with the positive period-product order. -/
def twistDeltaVector (j : Kind) : Fin 6 → ℤ :=
  ![0, 0, j.twist 0, 0, j.twist 1, j.twist 2]

/-- The complete actual degree-three coefficient, retaining the genuine surface shear. -/
theorem h2Coordinates_formula (j : Kind) (a : SingularHomology (S j) 2) :
    h2Coordinates j a =
      ((fibreNormIndex j : ℤ) * surfaceH2Equiv j (specialLocalData j).centralPeriod a 0 -
          sourceShearTwo j * surfaceH2Equiv j (specialLocalData j).centralPeriod a 1) •
        fibreInvariantPairVector j +
      surfaceH2Equiv j (specialLocalData j).centralPeriod a 1 • twistDeltaVector j := by
  have h := h2Coordinates_cover_columns j a
  rw [originalAffineNorm_splitFibreClassTwo, originalAffineNorm_splitCircleClassTwo] at h
  ext i
  apply mul_left_cancel₀ (fibreNormIndex_int_ne_zero j)
  have hi := congrFun h i
  change (fibreNormIndex j : ℤ) * h2Coordinates j a i =
    ((fibreNormIndex j : ℤ) * surfaceH2Equiv j (specialLocalData j).centralPeriod a 0 -
      sourceShearTwo j * surfaceH2Equiv j (specialLocalData j).centralPeriod a 1) *
        ((fibreNormIndex j : ℤ) * fibreInvariantPairVector j i) +
      surfaceH2Equiv j (specialLocalData j).centralPeriod a 1 *
        ((fibreNormIndex j : ℤ) * twistDeltaVector j i) at hi
  change (fibreNormIndex j : ℤ) * h2Coordinates j a i =
    (fibreNormIndex j : ℤ) *
      (((fibreNormIndex j : ℤ) * surfaceH2Equiv j (specialLocalData j).centralPeriod a 0 -
          sourceShearTwo j * surfaceH2Equiv j (specialLocalData j).centralPeriod a 1) *
        fibreInvariantPairVector j i +
        surfaceH2Equiv j (specialLocalData j).centralPeriod a 1 * twistDeltaVector j i)
  rw [hi]
  ring

theorem h2Coordinates_first_axis (j : Kind) :
    h2Coordinates j ((surfaceH2Equiv j (specialLocalData j).centralPeriod).symm ![1, 0]) =
      (fibreNormIndex j : ℤ) • fibreInvariantPairVector j := by
  rw [h2Coordinates_formula, LinearEquiv.apply_symm_apply]
  simp

theorem h2Coordinates_second_axis (j : Kind) :
    h2Coordinates j ((surfaceH2Equiv j (specialLocalData j).centralPeriod).symm ![0, 1]) =
      twistDeltaVector j - sourceShearTwo j • fibreInvariantPairVector j := by
  rw [h2Coordinates_formula, LinearEquiv.apply_symm_apply]
  simp [sub_eq_add_neg, add_comm]

/-- The formula is for the original cap-kernel inverse and the actual Wang map. -/
theorem capKernel_wang_h2_coordinates (j : Kind) (a : SingularHomology (S j) 2) :
    FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) 2
          ((EllipticCapProduct.boundaryCapKernelEquiv j 2).symm a).val) =
      ((fibreNormIndex j : ℤ) * surfaceH2Equiv j (specialLocalData j).centralPeriod a 0 -
          sourceShearTwo j * surfaceH2Equiv j (specialLocalData j).centralPeriod a 1) •
        fibreInvariantPairVector j +
      surfaceH2Equiv j (specialLocalData j).centralPeriod a 1 • twistDeltaVector j :=
  h2Coordinates_formula j a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
