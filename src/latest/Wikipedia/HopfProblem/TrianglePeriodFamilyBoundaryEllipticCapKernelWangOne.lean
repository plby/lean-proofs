import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangColumns
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitNorm

/-!
# The actual degree-two elliptic cap-kernel Wang map

The primitive fibre column has its positive norm index.  The other column
is the original twist, corrected by the actual shear of the existing
surface marking.  Its integral correction is determined by the genuine
covering coefficient, rather than by a replacement of that marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The positive original fourth period vector. -/
def deltaVector : Lattice := ![0, 0, 0, 1]

theorem twist_fourth_zero (j : Kind) : j.twist 3 = 0 := by
  cases j <;> rfl

/-- The actual integral Wang map forces divisibility of the covering shear correction. -/
theorem sourceShearOne_correction_divisible (j : Kind) :
    (j.order : ℤ) ∣ (fibreNormIndex j : ℤ) * sourceShearOne j := by
  let a := (surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![0, 1]
  have he : surfaceH1Equiv j (specialLocalData j).centralPeriod a = ![0, 1] :=
    LinearEquiv.apply_symm_apply _ _
  have h := h1Coordinates_cover_columns j a
  rw [originalAffineNorm_splitFibreClassOne, originalAffineNorm_splitCircleClassOne] at h
  have h₃ := congrFun h (3 : Fin 4)
  change (j.order : ℤ) * h1Coordinates j a 3 =
    ((j.order : ℤ) * (surfaceH1Equiv j (specialLocalData j).centralPeriod a) 0 -
      sourceShearOne j * (surfaceH1Equiv j (specialLocalData j).centralPeriod a) 1) *
        ((fibreNormIndex j : ℤ) * 1) +
    (surfaceH1Equiv j (specialLocalData j).centralPeriod a) 1 *
      ((j.order : ℤ) * j.twist 3) at h₃
  rw [he, twist_fourth_zero] at h₃
  change (j.order : ℤ) * h1Coordinates j a 3 =
    ((j.order : ℤ) * 0 - sourceShearOne j * 1) * ((fibreNormIndex j : ℤ) * 1) +
      1 * ((j.order : ℤ) * 0) at h₃
  refine ⟨-h1Coordinates j a 3, ?_⟩
  linear_combination h₃

/-- The actual shear correction, computed from the genuine covering column. -/
def h1ShearCorrection (j : Kind) : ℤ :=
  ((fibreNormIndex j : ℤ) * sourceShearOne j) / j.order

theorem order_mul_h1ShearCorrection (j : Kind) :
    (j.order : ℤ) * h1ShearCorrection j = (fibreNormIndex j : ℤ) * sourceShearOne j := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (sourceShearOne_correction_divisible j)

/-- The complete actual map in the original rank-four period marking and the
existing rank-two surface marking. -/
theorem h1Coordinates_formula (j : Kind) (a : SingularHomology (S j) 1) :
    h1Coordinates j a =
      surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 • j.twist +
      ((fibreNormIndex j : ℤ) * surfaceH1Equiv j (specialLocalData j).centralPeriod a 0 -
        h1ShearCorrection j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1) •
          deltaVector := by
  have h := h1Coordinates_cover_columns j a
  rw [originalAffineNorm_splitFibreClassOne, originalAffineNorm_splitCircleClassOne] at h
  have hm : (j.order : ℤ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  ext i
  apply mul_left_cancel₀ hm
  have hi := congrFun h i
  change (j.order : ℤ) * h1Coordinates j a i =
    ((j.order : ℤ) * surfaceH1Equiv j (specialLocalData j).centralPeriod a 0 -
      sourceShearOne j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1) *
        ((fibreNormIndex j : ℤ) * deltaVector i) +
      surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 *
        ((j.order : ℤ) * j.twist i) at hi
  change (j.order : ℤ) * h1Coordinates j a i =
    (j.order : ℤ) *
      (surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 * j.twist i +
        ((fibreNormIndex j : ℤ) * surfaceH1Equiv j (specialLocalData j).centralPeriod a 0 -
          h1ShearCorrection j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1) *
            deltaVector i)
  rw [hi]
  have hk := order_mul_h1ShearCorrection j
  linear_combination
    (surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 * deltaVector i) * hk

/-- In particular, the primitive fibre generator has its actual positive norm index. -/
theorem h1Coordinates_first_axis (j : Kind) :
    h1Coordinates j ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![1, 0]) =
      (fibreNormIndex j : ℤ) • deltaVector := by
  rw [h1Coordinates_formula, LinearEquiv.apply_symm_apply]
  simp

/-- The second old basis vector retains the actual covering shear. -/
theorem h1Coordinates_second_axis (j : Kind) :
    h1Coordinates j ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm ![0, 1]) =
      j.twist - h1ShearCorrection j • deltaVector := by
  rw [h1Coordinates_formula, LinearEquiv.apply_symm_apply]
  simp [sub_eq_add_neg]

/-- The literal cap-kernel inverse has the same fully computed Wang coefficient. -/
theorem capKernel_wang_h1_coordinates (j : Kind) (a : SingularHomology (S j) 1) :
    FlatTorus.singularH1Equiv
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) 1
          ((EllipticCapProduct.boundaryCapKernelEquiv j 1).symm a).val) =
      surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 • j.twist +
      ((fibreNormIndex j : ℤ) * surfaceH1Equiv j (specialLocalData j).centralPeriod a 0 -
        h1ShearCorrection j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1) •
          deltaVector :=
  h1Coordinates_formula j a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
