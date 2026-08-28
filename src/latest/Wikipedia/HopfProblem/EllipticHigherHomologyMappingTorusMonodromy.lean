import Wikipedia.HopfProblem.EllipticHigherHomologyCoordinatesTorus
import Wikipedia.HopfProblem.EllipticHigherHomologyAlgebra
import Wikipedia.HopfProblem.EllipticHigherHomologyTorus
import Wikipedia.HopfProblem.MappingTorusHomology

/-!
# The actual elliptic mapping-torus monodromy on integral homology

The explicit affine quotient has deck transformation `(t + 1, B x)`.
With the standard endpoint convention this is the mapping torus of
`B⁻¹`.  The actual positive coordinate-loop markings, and their actual
exterior products, identify its Wang operators with the integral
matrices already calculated.  No homology action is postulated.
-/

noncomputable section

open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- Powers of the genuine torus automorphism are the genuine matrix maps. -/
theorem fibreTorusHomeomorph_pow_apply (j : Kind) (n : ℕ) (x : ProductTorus 3) :
    (fibreTorusHomeomorph j ^ n) x = torusMatrixMap (fibreMatrix j ^ n) x := by
  induction n generalizing x with
  | zero => simp only [pow_zero, Homeomorph.one_apply, torusMatrixMap_one]; rfl
  | succ n ih =>
    rw [pow_succ, Homeomorph.mul_apply, ih, fibreTorusHomeomorph_apply,
      pow_succ, torusMatrixMap_mul]
    rfl

/-- The actual restricted torus automorphism has the required finite period. -/
theorem fibreTorusHomeomorph_pow_order (j : Kind) :
    fibreTorusHomeomorph j ^ j.order = 1 := by
  ext x
  rw [fibreTorusHomeomorph_pow_apply, fibreMatrix_pow_order, torusMatrixMap_one]
  rfl

/-- The special-linear inverse and the integral nonsingular inverse agree. -/
theorem fibreSL_inv_val (j : Kind) :
    (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) = (fibreMatrix j)⁻¹ := by
  have hleft : (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) * fibreMatrix j = 1 :=
    congrArg (fun C : SL(3, ℤ) => C.val) (inv_mul_cancel (fibreSL j))
  calc
    (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) =
        (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) * 1 := (mul_one _).symm
    _ = (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) *
        (fibreMatrix j * (fibreMatrix j)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (by simp [fibreMatrix_det])]
    _ = (fibreMatrix j)⁻¹ := by rw [← mul_assoc, hleft, one_mul]

/-- Exterior-square coordinates commute with the actual inverse matrix. -/
theorem torusSquareMatrix_fibreMatrix_inv (j : Kind) :
    torusSquareMatrix ((fibreMatrix j)⁻¹) = (fibreSquareMatrix j)⁻¹ := by
  have hleft : torusSquareMatrix ((fibreMatrix j)⁻¹) * fibreSquareMatrix j = 1 := by
    rw [← torusSquareMatrix_fibreMatrix, ← torusSquareMatrix_mul,
      Matrix.nonsing_inv_mul _ (by simp [fibreMatrix_det]), torusSquareMatrix_one]
  calc
    torusSquareMatrix ((fibreMatrix j)⁻¹) =
        torusSquareMatrix ((fibreMatrix j)⁻¹) * 1 := (mul_one _).symm
    _ = torusSquareMatrix ((fibreMatrix j)⁻¹) *
        (fibreSquareMatrix j * (fibreSquareMatrix j)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (by simp [fibreSquareMatrix_det])]
    _ = (fibreSquareMatrix j)⁻¹ := by rw [← mul_assoc, hleft, one_mul]

/-- Both inverse fibre automorphisms preserve the integral orientation. -/
theorem fibreMatrix_inv_det (j : Kind) : (fibreMatrix j)⁻¹.det = 1 := by
  have h := Matrix.det_nonsing_inv_mul_det (fibreMatrix j)
    (by simp [fibreMatrix_det])
  simpa only [fibreMatrix_det, mul_one] using h

/-- The actual topological mapping-torus model, in the standard convention. -/
abbrev mappingTorusModel (j : Kind) := MappingTorus.Torus (fibreTorusHomeomorph j).symm

/-- Actual first homology sees the inverse integral fibre matrix. -/
theorem mappingTorusMonodromy_one (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    torusH1Equiv (monodromyHomologyMap (fibreTorusHomeomorph j).symm 1 a) =
      (fibreMatrix j)⁻¹ *ᵥ torusH1Equiv a := by
  change torusH1Equiv
    (singularHomologyMap (torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)) 1 a) = _
  rw [fibreSL_inv_val, torusH1Equiv_matrix_natural]

/-- Actual second homology sees the inverse ordered matrix of minors. -/
theorem mappingTorusMonodromy_two (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2Coordinates (monodromyHomologyMap (fibreTorusHomeomorph j).symm 2 a) =
      (fibreSquareMatrix j)⁻¹ *ᵥ torusH2Coordinates a := by
  change torusH2Coordinates
    (singularHomologyMap (torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)) 2 a) = _
  rw [fibreSL_inv_val, torusH2Coordinates_matrix_natural,
    torusSquareMatrix_fibreMatrix_inv]

/-- The actual positive third-homology generator is fixed. -/
theorem mappingTorusMonodromy_three (j : Kind)
    (a : SingularHomology (ProductTorus 3) 3) :
    torusH3Coordinates (monodromyHomologyMap (fibreTorusHomeomorph j).symm 3 a) =
      torusH3Coordinates a := by
  change torusH3Coordinates
    (singularHomologyMap (torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)) 3 a) = _
  rw [fibreSL_inv_val, torusH3Coordinates_matrix_natural, fibreMatrix_inv_det, one_mul]

/-- The actual degree-one Wang operator has the calculated integral coordinates. -/
theorem mappingTorusDifference_one (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    torusH1Equiv (wangDifference (fibreTorusHomeomorph j).symm 1 a) =
      fibreInverseDifference j (torusH1Equiv a) := by
  change torusH1Equiv (a - monodromyHomologyMap (fibreTorusHomeomorph j).symm 1 a) = _
  rw [map_sub, mappingTorusMonodromy_one]
  simp only [fibreInverseDifference, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec]

/-- The actual degree-two Wang operator has the calculated integral coordinates. -/
theorem mappingTorusDifference_two (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    torusH2Coordinates (wangDifference (fibreTorusHomeomorph j).symm 2 a) =
      fibreSquareInverseDifference j (torusH2Coordinates a) := by
  change torusH2Coordinates (a - monodromyHomologyMap (fibreTorusHomeomorph j).symm 2 a) = _
  rw [map_sub, mappingTorusMonodromy_two]
  simp only [fibreSquareInverseDifference, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec]

/-- The degree-three Wang operator is genuinely zero. -/
theorem mappingTorusDifference_three (j : Kind) :
    wangDifference (fibreTorusHomeomorph j).symm 3 = 0 := by
  ext a
  apply torusH3Coordinates.injective
  change torusH3Coordinates (a - monodromyHomologyMap (fibreTorusHomeomorph j).symm 3 a) =
    torusH3Coordinates 0
  rw [map_sub, mappingTorusMonodromy_three, sub_self, map_zero]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
