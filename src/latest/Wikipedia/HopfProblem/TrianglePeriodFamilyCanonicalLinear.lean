import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAlternating

/-!
# Block derivatives and the period-family volume

For the actual product model `ℂ × ℂ²`, a block derivative with base derivative
`a` and fibre derivative `R` has determinant `a * det R`, independently of
the derivative `b` of the fibre coordinates in the base direction.  In
particular, fibre translations depending on the base have unit Jacobian.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

/-- A block-triangular continuous linear map on the actual period-family model. -/
def blockDerivative (a : ℂ) (b : ComplexPlane₂) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    Model →L[ℂ] Model :=
  (a • ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).prod
    ((ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).smulRight b +
      (Matrix.toLin' R).toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂))

@[simp] theorem blockDerivative_apply (a : ℂ) (b : ComplexPlane₂)
    (R : Matrix (Fin 2) (Fin 2) ℂ) (x : Model) :
    blockDerivative a b R x = (a * x.1, x.1 • b + R *ᵥ x.2) := rfl

/-- Its matrix in the standard base-first product basis. -/
theorem toMatrix_blockDerivative (a : ℂ) (b : ComplexPlane₂)
    (R : Matrix (Fin 2) (Fin 2) ℂ) :
    LinearMap.toMatrix basis basis (blockDerivative a b R).toLinearMap =
      !![a, 0, 0; b 0, R 0 0, R 0 1; b 1, R 1 0, R 1 1] := by
  ext i j
  simp only [LinearMap.toMatrix_apply, basis_repr]
  fin_cases i <;> fin_cases j <;>
    simp [basis, blockDerivative_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The base-direction shear does not affect the determinant. -/
theorem det_blockDerivative (a : ℂ) (b : ComplexPlane₂)
    (R : Matrix (Fin 2) (Fin 2) ℂ) :
    LinearMap.det (blockDerivative a b R).toLinearMap = a * R.det := by
  rw [← LinearMap.det_toMatrix basis, toMatrix_blockDerivative]
  simp [Matrix.det_fin_three, Matrix.det_fin_two, mul_sub, mul_assoc]

theorem volume_pullback_blockDerivative (a : ℂ) (b : ComplexPlane₂)
    (R : Matrix (Fin 2) (Fin 2) ℂ) :
    volume.compContinuousLinearMap (blockDerivative a b R) =
      (a * R.det) • volume := by
  rw [volume_pullback, det_blockDerivative]

theorem pullback_blockDerivative (α : TopCovector) (a : ℂ) (b : ComplexPlane₂)
    (R : Matrix (Fin 2) (Fin 2) ℂ) :
    α.compContinuousLinearMap (blockDerivative a b R) = (a * R.det) • α := by
  rw [pullback_eq_det_smul, det_blockDerivative]

theorem coefficient_pullback_blockDerivative (α : TopCovector) (a : ℂ)
    (b : ComplexPlane₂) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    coefficient (α.compContinuousLinearMap (blockDerivative a b R)) =
      (a * R.det) * coefficient α := by
  rw [coefficient_pullback, det_blockDerivative]

/-- The derivative of a base-dependent fibre translation is a shear. -/
def shearDerivative (b : ComplexPlane₂) : Model →L[ℂ] Model :=
  blockDerivative 1 b 1

@[simp] theorem shearDerivative_apply (b : ComplexPlane₂) (x : Model) :
    shearDerivative b x = (x.1, x.1 • b + x.2) := by
  simp [shearDerivative]

@[simp] theorem det_shearDerivative (b : ComplexPlane₂) :
    LinearMap.det (shearDerivative b).toLinearMap = 1 := by
  simp [shearDerivative, det_blockDerivative]

@[simp] theorem volume_pullback_shearDerivative (b : ComplexPlane₂) :
    volume.compContinuousLinearMap (shearDerivative b) = volume := by
  rw [volume_pullback, det_shearDerivative, one_smul]

@[simp] theorem pullback_shearDerivative (α : TopCovector) (b : ComplexPlane₂) :
    α.compContinuousLinearMap (shearDerivative b) = α := by
  rw [pullback_eq_det_smul, det_shearDerivative, one_smul]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
