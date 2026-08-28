import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroup
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupExtensionDerivative

/-!
# Solved coefficient transport with the actual globally holomorphic factors

Invertibility of the actual base action and actual right-block matrices
solves the genuine coefficient covariance equations. Their full
upper-half-plane versions use the proved restrictions of the original
global factors, including their holomorphic inverses at elliptic points.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

theorem groupBaseDerivative_ne_zero (g : TriangleGroup) (z : TriangleRegularPoint) :
    groupBaseDerivative g z ≠ 0 := by
  simpa only [groupBaseDerivativeExtension_restrict] using
    groupBaseDerivativeExtension_ne_zero g z.val

@[simp] theorem groupRightBlock_mul_inv (g : TriangleGroup) (z : TriangleRegularPoint) :
    data.rightBlock g z * (data.rightBlock g z)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (data.rightBlock_det_ne_zero g z))

/-- The original row-covector equation solved using the actual matrix inverse. -/
theorem fibreOne_group_transport (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) = fibreOne θ z ᵥ* (data.rightBlock g z)⁻¹ := by
  have h := congrArg (fun C : ComplexPlane₂ => C ᵥ* (data.rightBlock g z)⁻¹)
    (fibreOne_group_covariance θ g z)
  simpa only [Matrix.vecMul_vecMul, groupRightBlock_mul_inv, Matrix.vecMul_one] using h

/-- The base coefficient transforms by the reciprocal of the actual base Jacobian. -/
theorem baseOne_group_transport (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseOne θ (g • z) = baseOne θ z / groupBaseDerivative g z :=
  (eq_div_iff (groupBaseDerivative_ne_zero g z)).mpr (baseOne_group_covariance θ g z)

/-- Both mixed coefficients use the reciprocal base Jacobian and original inverse matrix. -/
theorem mixedTwo_group_transport (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    mixedTwo θ (g • z) = (groupBaseDerivative g z)⁻¹ •
      (mixedTwo θ z ᵥ* (data.rightBlock g z)⁻¹) := by
  have h₁ : mixedTwo θ (g • z) ᵥ* data.rightBlock g z =
      (groupBaseDerivative g z)⁻¹ • mixedTwo θ z := by
    rw [← mixedTwo_group_covariance θ g z, smul_smul,
      inv_mul_cancel₀ (groupBaseDerivative_ne_zero g z), one_smul]
  have h := congrArg (fun C : ComplexPlane₂ => C ᵥ* (data.rightBlock g z)⁻¹) h₁
  simpa only [Matrix.vecMul_vecMul, groupRightBlock_mul_inv, Matrix.vecMul_one,
    Matrix.smul_vecMul] using h

/-- The top coefficient transforms by the reciprocal of the full block determinant. -/
theorem baseTop_group_transport (θ : Form Model Threefold.Space 3)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseTop θ (g • z) = baseTop θ z /
      (groupBaseDerivative g z * (data.rightBlock g z).det) := by
  apply (eq_div_iff (mul_ne_zero (groupBaseDerivative_ne_zero g z)
    (data.rightBlock_det_ne_zero g z))).mpr
  simpa only [mul_assoc] using baseTop_group_covariance θ g z

/-- The fibre transport factor is the restriction of the holomorphic
inverse matrix on the whole upper half-plane. -/
theorem fibreOne_group_transport_extension (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) = fibreOne θ z ᵥ* (groupRightBlockExtension g z.val)⁻¹ := by
  simpa only [groupRightBlockExtension_restrict] using fibreOne_group_transport θ g z

theorem baseOne_group_transport_extension (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseOne θ (g • z) = baseOne θ z / groupBaseDerivativeExtension g z.val := by
  simpa only [groupBaseDerivativeExtension_restrict] using baseOne_group_transport θ g z

theorem mixedTwo_group_transport_extension (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    mixedTwo θ (g • z) = (groupBaseDerivativeExtension g z.val)⁻¹ •
      (mixedTwo θ z ᵥ* (groupRightBlockExtension g z.val)⁻¹) := by
  simpa only [groupBaseDerivativeExtension_restrict, groupRightBlockExtension_restrict] using
    mixedTwo_group_transport θ g z

theorem baseTop_group_transport_extension (θ : Form Model Threefold.Space 3)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseTop θ (g • z) = baseTop θ z /
      (groupBaseDerivativeExtension g z.val * (groupRightBlockExtension g z.val).det) := by
  simpa only [groupBaseDerivativeExtension_restrict, groupRightBlockExtension_restrict] using
    baseTop_group_transport θ g z

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
