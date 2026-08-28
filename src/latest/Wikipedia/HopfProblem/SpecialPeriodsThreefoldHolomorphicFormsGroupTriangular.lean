import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupCovariance
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupExtension
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalFactors

/-!
# The actual triangular cocycle and its scalar form laws

The fixed last lattice vector forces the second column of every right
block to be the second unit vector. These identities hold for the
constructed regular-family data and its original full upper-half-plane
data. Evaluation of the genuine covector laws then gives the scalar
coefficient identities, including the complete lower shear term.
-/

noncomputable section

open Matrix UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold
  triangleGeometricAction

/-- The actual regular right block has second column equal to the second unit vector. -/
theorem groupRightBlock_secondColumn (g : TriangleGroup) (z : TriangleRegularPoint) :
    (fun i => data.rightBlock g z i 1) = (![0, 1] : Fin 2 → ℂ) :=
  data.rightBlock_secondColumn g z

theorem groupRightBlock_eq_lower (g : TriangleGroup) (z : TriangleRegularPoint) :
    data.rightBlock g z = !![(data.rightBlock g z).det, 0; data.rightBlock g z 1 0, 1] :=
  data.rightBlock_eq_lower g z

theorem groupRightBlock_det_eq_entry (g : TriangleGroup) (z : TriangleRegularPoint) :
    (data.rightBlock g z).det = data.rightBlock g z 0 0 :=
  data.rightBlock_det_eq_entry g z

theorem groupRightBlock_isLowerTriangular (g : TriangleGroup) (z : TriangleRegularPoint) :
    (data.rightBlock g z).IsLowerTriangular :=
  data.rightBlock_isLowerTriangular g z

/-- The same column identity holds at every point of the original upper half-plane. -/
theorem groupRightBlockExtension_secondColumn (g : TriangleGroup) (z : ℍ) :
    (fun i => groupRightBlockExtension g z i 1) = (![0, 1] : Fin 2 → ℂ) :=
  fullGroupData.rightBlock_secondColumn g z

theorem groupRightBlockExtension_eq_lower (g : TriangleGroup) (z : ℍ) :
    groupRightBlockExtension g z =
      !![(groupRightBlockExtension g z).det, 0; groupRightBlockExtension g z 1 0, 1] :=
  fullGroupData.rightBlock_eq_lower g z

theorem groupRightBlockExtension_det_eq_entry (g : TriangleGroup) (z : ℍ) :
    (groupRightBlockExtension g z).det = groupRightBlockExtension g z 0 0 :=
  fullGroupData.rightBlock_det_eq_entry g z

theorem groupRightBlockExtension_isLowerTriangular (g : TriangleGroup) (z : ℍ) :
    (groupRightBlockExtension g z).IsLowerTriangular :=
  fullGroupData.rightBlock_isLowerTriangular g z

/-- The second fibre coefficient of every genuine global one-form is group invariant. -/
theorem fibreOne_second_group_invariant (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) 1 = fibreOne θ z 1 := by
  have h := congrFun (fibreOne_group_covariance θ g z) 1
  simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
    data.rightBlock_zero_one, data.rightBlock_one_one, mul_zero, mul_one, zero_add] using h

/-- The second mixed coefficient carries only the actual base derivative. -/
theorem mixedTwo_second_group_covariance (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    mixedTwo θ (g • z) 1 * groupBaseDerivative g z = mixedTwo θ z 1 := by
  have h := congrFun (mixedTwo_group_covariance θ g z) 1
  rw [mul_comm]
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.transpose_apply, data.rightBlock_zero_one,
    data.rightBlock_one_one, mul_zero, mul_one, zero_add] using h

/-- The first fibre coefficient retains the complete lower shear contribution. -/
theorem fibreOne_first_group_covariance (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) 0 * (data.rightBlock g z).det +
        fibreOne θ (g • z) 1 * data.rightBlock g z 1 0 = fibreOne θ z 0 := by
  have h := congrFun (fibreOne_group_covariance θ g z) 0
  simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
    groupRightBlock_det_eq_entry] using h

/-- The first mixed coefficient obeys the full triangular row law with the base derivative. -/
theorem mixedTwo_first_group_covariance (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    (mixedTwo θ (g • z) 0 * (data.rightBlock g z).det +
        mixedTwo θ (g • z) 1 * data.rightBlock g z 1 0) * groupBaseDerivative g z =
      mixedTwo θ z 0 := by
  have h := congrFun (mixedTwo_group_covariance θ g z) 0
  rw [mul_comm]
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.transpose_apply, groupRightBlock_det_eq_entry] using h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
