import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupTriangular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationScalar

/-!
# The actual scalar characters of vertical column coefficients

The original right-block cocycle is lower triangular with fixed second
column. Its first component has exactly the homogeneous μ character;
after that component vanishes, its second component is invariant under
the full triangle group. These are algebraic consequences of the proved
actual matrices, not additional automorphy assumptions.
-/

noncomputable section

open Matrix UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open HolomorphicForms.RegularCover

attribute [local instance] triangleGeometricAction

theorem groupRightBlockExtension_det_generator₁ (z : ℍ) :
    (groupRightBlockExtension triangleGenerator₁ z).det = -1 / specialTau z :=
  fullGroupData.determinantFactor_generator₁ z

theorem groupRightBlockExtension_det_generator₂ (z : ℍ) :
    (groupRightBlockExtension triangleGenerator₂ z).det = 1 / specialTau z :=
  fullGroupData.determinantFactor_generator₂ z

variable {H : ℍ → ComplexPlane₂}
  (hH : ∀ g : TriangleGroup, ∀ z : ℍ,
    H (triangleGeometricRepresentation g z) = groupRightBlockExtension g z *ᵥ H z)

include hH

theorem first_covariant (g : TriangleGroup) (z : ℍ) :
    H (triangleGeometricRepresentation g z) 0 = (groupRightBlockExtension g z).det * H z 0 := by
  have h := congrFun (hH g z) 0
  rw [groupRightBlockExtension_eq_lower] at h
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, zero_mul, add_zero] using h

theorem first_covariant_generator₁ (z : ℍ) :
    H (Triangle.generatorOneSL • z) 0 = -H z 0 / specialTau z := by
  have h := first_covariant hH triangleGenerator₁ z
  rw [triangleGeometricRepresentation_generator₁_apply,
    groupRightBlockExtension_det_generator₁] at h
  exact h.trans (by ring)

theorem first_covariant_generator₂ (z : ℍ) :
    H (Triangle.generatorTwoSL • z) 0 = H z 0 / specialTau z := by
  have h := first_covariant hH triangleGenerator₂ z
  rw [triangleGeometricRepresentation_generator₂_apply,
    groupRightBlockExtension_det_generator₂] at h
  exact h.trans (by ring)

theorem second_invariant_of_first_zero (hzero : ∀ z : ℍ, H z 0 = 0)
    (g : TriangleGroup) (z : ℍ) :
    H (triangleGeometricRepresentation g z) 1 = H z 1 := by
  have h := congrFun (hH g z) 1
  rw [groupRightBlockExtension_eq_lower] at h
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, hzero, mul_zero, one_mul, zero_add] using h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
