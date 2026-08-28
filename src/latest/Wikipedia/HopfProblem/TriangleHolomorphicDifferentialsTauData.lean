import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalFactors
import Wikipedia.HopfProblem.SpecialPeriodsExistence

/-!
# The actual special periods and determinant factors on the full upper half-plane

The already constructed global special periods and the already constructed
holomorphic triangle action give genuine period-family data before any
restriction to the regular locus. The scalar factors below are the
determinants of the actual complex period-covariance matrices.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods

attribute [local instance] triangleGeometricAction

/-- The actual global special period family over the original upper half-plane. -/
def specialData : TrianglePeriodFamily.Data ℂ ℍ where
  periods := specialPeriodMap
  base_holomorphic := triangleGeometricRepresentation_holomorphic
  covariance₁ z := by
    change specialPeriodMap.point (triangleGeometricRepresentation triangleGenerator₁ z) = _
    rw [triangleGeometricRepresentation_generator₁_apply]
    exact specialPeriodMap_generator₁ z
  covariance₂ z := by
    change specialPeriodMap.point (triangleGeometricRepresentation triangleGenerator₂ z) = _
    rw [triangleGeometricRepresentation_generator₂_apply]
    exact specialPeriodMap_generator₂ z

@[simp] theorem specialData_periods : specialData.periods = specialPeriodMap := rfl

/-- The determinant of the actual complex covariance matrix. -/
def determinantFactor (g : TriangleGroup) (z : ℍ) : ℂ :=
  specialData.determinantFactor g z

/-- The reciprocal determinant factor appearing in the source. -/
def inverseDeterminantFactor (g : TriangleGroup) (z : ℍ) : ℂ :=
  specialData.inverseDeterminantFactor g z

theorem determinantFactor_ne_zero (g : TriangleGroup) (z : ℍ) :
    determinantFactor g z ≠ 0 := specialData.determinantFactor_ne_zero g z

theorem inverseDeterminantFactor_ne_zero (g : TriangleGroup) (z : ℍ) :
    inverseDeterminantFactor g z ≠ 0 := specialData.inverseDeterminantFactor_ne_zero g z

theorem determinantFactor_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (determinantFactor g) :=
  specialData.determinantFactor_holomorphic g

theorem inverseDeterminantFactor_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (inverseDeterminantFactor g) :=
  specialData.inverseDeterminantFactor_holomorphic g

@[simp] theorem determinantFactor_one (z : ℍ) : determinantFactor 1 z = 1 :=
  specialData.determinantFactor_one z

theorem determinantFactor_mul (g h : TriangleGroup) (z : ℍ) :
    determinantFactor (g * h) z =
      determinantFactor g (triangleGeometricRepresentation h z) * determinantFactor h z :=
  specialData.determinantFactor_mul g h z

@[simp] theorem determinantFactor_generator₁ (z : ℍ) :
    determinantFactor triangleGenerator₁ z = -1 / specialTau z :=
  specialData.determinantFactor_generator₁ z

@[simp] theorem determinantFactor_generator₂ (z : ℍ) :
    determinantFactor triangleGenerator₂ z = 1 / specialTau z :=
  specialData.determinantFactor_generator₂ z

@[simp] theorem determinantFactor_cusp (z : ℍ) :
    determinantFactor triangleCuspGenerator z = 1 := specialData.determinantFactor_cusp z

@[simp] theorem inverseDeterminantFactor_eq_inv (g : TriangleGroup) (z : ℍ) :
    inverseDeterminantFactor g z = (determinantFactor g z)⁻¹ := rfl

@[simp] theorem inverseDeterminantFactor_generator₁ (z : ℍ) :
    inverseDeterminantFactor triangleGenerator₁ z = -specialTau z :=
  specialData.inverseDeterminantFactor_generator₁ z

@[simp] theorem inverseDeterminantFactor_generator₂ (z : ℍ) :
    inverseDeterminantFactor triangleGenerator₂ z = specialTau z :=
  specialData.inverseDeterminantFactor_generator₂ z

@[simp] theorem inverseDeterminantFactor_cusp (z : ℍ) :
    inverseDeterminantFactor triangleCuspGenerator z = 1 :=
  specialData.inverseDeterminantFactor_cusp z

theorem specialTau_ne_zero (z : ℍ) : specialTau z ≠ 0 :=
  (specialPeriodMap.point z).val.τ_ne_zero (specialPeriodMap.point z).property.1

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
