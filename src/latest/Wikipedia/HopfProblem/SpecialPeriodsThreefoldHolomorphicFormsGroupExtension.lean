import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupDerivative

/-!
# The original right-block cocycle on the full upper half-plane

The constructed special periods exist on all of the upper half-plane,
including both elliptic orbits. Together with the actual geometric
triangle action they give the same right-block matrices as on the regular
cover. The original cocycle supplies holomorphic inverse matrices there
as well, without an extension hypothesis.
-/

noncomputable section

open Matrix UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] triangleGeometricAction

/-- The original global special periods with the actual full triangle action. -/
def fullGroupData : TrianglePeriodFamily.Data ℂ ℍ where
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

/-- The actual period right block, defined also at every elliptic orbit point. -/
def groupRightBlockExtension (g : TriangleGroup) (z : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fullGroupData.rightBlock g z

/-- Restriction recovers exactly the unchanged regular-family matrix. -/
@[simp] theorem groupRightBlockExtension_restrict (g : TriangleGroup)
    (z : TriangleRegularPoint) : groupRightBlockExtension g z.val = data.rightBlock g z := rfl

theorem groupRightBlockExtension_entry_holomorphic (g : TriangleGroup) (i k : Fin 2) :
    ContMDiff I₁ I₁ ω (fun z : ℍ => groupRightBlockExtension g z i k) :=
  fullGroupData.rightBlock_entry_holomorphic g i k

theorem groupRightBlockExtension_det_ne_zero (g : TriangleGroup) (z : ℍ) :
    (groupRightBlockExtension g z).det ≠ 0 :=
  fullGroupData.rightBlock_det_ne_zero g z

/-- The full original cocycle, including points omitted from the regular cover. -/
theorem groupRightBlockExtension_mul (g h : TriangleGroup) (z : ℍ) :
    groupRightBlockExtension (g * h) z =
      groupRightBlockExtension g (triangleGeometricRepresentation h z) *
        groupRightBlockExtension h z :=
  fullGroupData.rightBlock_mul g h z

theorem groupRightBlockExtension_inv_mul (g : TriangleGroup) (z : ℍ) :
    groupRightBlockExtension g⁻¹ (triangleGeometricRepresentation g z) *
      groupRightBlockExtension g z = 1 :=
  fullGroupData.rightBlock_inv_mul g z

theorem groupRightBlockExtension_mul_inv (g : TriangleGroup) (z : ℍ) :
    groupRightBlockExtension g z *
      groupRightBlockExtension g⁻¹ (triangleGeometricRepresentation g z) = 1 :=
  mul_eq_one_comm.mpr (groupRightBlockExtension_inv_mul g z)

/-- The inverse matrix is the original inverse-group cocycle at the image point. -/
theorem groupRightBlockExtension_inv_eq (g : TriangleGroup) (z : ℍ) :
    (groupRightBlockExtension g z)⁻¹ =
      groupRightBlockExtension g⁻¹ (triangleGeometricRepresentation g z) :=
  Matrix.inv_eq_left_inv (groupRightBlockExtension_inv_mul g z)

/-- Its inverse entries are holomorphic everywhere in the original base atlas. -/
theorem groupRightBlockExtension_inv_entry_holomorphic (g : TriangleGroup) (i k : Fin 2) :
    ContMDiff I₁ I₁ ω (fun z : ℍ => (groupRightBlockExtension g z)⁻¹ i k) := by
  simp_rw [groupRightBlockExtension_inv_eq]
  exact (groupRightBlockExtension_entry_holomorphic g⁻¹ i k).comp
    (triangleGeometricRepresentation_holomorphic g)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
