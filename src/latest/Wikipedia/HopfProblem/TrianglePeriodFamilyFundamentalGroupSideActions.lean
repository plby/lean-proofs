import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupLiftedBasepoints

/-!
# The actual generator identifications at the semicircle endpoints

The reflection fixing each real boundary preimage gives the exact
triangle-group element joining its two reflected lifts. These are
equalities of points in the original regular upper-half-plane locus.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

/-- At the right side, circle reflection is the inverse first generator. -/
theorem circleReflection_eq_inverse_generatorOne (z : ℍ)
    (hz : rightReflection z = z) :
    circleReflection z = triangleGeometricRepresentation triangleGenerator₁⁻¹ z := by
  rw [map_inv]
  apply (triangleGeometricRepresentation triangleGenerator₁).eq_symm_apply.mpr
  rw [triangleGeometricRepresentation_generator₁_apply, generatorOne_reflections,
    circleReflection_involutive, hz]

/-- At the left side, circle reflection is the second generator. -/
theorem circleReflection_eq_generatorTwo (z : ℍ)
    (hz : leftReflection z = z) :
    circleReflection z = triangleGeometricRepresentation triangleGenerator₂ z := by
  rw [triangleGeometricRepresentation_generator₂_apply, generatorTwo_reflections, hz]

@[simp] theorem reflectedHalfPlaneLift_leftPoint :
    reflectedHalfPlaneLift halfPlaneMeridianLeftPoint =
      triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint := by
  apply Subtype.ext
  exact circleReflection_eq_inverse_generatorOne _
    normalizedRegularMeridianLeftPoint_rightReflection

@[simp] theorem reflectedHalfPlaneLift_rightPoint :
    reflectedHalfPlaneLift halfPlaneMeridianRightPoint =
      triangleGenerator₂ • normalizedRegularMeridianRightPoint := by
  apply Subtype.ext
  exact circleReflection_eq_generatorTwo _ normalizedRegularMeridianRightPoint_leftReflection

@[simp] theorem inverse_generatorTwo_reflectedHalfPlaneLift_rightPoint :
    triangleGenerator₂⁻¹ • reflectedHalfPlaneLift halfPlaneMeridianRightPoint =
      normalizedRegularMeridianRightPoint := by
  rw [reflectedHalfPlaneLift_rightPoint, inv_smul_smul]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
