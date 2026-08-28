import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupHomeomorph

/-!
# Circle reflection in the actual normalized triangle uniformization

Circle reflection and right reflection differ by the first triangle-group
generator.  They therefore define the same actual triangle orbit.  On
the finite half-Ford triangle the folded uniformization reads that orbit
as the complex conjugate of the normalized half-plane value.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping TriangleUniformizationGluing

/-- The two reflected points have the same actual triangle orbit. -/
theorem triangleOrbitProjection_circleReflection (z : ℍ) :
    triangleOrbitProjection (circleReflection z) =
      triangleOrbitProjection (rightReflection z) := by
  have h := triangleOrbitProjection_smul triangleGenerator₁ (circleReflection z)
  rw [triangleGeometricRepresentation_generator₁_apply, generatorOne_reflections,
    circleReflection_involutive] at h
  exact h.symm

/-- Circle reflection conjugates the normalized uniformization value of
every point in the closed finite half-Ford triangle. -/
theorem trianglePlaneUniformizationHomeomorph_circleReflection {z : ℍ}
    (hz : z ∈ halfFordRegion) :
    trianglePlaneUniformizationHomeomorph (triangleOrbitProjection (circleReflection z)) =
      conj (triangleSignedHalfPlaneMap z) := by
  rw [triangleOrbitProjection_circleReflection]
  change triangleSignedHalfPlaneMap.quotientHomeomorph
    triangleSignedHalfPlaneMap_isProperMap (triangleOrbitProjection (rightReflection z)) = _
  rw [triangleSignedHalfPlaneMap.quotientHomeomorph_projection
    triangleSignedHalfPlaneMap_isProperMap (rightReflection z)
      (rightReflection_mapsTo_fordRegion hz.1)]
  exact triangleSignedHalfPlaneMap.toBoundaryMap.foldedFordMap_reflected z hz

/-- The same reflection identity in the literal normalized half-plane
homeomorphism coordinates, with the original half-triangle membership. -/
theorem trianglePlaneUniformizationHomeomorph_circleReflection_normalization {z : ℍ}
    (hz : z ∈ halfFordRegion) :
    trianglePlaneUniformizationHomeomorph (triangleOrbitProjection (circleReflection z)) =
      conj (halfFordNormalizationHomeomorph ⟨z, hz⟩ : ℂ) := by
  rw [trianglePlaneUniformizationHomeomorph_circleReflection hz,
    triangleSignedHalfPlaneMap_of_mem hz]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
