import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedWordOrbits
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedCutFirst
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedCutSecond

/-!
# Orbit points in the actual closed circular polygon

The reduced-word classification leaves only the bounded powers of the two
cyclic factors.  Their proved boundary-return identities show that every
orbit point in the closed polygon is either the original point or its
reflection in the circular side.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- A point of the actual closed circular polygon can return only to
itself or to its circular reflection. -/
theorem circularDoubleRegion_orbit_point (g : TriangleGroup) {z : ℍ}
    (hz : z ∈ circularDoubleRegion)
    (hgz : triangleGeometricRepresentation g z ∈ circularDoubleRegion) :
    triangleGeometricRepresentation g z = z ∨
      triangleGeometricRepresentation g z = circleReflection z := by
  rcases circularDoubleRegion_return_generator_pow g hz hgz with
    ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · simp only [map_pow, triangleGeometricRepresentation_generator₁,
      generatorOnePerm_pow_apply] at hgz ⊢
    interval_cases n
    · exact Or.inl (by simp)
    · right
      simp only [pow_one] at hgz ⊢
      exact generatorOne_closed_return z hz hgz
    · exact Or.inr (generatorOne_sq_closed_return z hz hgz)
  · simp only [map_pow, triangleGeometricRepresentation_generator₂,
      generatorTwoPerm_pow_apply] at hgz ⊢
    interval_cases n
    · exact Or.inl (by simp)
    · right
      simp only [pow_one] at hgz ⊢
      exact generatorTwo_closed_return z hz hgz
    · exact Or.inr (generatorTwo_sq_closed_return z hz hgz)
    · exact Or.inr (generatorTwo_cube_closed_return z hz hgz)

/-- The actual triangle orbit relation between two closed-polygon points
allows only equality or the circular-side reflection. -/
theorem circularDoubleRegion_orbit_point_of_eq (g : TriangleGroup) {z w : ℍ}
    (hz : z ∈ circularDoubleRegion) (hw : w ∈ circularDoubleRegion)
    (hzw : triangleGeometricRepresentation g z = w) :
    w = z ∨ w = circleReflection z := by
  simpa only [hzw] using circularDoubleRegion_orbit_point g hz (hzw ▸ hw)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
