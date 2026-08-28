import Wikipedia.HopfProblem.TriangleRiemannSignedHalfPlane
import Wikipedia.HopfProblem.TriangleUniformizationGluingProper

/-!
# The actual triangle quotient is a plane, and its compactification a sphere

The normalized Riemann map now supplies every input to the reflection
gluing construction. This gives actual homeomorphisms of the original
quotient and its original one-point compactification, with the prescribed
three marked values. Compatibility with the already constructed complex
atlases is the additional analytic step.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannMapping TriangleUniformizationGluing

/-- The genuine quotient topology is homeomorphic to the complex plane. -/
def trianglePlaneUniformizationHomeomorph : TriangleOrbitSpace ≃ₜ ℂ :=
  triangleSignedHalfPlaneMap.quotientHomeomorph triangleSignedHalfPlaneMap_isProperMap

/-- The genuine cusp compactification is homeomorphic to the sphere. -/
def triangleSphereUniformizationHomeomorph :
    TriangleCompactifiedOrbitSpace ≃ₜ RiemannSphere :=
  triangleSignedHalfPlaneMap.compactifiedHomeomorph triangleSignedHalfPlaneMap_isProperMap

@[simp] theorem triangleSphereUniformizationHomeomorph_cusp :
    triangleSphereUniformizationHomeomorph triangleCuspPoint = (∞ : RiemannSphere) := rfl

@[simp] theorem triangleSphereUniformizationHomeomorph_openInclusion
    (q : TriangleOrbitSpace) :
    triangleSphereUniformizationHomeomorph (triangleOpenInclusion q) =
      ((trianglePlaneUniformizationHomeomorph q : ℂ) : RiemannSphere) := rfl

/-- On the literal finite half-triangle, the quotient map has exactly
the constructed normalized Riemann-map values. -/
theorem trianglePlaneUniformizationHomeomorph_projection {z : ℍ}
    (hz : z ∈ halfFordRegion) :
    trianglePlaneUniformizationHomeomorph (triangleOrbitProjection z) =
      triangleSignedHalfPlaneMap z := by
  change triangleSignedHalfPlaneMap.quotientHomeomorph
    triangleSignedHalfPlaneMap_isProperMap (triangleOrbitProjection z) = _
  rw [triangleSignedHalfPlaneMap.quotientHomeomorph_projection
    triangleSignedHalfPlaneMap_isProperMap z hz.1]
  exact triangleSignedHalfPlaneMap.toBoundaryMap.foldedFordMap_of_left hz.2

@[simp] theorem trianglePlaneUniformizationHomeomorph_centerOne :
    trianglePlaneUniformizationHomeomorph triangleOrbitCenterOne = 0 := by
  rw [show triangleOrbitCenterOne = triangleOrbitProjection centerOne from rfl,
    trianglePlaneUniformizationHomeomorph_projection centerOne_mem_halfFordRegion,
    triangleSignedHalfPlaneMap_centerOne]

@[simp] theorem trianglePlaneUniformizationHomeomorph_centerTwo :
    trianglePlaneUniformizationHomeomorph triangleOrbitCenterTwo = 1 := by
  rw [show triangleOrbitCenterTwo = triangleOrbitProjection centerTwo from rfl,
    trianglePlaneUniformizationHomeomorph_projection centerTwo_mem_halfFordRegion,
    triangleSignedHalfPlaneMap_centerTwo]

@[simp] theorem triangleSphereUniformizationHomeomorph_centerOne :
    triangleSphereUniformizationHomeomorph (triangleOpenInclusion triangleOrbitCenterOne) =
      ((0 : ℂ) : RiemannSphere) := by
  rw [triangleSphereUniformizationHomeomorph_openInclusion,
    trianglePlaneUniformizationHomeomorph_centerOne]

@[simp] theorem triangleSphereUniformizationHomeomorph_centerTwo :
    triangleSphereUniformizationHomeomorph (triangleOpenInclusion triangleOrbitCenterTwo) =
      ((1 : ℂ) : RiemannSphere) := by
  rw [triangleSphereUniformizationHomeomorph_openInclusion,
    trianglePlaneUniformizationHomeomorph_centerTwo]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
