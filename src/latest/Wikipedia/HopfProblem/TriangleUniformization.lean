import Wikipedia.HopfProblem.TriangleUniformizationTopology
import Wikipedia.HopfProblem.TriangleUniformizationGluing

/-!
# Unconditional normalized uniformization of the actual triangle quotient

The actual half-triangle Riemann map, its proved boundary extension and
three-point normalization supply all hypotheses of the reflection-gluing
theorem. The result is a biholomorphism for the previously constructed
quotient and cusp atlases, normalized at the two elliptic points and the
cusp. No uniformizing coordinate or boundary-map property is assumed.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannMapping TriangleUniformizationGluing

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The original full triangle orbit curve is biholomorphic to the plane. -/
def trianglePlaneUniformization :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω :=
  triangleSignedHalfPlaneMap.quotientBiholomorph
    triangleSignedHalfPlaneMap_isProperMap triangleSignedHalfPlaneMap_holomorphicOn

/-- The actual cusp compactification is biholomorphic to the standard
Riemann sphere, with its three prescribed marked values. -/
def triangleSphereUniformization :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω :=
  triangleSignedHalfPlaneMap.compactifiedBiholomorph
    triangleSignedHalfPlaneMap_isProperMap triangleSignedHalfPlaneMap_holomorphicOn

@[simp] theorem trianglePlaneUniformization_toHomeomorph :
    trianglePlaneUniformization.toHomeomorph = trianglePlaneUniformizationHomeomorph :=
  triangleSignedHalfPlaneMap.quotientBiholomorph_toHomeomorph
    triangleSignedHalfPlaneMap_isProperMap triangleSignedHalfPlaneMap_holomorphicOn

@[simp] theorem triangleSphereUniformization_toHomeomorph :
    triangleSphereUniformization.toHomeomorph = triangleSphereUniformizationHomeomorph :=
  triangleSignedHalfPlaneMap.compactifiedBiholomorph_toHomeomorph
    triangleSignedHalfPlaneMap_isProperMap triangleSignedHalfPlaneMap_holomorphicOn

@[simp] theorem triangleSphereUniformization_cusp :
    triangleSphereUniformization triangleCuspPoint = (∞ : RiemannSphere) := rfl

@[simp] theorem triangleSphereUniformization_openInclusion (q : TriangleOrbitSpace) :
    triangleSphereUniformization (triangleOpenInclusion q) =
      ((trianglePlaneUniformization q : ℂ) : RiemannSphere) := rfl

@[simp] theorem trianglePlaneUniformization_centerOne :
    trianglePlaneUniformization triangleOrbitCenterOne = 0 :=
  trianglePlaneUniformizationHomeomorph_centerOne

@[simp] theorem trianglePlaneUniformization_centerTwo :
    trianglePlaneUniformization triangleOrbitCenterTwo = 1 :=
  trianglePlaneUniformizationHomeomorph_centerTwo

@[simp] theorem triangleSphereUniformization_centerOne :
    triangleSphereUniformization (triangleOpenInclusion triangleOrbitCenterOne) =
      ((0 : ℂ) : RiemannSphere) :=
  triangleSphereUniformizationHomeomorph_centerOne

@[simp] theorem triangleSphereUniformization_centerTwo :
    triangleSphereUniformization (triangleOpenInclusion triangleOrbitCenterTwo) =
      ((1 : ℂ) : RiemannSphere) :=
  triangleSphereUniformizationHomeomorph_centerTwo

theorem trianglePlaneUniformization_projection {z : ℍ} (hz : z ∈ halfFordRegion) :
    trianglePlaneUniformization (triangleOrbitProjection z) = triangleSignedHalfPlaneMap z :=
  trianglePlaneUniformizationHomeomorph_projection hz

theorem triangleSphereUniformization_projection {z : ℍ} (hz : z ∈ halfFordRegion) :
    triangleSphereUniformization (triangleCompactifiedProjection z) =
      (triangleSignedHalfPlaneMap z : RiemannSphere) :=
  triangleSignedHalfPlaneMap.compactifiedBiholomorph_projection_half
    triangleSignedHalfPlaneMap_isProperMap triangleSignedHalfPlaneMap_holomorphicOn z hz

theorem triangleSphereUniformization_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleSphereUniformization :=
  triangleSphereUniformization.contMDiff

theorem triangleSphereUniformization_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleSphereUniformization.symm :=
  triangleSphereUniformization.symm.contMDiff

/-- All three normalizations hold for a constructed biholomorphism;
there is no remaining source-function or uniformization hypothesis. -/
theorem exists_normalized_triangle_sphere_biholomorph :
    ∃ π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω,
      π triangleCuspPoint = (∞ : RiemannSphere) ∧
      π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere) ∧
      π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere) :=
  ⟨triangleSphereUniformization, triangleSphereUniformization_cusp,
    triangleSphereUniformization_centerOne, triangleSphereUniformization_centerTwo⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
