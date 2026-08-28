import Wikipedia.HopfProblem.TriangleUniformizationGluingHolomorphic
import Wikipedia.HopfProblem.TriangleUniformizationGluingQuotientAnalyticCompactified
import Wikipedia.HopfProblem.TriangleUniformizationGluingInverseManifold
import Wikipedia.HopfProblem.TriangleUniformizationGluingData

/-!
# Analytic gluing on the actual triangle quotient and its cusp compactification

An actual signed closed-half-plane map, proper on the closed half-Ford
triangle and holomorphic on its interior, constructs biholomorphisms
from the actual full triangle orbit curve to `ℂ` and from its existing
cusp compactification to the standard Riemann sphere.

The tiling, boundary orbit identifications, continuous descent, properness,
edge removal, elliptic/cusp point removal, and holomorphic inverse are all
proved in the imported construction.  None is a hypothesis about a
desired global map, and neither complex atlas is transported along the
resulting equivalence.  Instantiating the input half-plane map from the
normalized half-triangle Riemann map is a separate concrete application.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

namespace SignedHalfPlaneMap

variable (D : SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) halfFordInterior)

/-- The actual full triangle orbit curve, including its elliptic points,
is biholomorphic to the complex plane for its previously constructed atlas. -/
def quotientBiholomorph : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω :=
  biholomorphOfHomeomorph (D.quotientHomeomorph hlocal)
    (D.quotientHomeomorph_holomorphic hlocal (D.upstairsMap_holomorphic hd))

/-- The actual filled cusp curve is biholomorphic to the standard
Riemann sphere, with both prescribed analytic atlases unchanged. -/
def compactifiedBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω :=
  biholomorphOfHomeomorph (D.compactifiedHomeomorph hlocal)
    (D.compactifiedHomeomorph_holomorphic hlocal (D.upstairsMap_holomorphic hd))

@[simp] theorem quotientBiholomorph_apply (q : TriangleOrbitSpace) :
    D.quotientBiholomorph hlocal hd q = D.quotientMap q := rfl

@[simp] theorem quotientBiholomorph_toHomeomorph :
    (D.quotientBiholomorph hlocal hd).toHomeomorph = D.quotientHomeomorph hlocal :=
  biholomorphOfHomeomorph_toHomeomorph _ _

@[simp] theorem compactifiedBiholomorph_toHomeomorph :
    (D.compactifiedBiholomorph hlocal hd).toHomeomorph = D.compactifiedHomeomorph hlocal :=
  biholomorphOfHomeomorph_toHomeomorph _ _

theorem quotientBiholomorph_projection (z : ℍ) (hz : z ∈ fordRegion) :
    D.quotientBiholomorph hlocal hd (triangleOrbitProjection z) = D.foldedFordMap z :=
  D.toBoundaryMap.quotientMap_projection z hz

@[simp] theorem compactifiedBiholomorph_cusp :
    D.compactifiedBiholomorph hlocal hd triangleCuspPoint = (∞ : RiemannSphere) := rfl

@[simp] theorem compactifiedBiholomorph_openInclusion (q : TriangleOrbitSpace) :
    D.compactifiedBiholomorph hlocal hd (triangleOpenInclusion q) =
      (D.quotientBiholomorph hlocal hd q : RiemannSphere) := rfl

theorem compactifiedBiholomorph_projection (z : ℍ) (hz : z ∈ fordRegion) :
    D.compactifiedBiholomorph hlocal hd (triangleCompactifiedProjection z) =
      (D.foldedFordMap z : RiemannSphere) :=
  D.compactifiedHomeomorph_projection hlocal z hz

/-- On the original closed half-triangle, the result is exactly the
supplied normalized finite map, including its boundary values. -/
theorem compactifiedBiholomorph_projection_half (z : ℍ) (hz : z ∈ halfFordRegion) :
    D.compactifiedBiholomorph hlocal hd (triangleCompactifiedProjection z) =
      (D.toFun z : RiemannSphere) := by
  rw [D.compactifiedBiholomorph_projection hlocal hd z hz.1]
  exact congrArg (fun w : ℂ => (w : RiemannSphere))
    (D.toBoundaryMap.foldedFordMap_of_left hz.2)

theorem compactifiedBiholomorph_eq_infty_iff (q : TriangleCompactifiedOrbitSpace) :
    D.compactifiedBiholomorph hlocal hd q = (∞ : RiemannSphere) ↔ q = triangleCuspPoint :=
  D.compactifiedHomeomorph_eq_infty_iff hlocal q

theorem quotientBiholomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.quotientBiholomorph hlocal hd) :=
  (D.quotientBiholomorph hlocal hd).contMDiff

theorem quotientBiholomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.quotientBiholomorph hlocal hd).symm :=
  (D.quotientBiholomorph hlocal hd).symm.contMDiff

theorem compactifiedBiholomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedBiholomorph hlocal hd) :=
  (D.compactifiedBiholomorph hlocal hd).contMDiff

theorem compactifiedBiholomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedBiholomorph hlocal hd).symm :=
  (D.compactifiedBiholomorph hlocal hd).symm.contMDiff

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
