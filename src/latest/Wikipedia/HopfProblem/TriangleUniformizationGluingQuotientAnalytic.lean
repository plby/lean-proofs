import Wikipedia.HopfProblem.TriangleUniformizationGluingProper
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph
import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovablePointsFinite

/-!
# Holomorphic descent to the actual triangle quotient atlas

The constructed quotient projection has local analytic inverses away
from its two elliptic orbits. These inverses descend holomorphicity of
the actual invariant upstairs map. Continuity then removes the finite
elliptic exceptional set in the existing complex-curve charts.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

namespace BoundaryMap

variable (D : BoundaryMap)

/-- Holomorphicity descends through the genuine local inverse of the
actual orbit projection, using the selected quotient atlas. -/
theorem quotientMap_holomorphicAt_of_not_elliptic
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) {q : TriangleOrbitSpace}
    (h₁ : q ≠ triangleOrbitCenterOne) (h₂ : q ≠ triangleOrbitCenterTwo) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap q := by
  obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective q
  have hp := triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic h₁ h₂
  have h := hup.contMDiffAt.comp (triangleOrbitProjection z) hp.localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with y hy
  change D.quotientMap y = D.quotientMap (triangleOrbitProjection (hp.localInverse y))
  rw [show triangleOrbitProjection (hp.localInverse y) = y from hy]

/-- Continuity removes the two elliptic orbits from the descended map's
holomorphicity statement in the actual quotient complex curve. -/
theorem quotientMap_holomorphic
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap := by
  apply contMDiff_of_continuous_of_finite D.quotientMap_continuous
    ((Set.finite_singleton triangleOrbitCenterTwo).insert triangleOrbitCenterOne)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
  exact D.quotientMap_holomorphicAt_of_not_elliptic hup hq.1 hq.2

end BoundaryMap

namespace SignedHalfPlaneMap

variable (D : SignedHalfPlaneMap)

theorem quotientMap_holomorphic
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap :=
  D.toBoundaryMap.quotientMap_holomorphic hup

/-- The actual quotient homeomorphism is holomorphic, without any
nonvanishing-derivative assumption. -/
theorem quotientHomeomorph_holomorphic
    (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z))
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.quotientHomeomorph hlocal) :=
  D.quotientMap_holomorphic hup

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
