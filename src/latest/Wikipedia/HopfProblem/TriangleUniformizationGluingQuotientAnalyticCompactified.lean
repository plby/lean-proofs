import Wikipedia.HopfProblem.TriangleUniformizationGluingQuotientAnalytic
import Wikipedia.HopfProblem.TriangleUniformizationGluingProper
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlasAgreement

/-!
# Holomorphicity on the actual compactified triangle curve

The old quotient and the cusp complement have their proved compatible
complex atlases. The actual compactified homeomorphism is holomorphic
there, by its finite-coordinate formula and the local analytic inverse
of the literal open inclusion. Continuity removes the single cusp.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

namespace SignedHalfPlaneMap

/-- Away from the actual cusp, the compactified homeomorphism is
holomorphic for the selected source atlas and the standard sphere atlas. -/
theorem compactifiedHomeomorph_holomorphicAt_of_ne_cusp (D : SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z))
    (hq : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap)
    {p : TriangleCompactifiedOrbitSpace} (hp : p ≠ triangleCuspPoint) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedHomeomorph hlocal) p := by
  obtain ⟨q, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
  have hfinite : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → RiemannSphere) :=
    RiemannSphere.standardCharts.affineMap_holomorphic false
  have hcomp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      ((D.compactifiedHomeomorph hlocal) ∘ triangleOpenInclusion) := by
    simpa only [Function.comp_def, D.compactifiedHomeomorph_openInclusion hlocal] using
      hfinite.comp hq
  have hi := triangleOpenInclusion_isLocalDiffeomorph q
  have h := hcomp.contMDiffAt.comp (triangleOpenInclusion q) hi.localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [hi.localInverse_eventuallyEq_right] with z hz
  change D.compactifiedHomeomorph hlocal z =
    D.compactifiedHomeomorph hlocal (triangleOpenInclusion (hi.localInverse z))
  rw [show triangleOpenInclusion (hi.localInverse z) = z from hz]

/-- The single cusp is removable in the already selected cusp atlas.
Thus the actual compactified homeomorphism is holomorphic everywhere. -/
theorem compactifiedHomeomorph_holomorphic (D : SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z))
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedHomeomorph hlocal) := by
  apply contMDiff_of_continuous_of_finite (D.compactifiedHomeomorph hlocal).continuous
    (Set.finite_singleton triangleCuspPoint)
  intro p hp
  exact D.compactifiedHomeomorph_holomorphicAt_of_ne_cusp hlocal
    (D.quotientMap_holomorphic hup) (by simpa only [Set.mem_singleton_iff] using hp)

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
