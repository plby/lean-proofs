import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorBase

/-!
# The genuine finite coordinate on the regular base

The normalized sphere uniformization sends the actual regular quotient to
the complement of infinity, zero and one.  Its finite affine coordinate is
therefore holomorphic and locally biholomorphic.  Pulling this coordinate
back along the original regular quotient covering gives the actual invariant
function whose differential occurs in the regular canonical form.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open Triangle

attribute [local instance] triangleRegularQuotientChartedSpace triangleOrbitChartedSpace
  triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  triangleRegularQuotient_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

theorem regularBaseSphere_mem (q : TriangleRegularQuotient) :
    regularBaseSphere q ∈ sphereRegularPatch :=
  (sphereUniformization_mem_regular_iff (regularInclusion q)).mpr (regularInclusion_mem q)

theorem regularBaseSphere_ne_infty (q : TriangleRegularQuotient) :
    regularBaseSphere q ≠ (∞ : RiemannSphere) :=
  ((mem_sphereRegularPatch (regularBaseSphere q)).mp (regularBaseSphere_mem q)).1

/-- The original finite sphere coordinate of the actual regular base. -/
def baseCoordinate (q : TriangleRegularQuotient) : ℂ :=
  BetaTorsor.sphereFiniteCoordinate (regularBaseSphere q)

@[simp] theorem baseCoordinate_coe (q : TriangleRegularQuotient) :
    (baseCoordinate q : RiemannSphere) = regularBaseSphere q :=
  BetaTorsor.sphereFiniteCoordinate_coe_apply (regularBaseSphere_ne_infty q)

theorem baseCoordinate_ne_zero (q : TriangleRegularQuotient) : baseCoordinate q ≠ 0 := by
  intro h
  exact ((mem_sphereRegularPatch (regularBaseSphere q)).mp
    (regularBaseSphere_mem q)).2.1 ((baseCoordinate_coe q).symm.trans (congrArg
      (fun z : ℂ => (z : RiemannSphere)) h))

theorem baseCoordinate_ne_one (q : TriangleRegularQuotient) : baseCoordinate q ≠ 1 := by
  intro h
  exact ((mem_sphereRegularPatch (regularBaseSphere q)).mp
    (regularBaseSphere_mem q)).2.2 ((baseCoordinate_coe q).symm.trans (congrArg
      (fun z : ℂ => (z : RiemannSphere)) h))

/-- Both factors are genuine local biholomorphisms for the existing atlases. -/
theorem baseCoordinate_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω baseCoordinate := by
  intro q
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularToOrbit q :=
    (triangleRegularOrbitBiholomorph.isLocalDiffeomorph q).comp
      (K := 𝓘(ℂ)) (P := TriangleOrbitSpace)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) triangleOrbitRegularDomain
        (triangleRegularOrbitBiholomorph q))
  exact hreg.comp (K := 𝓘(ℂ)) (P := ℂ)
    ((BetaTorsor.finiteOrbitBiholomorph triangleSphereUniformization
      triangleSphereUniformization_cusp).isLocalDiffeomorph (triangleRegularToOrbit q))

theorem baseCoordinate_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω baseCoordinate :=
  baseCoordinate_isLocalDiffeomorph.contMDiff

/-- The same actual finite coordinate pulled back to the regular upper half-plane. -/
def upstairsCoordinate : TriangleRegularPoint → ℂ := baseCoordinate ∘ triangleRegularProject

@[simp] theorem upstairsCoordinate_apply (z : TriangleRegularPoint) :
    upstairsCoordinate z = baseCoordinate (triangleRegularProject z) := rfl

@[simp] theorem upstairsCoordinate_coe (z : TriangleRegularPoint) :
    (upstairsCoordinate z : RiemannSphere) =
      triangleSphereUniformization (triangleCompactifiedProjection z.val) :=
  baseCoordinate_coe (triangleRegularProject z)

theorem upstairsCoordinate_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω upstairsCoordinate := by
  intro z
  exact (triangleRegularProject_isLocalDiffeomorph z).comp (K := 𝓘(ℂ)) (P := ℂ)
    (baseCoordinate_isLocalDiffeomorph (triangleRegularProject z))

theorem upstairsCoordinate_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω upstairsCoordinate :=
  upstairsCoordinate_isLocalDiffeomorph.contMDiff

theorem upstairsCoordinate_ne_zero (z : TriangleRegularPoint) : upstairsCoordinate z ≠ 0 :=
  baseCoordinate_ne_zero (triangleRegularProject z)

theorem upstairsCoordinate_ne_one (z : TriangleRegularPoint) : upstairsCoordinate z ≠ 1 :=
  baseCoordinate_ne_one (triangleRegularProject z)

@[simp] theorem upstairsCoordinate_invariant (g : TriangleGroup) (z : TriangleRegularPoint) :
    upstairsCoordinate (g • z) = upstairsCoordinate z := by
  change baseCoordinate (triangleRegularProject (g • z)) = _
  rw [triangleRegularProject_covering.map_smul]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
