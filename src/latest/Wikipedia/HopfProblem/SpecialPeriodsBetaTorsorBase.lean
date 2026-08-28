import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCoverSphere
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlasAgreement

/-!
# The finite coordinate of a supplied normalized triangle uniformization

A supplied biholomorphism from the actual compact triangle quotient to the
Riemann sphere, taking its actual cusp to infinity, gives a biholomorphism
from the original orbit quotient to the complex plane.  Composing with the
actual orbit projection constructs the holomorphic, surjective, invariant
finite coordinate upstairs.  No local section of an affine torsor is part
of this construction.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

/-- The actual finite affine coordinate on the standard analytic sphere. -/
def sphereFiniteCoordinate : RiemannSphere → ℂ :=
  (RiemannSphere.standardCharts.parametrization false).symm

@[simp] theorem sphereFiniteCoordinate_coe (z : ℂ) :
    sphereFiniteCoordinate (z : RiemannSphere) = z :=
  RiemannSphere.standardCharts.parametrization_symm_apply false z

theorem sphereFiniteCoordinate_mem_source {q : RiemannSphere} (hq : q ≠ (∞ : RiemannSphere)) :
    q ∈ (RiemannSphere.standardCharts.parametrization false).target := by
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hq
  exact ⟨z, Set.mem_univ z, rfl⟩

theorem sphereFiniteCoordinate_coe_apply {q : RiemannSphere} (hq : q ≠ (∞ : RiemannSphere)) :
    (sphereFiniteCoordinate q : RiemannSphere) = q :=
  (RiemannSphere.standardCharts.parametrization false).right_inv
    (sphereFiniteCoordinate_mem_source hq)

theorem sphereFiniteCoordinate_holomorphicAt {q : RiemannSphere}
    (hq : q ≠ (∞ : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereFiniteCoordinate q := by
  apply contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (mem_range_self false))
  exact sphereFiniteCoordinate_mem_source hq

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The finite coordinate of an actual orbit, through the supplied sphere map. -/
def finiteOrbitCoordinate (q : TriangleOrbitSpace) : ℂ :=
  sphereFiniteCoordinate (π (triangleOpenInclusion q))

/-- The finite upstairs projection is the coordinate of the actual orbit. -/
def finiteProjection (z : ℍ) : ℂ := finiteOrbitCoordinate π (triangleOrbitProjection z)

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

theorem finiteOrbitCoordinate_target_ne_infty (q : TriangleOrbitSpace) :
    π (triangleOpenInclusion q) ≠ (∞ : RiemannSphere) := by
  intro h
  exact triangleOpenInclusion_ne_cusp q (π.injective (h.trans hπ.symm))

theorem finiteOrbitCoordinate_coe (q : TriangleOrbitSpace) :
    (finiteOrbitCoordinate π q : RiemannSphere) = π (triangleOpenInclusion q) :=
  sphereFiniteCoordinate_coe_apply (finiteOrbitCoordinate_target_ne_infty π hπ q)

theorem finiteOrbitCoordinate_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteOrbitCoordinate π) := by
  intro q
  exact (sphereFiniteCoordinate_holomorphicAt
    (finiteOrbitCoordinate_target_ne_infty π hπ q)).comp q
      ((π.contMDiff.comp triangleOpenInclusion_holomorphic) q)

theorem finiteOrbitCoordinate_injective : Function.Injective (finiteOrbitCoordinate π) := by
  intro q r h
  apply OnePoint.coe_injective
  apply π.injective
  exact (finiteOrbitCoordinate_coe π hπ q).symm.trans
    ((congrArg (fun z : ℂ => (z : RiemannSphere)) h).trans
      (finiteOrbitCoordinate_coe π hπ r))

/-- The actual inverse finite coordinate, with its value in the original quotient. -/
def finiteOrbitInverse (z : ℂ) : TriangleOrbitSpace :=
  triangleOpenComplementBiholomorph.symm
    ⟨MuTorsor.Cover.finiteInverse π z, MuTorsor.Cover.finiteInverse_ne_cusp π hπ z⟩

theorem openInclusion_finiteOrbitInverse (z : ℂ) :
    triangleOpenInclusion (finiteOrbitInverse π hπ z) = MuTorsor.Cover.finiteInverse π z :=
  triangleOpenComplementBiholomorph_symm_apply _

theorem finiteOrbitInverse_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteOrbitInverse π hπ) := by
  have hcod : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ => (⟨MuTorsor.Cover.finiteInverse π z,
        MuTorsor.Cover.finiteInverse_ne_cusp π hπ z⟩ : triangleCuspComplement)) := by
    intro z
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
      (MuTorsor.Cover.finiteInverse_holomorphic π z)
  exact triangleOpenComplementBiholomorph.symm.contMDiff.comp hcod

@[simp] theorem finiteOrbitCoordinate_inverse (z : ℂ) :
    finiteOrbitCoordinate π (finiteOrbitInverse π hπ z) = z := by
  apply OnePoint.coe_injective
  rw [finiteOrbitCoordinate_coe π hπ, openInclusion_finiteOrbitInverse,
    MuTorsor.Cover.apply_finiteInverse]

@[simp] theorem finiteOrbitInverse_coordinate (q : TriangleOrbitSpace) :
    finiteOrbitInverse π hπ (finiteOrbitCoordinate π q) = q :=
  finiteOrbitCoordinate_injective π hπ (finiteOrbitCoordinate_inverse π hπ _)

/-- The supplied compact sphere identification restricts to an actual
biholomorphism of the original quotient with the finite complex plane. -/
def finiteOrbitBiholomorph : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω where
  toEquiv :=
    { toFun := finiteOrbitCoordinate π
      invFun := finiteOrbitInverse π hπ
      left_inv := finiteOrbitInverse_coordinate π hπ
      right_inv := finiteOrbitCoordinate_inverse π hπ }
  contMDiff_toFun := finiteOrbitCoordinate_holomorphic π hπ
  contMDiff_invFun := finiteOrbitInverse_holomorphic π hπ

theorem finiteProjection_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteProjection π) :=
  (finiteOrbitCoordinate_holomorphic π hπ).comp triangleOrbitProjection_holomorphic

theorem finiteProjection_surjective : Function.Surjective (finiteProjection π) := by
  intro z
  obtain ⟨a, ha⟩ := triangleOrbitProjection_surjective (finiteOrbitInverse π hπ z)
  exact ⟨a, by simp only [finiteProjection, ha, finiteOrbitCoordinate_inverse]⟩

omit hπ in
theorem finiteProjection_invariant (g : TriangleGroup) (z : ℍ) :
    finiteProjection π (triangleGeometricRepresentation g z) = finiteProjection π z := by
  simp only [finiteProjection, triangleOrbitProjection_smul]

theorem finiteProjection_eq_iff (z w : ℍ) :
    finiteProjection π z = finiteProjection π w ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g w = z :=
  (finiteOrbitCoordinate_injective π hπ).eq_iff.trans (triangleOrbitProjection_eq_iff z w)

theorem finiteInverse_finiteProjection (z : ℍ) :
    MuTorsor.Cover.finiteInverse π (finiteProjection π z) =
      triangleCompactifiedProjection z := by
  apply π.injective
  change π (MuTorsor.Cover.finiteInverse π (finiteProjection π z)) =
    π (triangleCompactifiedProjection z)
  rw [MuTorsor.Cover.apply_finiteInverse]
  exact finiteOrbitCoordinate_coe π hπ (triangleOrbitProjection z)

theorem finiteProjection_mem_pullback
    (V : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace) (z : ℍ) :
    finiteProjection π z ∈ MuTorsor.Cover.finitePullback π V ↔
      triangleCompactifiedProjection z ∈ V := by
  rw [MuTorsor.Cover.mem_finitePullback, finiteInverse_finiteProjection π hπ]

/-- Pull an actual locally holomorphic function on the quotient back to
the genuine finite complex coordinate. -/
theorem analyticOnNhd_finite_pullback (U : TopologicalSpace.Opens TriangleOrbitSpace)
    {f : TriangleOrbitSpace → ℂ} (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f U) :
    AnalyticOnNhd ℂ (f ∘ finiteOrbitInverse π hπ)
      (finiteOrbitInverse π hπ ⁻¹' (U : Set TriangleOrbitSpace)) := by
  intro z hz
  have hh := hf.contMDiffAt (U.isOpen.mem_nhds hz)
  exact (hh.comp z (finiteOrbitInverse_holomorphic π hπ z)).contDiffAt.analyticAt

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
