import Wikipedia.HopfProblem.DegreeCollapseFramedCoreImmersion
import Wikipedia.NoExoticSixSphere.GeometricSphereParityNullhomotopy
import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass

/-!
# Compare geometric and derivative parity using actual framed spheres

For two full framed sphere cores, the difference of geometric parities is
the difference of their untwisted derivative parities. For a two-connected
target, an actual zero integral sphere class is nullhomotopic and has zero
geometric parity. These facts allow a common zero-class representative to
fix the possible source-twist offset without assigning that twist a value.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open SmoothCube Wikipedia.SmoothSixDPoincare SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

theorem geometricParity_sum_eq_derivative_faces
    (B C : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M) :
    e.geometricSphereParity a r (FramedSurgery.coreMap (E := Vector 4) B) +
      e.geometricSphereParity a r (FramedSurgery.coreMap (E := Vector 4) C) =
    e.sphereDerivativeParity a (FramedSurgery.coreMap (E := Vector 4) B)
      (FramedSurgery.contMDiff_coreMap (E := Vector 4) B) (FramedCore.injective_core_derivative B) +
    e.sphereDerivativeParity a (FramedSurgery.coreMap (E := Vector 4) C)
      (FramedSurgery.contMDiff_coreMap (E := Vector 4) C) (FramedCore.injective_core_derivative C) := by
  have hB := FramedSurgery.contMDiff_coreMap (E := Vector 4) B
  have hC := FramedSurgery.contMDiff_coreMap (E := Vector 4) C
  have hdB := FramedCore.injective_core_derivative B
  have hdC := FramedCore.injective_core_derivative C
  have hiB := FramedCore.injective_core B
  have hiC := FramedCore.injective_core C
  have h := e.immersedSphereFrameParity_sum_eq_derivativeParity a
    (FramedSurgery.coreMap (E := Vector 4) B) (FramedSurgery.coreMap (E := Vector 4) C)
    hB hC hdB hdC
  rw [e.immersedSphereFrameParity_eq_sphereParity a _ hB hdB hiB,
    e.immersedSphereFrameParity_eq_sphereParity a _ hC hdC hiC,
    ← e.geometricSphereParity_eq_of_embedding a r _ hB hiB hdB,
    ← e.geometricSphereParity_eq_of_embedding a r _ hC hiC hdC] at h
  exact h

theorem geometricParity_zero_of_integral_class [SimplyConnectedSpace M]
    (m : M) [Subsingleton (π_ 2 M m)] (g : C(Sphere 3, M))
    (hg : integralSphereClass g = 0) : e.geometricSphereParity a r g = 0 := by
  apply e.geometricSphereParity_zero_of_nullhomotopic a r g m
  apply (integralSphereClass_eq_iff_homotopic m g (ContinuousMap.const _ m)).mp
  exact hg.trans (integralSphereClass_const m).symm

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
