import Wikipedia.NoExoticSixSphere.EmbeddedSpherePushOff
import Wikipedia.NoExoticSixSphere.GeometricIntersectionFundamentalClass

/-!
# Vanishing of the self-intersection of embedded three-spheres

The constructed disjoint push-off is genuinely homotopic to the original
sphere map. Geometric homotopy invariance therefore proves self-intersection
zero, and the standard fundamental-class comparison gives the same statement
for the native homology pairing. This does not assert that every middle
class has an embedded representative.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

section General

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

include a in
theorem sphereIntersectionNumber_self_of_embedding (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    sphereIntersectionNumber e r f f = 0 := by
  obtain ⟨g, hg, H, hdis⟩ := e.exists_disjoint_sphere_pushOff a r f hf hi hd
  exact (sphereIntersectionNumber_homotopic e r f f f g (ContinuousMap.Homotopic.refl f) H).trans
    (sphereIntersectionNumber_zero_of_disjoint e r f g hf hg hdis)

end General

theorem modTwoHomologyIntersection_self_of_embedding
    {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
    [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
    (e : EuclideanEmbedding 6 M)
    (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
    (m : M) [Subsingleton (π_ 2 M m)] (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    modTwoHomologyIntersection e r m
      (SixSphereMiddleParity.sphereClass f) (SixSphereMiddleParity.sphereClass f) = 0 := by
  rw [modTwoHomologyIntersection_standardSphereClass]
  exact sphereIntersectionNumber_self_of_embedding e a r f hf hi hd

end NoExoticSixSphere.EuclideanEmbedding
