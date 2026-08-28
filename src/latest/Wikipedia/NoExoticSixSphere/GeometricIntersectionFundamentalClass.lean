import Wikipedia.NoExoticSixSphere.SphereHurewiczFundamentalClass
import Wikipedia.NoExoticSixSphere.SmoothSphereBasepointAdjustment
import Wikipedia.NoExoticSixSphere.ModHomologyHomotopy
import Wikipedia.NoExoticSixSphere.SixSphereMiddleParity

/-!
# Geometric intersection on the standard fundamental classes

The pairing evaluates to the actual intersection number for arbitrary
continuous sphere maps, not only maps taking the sphere pole to a chosen
basepoint. Moving that value along an actual path gives based maps without
changing either the native homology class or the geometric count.
Consequently the pairing does not depend on the target basepoint.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SphereHomologyCoefficients

namespace SixSphereMiddleParity

variable {M : Type} [TopologicalSpace M]

theorem sphereClass_homotopic {f g : C(Sphere 3, M)} (H : f.Homotopic g) :
    sphereClass f = sphereClass g := by
  unfold sphereClass
  rw [modHomologyMap_homotopic 2 H 3]

end SixSphereMiddleParity

namespace EuclideanEmbedding

open GLOrthonormalization SmoothCube

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)
  (m : M) [h₂ : Subsingleton (π_ 2 M m)]

theorem modTwoHomologyIntersection_standardBasedClass (f g : BasedMap 3 M m) :
    modTwoHomologyIntersection e r m
        (SixSphereMiddleParity.sphereClass f.val) (SixSphereMiddleParity.sphereClass g.val) =
      sphereIntersectionNumber e r f.val g.val := by
  change modTwoHomologyIntersection e r m
    (modHomologyMap 2 f.val 3 (unitSphereModTopClass 2 2))
    (modHomologyMap 2 g.val 3 (unitSphereModTopClass 2 2)) = _
  rw [← modTwoSphereClass_eq_standard f, ← modTwoSphereClass_eq_standard g]
  exact modTwoHomologyIntersection_sphereClass e r m f g

theorem modTwoHomologyIntersection_standardSphereClass (f g : C(Sphere 3, M)) :
    modTwoHomologyIntersection e r m
        (SixSphereMiddleParity.sphereClass f) (SixSphereMiddleParity.sphereClass g) =
      sphereIntersectionNumber e r f g := by
  obtain ⟨F, hF⟩ := exists_based_map_homotopic (by decide : 0 < 3) f m
  obtain ⟨G, hG⟩ := exists_based_map_homotopic (by decide : 0 < 3) g m
  rw [SixSphereMiddleParity.sphereClass_homotopic hF,
    SixSphereMiddleParity.sphereClass_homotopic hG]
  exact (modTwoHomologyIntersection_standardBasedClass e r m F G).trans
    (sphereIntersectionNumber_homotopic e r f F.val g G.val hF hG).symm

theorem modTwoHomologyIntersection_basepoint_independent
    (m' : M) [Subsingleton (π_ 2 M m')] :
    modTwoHomologyIntersection e r m = modTwoHomologyIntersection e r m' := by
  apply modTwoHomologyIntersection_unique e r m'
  intro f g
  rw [modTwoSphereClass_eq_standard f, modTwoSphereClass_eq_standard g]
  exact modTwoHomologyIntersection_standardSphereClass e r m f.val g.val

include m h₂ in
theorem sphereIntersectionNumber_eq_of_homologyClass_eq
    (f f' g g' : C(Sphere 3, M))
    (hf : SixSphereMiddleParity.sphereClass f = SixSphereMiddleParity.sphereClass f')
    (hg : SixSphereMiddleParity.sphereClass g = SixSphereMiddleParity.sphereClass g') :
    sphereIntersectionNumber e r f g = sphereIntersectionNumber e r f' g' := by
  rw [← modTwoHomologyIntersection_standardSphereClass e r m f g,
    ← modTwoHomologyIntersection_standardSphereClass e r m f' g', hf, hg]

end EuclideanEmbedding

end NoExoticSixSphere
