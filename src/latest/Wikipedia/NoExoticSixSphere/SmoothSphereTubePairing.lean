import Wikipedia.NoExoticSixSphere.SmoothSphereTubeFiniteEvaluation
import Wikipedia.NoExoticSixSphere.OpenSphereTubeEvaluation

/-!
# Original cap pairing equals actual intersection parity for a smooth tube core

The original cap-evaluation formula and the proved transverse local
contributions now identify the pairing with the actual source-pair
count. No replacement pairing is introduced. This comparison currently
uses a genuine embedded first sphere with a whole-source smooth tube;
it does not yet cover arbitrary immersed first representatives.
-/

noncomputable section

open Set Function
open Wikipedia.HopfProblem SphereHomologyCoefficients
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SmoothSphereTube

open SphereNormalCapNormalization

attribute [local instance] SphereNormalCapNormalization.ambientDimension

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace AmbientVector M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 3)) (𝓡 6) (Sphere 3 × NormalVector) M ∞)
  (hsource : Φ.source = univ) (f : Sphere 3 → M) (hcore : ∀ s, Φ (s, 0) = f s)
  (g : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
  (ht : ∀ x y, f x = g y → Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
    (mfderiv (𝓡 3) (𝓡 6) g y))) (m : M) [Subsingleton (π_ 2 M m)]

include Φ hsource hcore hg ht in
/-- The original cap pairing on the original sphere classes is the actual transverse pair count. -/
theorem pairing_eq_intersection_parity :
    MiddleCapEvaluation.pairing (E := AmbientVector) m
      (modHomologyMap 2 (⟨f, hf.continuous⟩ : C(Sphere 3, M)) 3 (unitSphereModTopClass 2 2))
      (modHomologyMap 2 g 3 (unitSphereModTopClass 2 2)) = MapIntersections.parity f g := by
  have hc : OpenSphereTubeCap.core (tube Φ hsource) = (⟨f, hf.continuous⟩ : C(Sphere 3, M)) :=
    ContinuousMap.ext hcore
  have hp := OpenSphereTubeCap.pairing_core_sphere_supported
    (tube Φ hsource) (isOpenEmbedding_tube Φ hsource) m g
  rw [hc] at hp
  exact hp.trans (value_supportedPullback_eq_parity Φ hsource f hcore g hf hg ht)

end NoExoticSixSphere.SmoothSphereTube
