import Wikipedia.NoExoticSixSphere.GeometricIntersectionNullhomotopy
import Wikipedia.NoExoticSixSphere.SpherePinchIntersectionCount
import Wikipedia.NoExoticSixSphere.SpherePinchTransversality

/-!
# Geometric intersection additivity for a smooth hemisphere pinch

The geometric number equals the actual mod-two count of each smooth
transverse pair. The native differential calculation and explicit
intersection-pair bijection therefore prove additivity for the actual
pinch map. Smoothness is supplied by local constancy of both inputs at the
common base value; that value must avoid the comparison map.

The local constancy, avoidance, and transversality hypotheses are explicit.
This file does not yet identify the pinch with native homotopy-group
addition or descend the pairing to homology.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections SphereFold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem finite_transverse_sphere_pairs_of_retraction (f k : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hk : ContMDiff (𝓡 3) (𝓡 6) ∞ k)
    (ht : ∀ x y, f x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) k y))) :
    (pairs f k).Finite :=
  (e.intersectionParity_eq_of_smooth_families r (fun _ ↦ f) (fun _ ↦ k)
    (hf.comp contMDiff_snd) (hk.comp contMDiff_snd) (fun _ _ ↦ ht)).1

theorem sphereIntersectionNumber_pinch (v : Sphere 3) (f g k : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hk : ContMDiff (𝓡 3) (𝓡 6) ∞ k) (hm : f (antipode v) ∉ range k)
    (hfk : ∀ x y, f x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) k y)))
    (hgk : ∀ x y, g x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) k y)))
    (m : M) {U : Set (Sphere 3)} (hU : IsOpen U) (hv : antipode v ∈ U)
    (hfU : EqOn f (fun _ ↦ m) U) (hgU : EqOn g (fun _ ↦ m) U) :
    sphereIntersectionNumber e r (pinch v f g hbase) k =
      sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k := by
  have hP := contMDiff_pinch v f g hbase hf hg m hU hv hfU hgU
  have htP := transverse_pinch v f g k hbase hf hg hm hfk hgk
  have hfinf := e.finite_transverse_sphere_pairs_of_retraction r f k hf hk hfk
  have hfing := e.finite_transverse_sphere_pairs_of_retraction r g k hg hk hgk
  rw [sphereIntersectionNumber_eq_parity e r (pinch v f g hbase) k hP hk htP,
    sphereIntersectionNumber_eq_parity e r f k hf hk hfk,
    sphereIntersectionNumber_eq_parity e r g k hg hk hgk]
  exact pinch_parity v f g hbase k hm hfinf hfing

end NoExoticSixSphere.EuclideanEmbedding
