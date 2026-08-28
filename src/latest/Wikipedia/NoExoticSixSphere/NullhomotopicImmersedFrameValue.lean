import Wikipedia.NoExoticSixSphere.GeometricSphereParityNullhomotopy
import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates

/-!
# Frame parity of an actual nullhomotopic self-transverse immersion

The already checked corrected-parity invariant vanishes on a specified
nullhomotopy. Thus the source-twisted frame value equals the actual unordered
double-point count. The ordinary untwisted derivative-frame value is not
identified with that count.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

include r in
theorem immersedSphereFrameParity_eq_unordered_of_nullhomotopic
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : NativeSphereSelfTransverse f) (p : M)
    (H : f.Homotopic (ContinuousMap.const _ p)) :
    e.immersedSphereFrameParity ν f hf hi = SphereSelfIntersections.unorderedParity f := by
  have hz := e.geometricSphereParity_zero_of_nullhomotopic ν r f p H
  have he := e.geometricSphereParity_eq_representative ν r f f hf hi
    ((nativeSphereSelfTransverse_iff _).mp ht) (ContinuousMap.Homotopic.refl f)
  rw [he] at hz
  change e.immersedSphereFrameParity ν f hf hi +
    SphereSelfIntersections.unorderedParity f = 0 at hz
  simpa only [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left hz

end NoExoticSixSphere.EuclideanEmbedding
