import Wikipedia.NoExoticSixSphere.ImmersedSphereRegularParity
import Wikipedia.NoExoticSixSphere.UnorderedSphereDoublePoints

/-!
# Frame parity corrected by the actual unordered double-point count

Both terms are evaluated on the given smooth immersion. For an embedding
the double-point term is empty, so this agrees exactly with geometric disk
parity. For self-transverse immersions the actual orbit set is finite.
Ordinary homotopy invariance, the quadratic identity, and descent to
homology are not asserted by this definition or the comparison below.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

def immersedSphereCorrectedParity : ZMod 2 :=
  e.immersedSphereFrameParity a f hf hd + SphereSelfIntersections.unorderedParity f

theorem immersedSphereCorrectedParity_eq_sphereParity (hi : Injective f) :
    e.immersedSphereCorrectedParity a f hf hd = e.sphereParity a f hf hi hd := by
  rw [immersedSphereCorrectedParity, SphereSelfIntersections.unorderedParity_zero_of_injective f hi,
    add_zero, immersedSphereFrameParity_eq_sphereParity e a f hf hd hi]

end NoExoticSixSphere.EuclideanEmbedding
