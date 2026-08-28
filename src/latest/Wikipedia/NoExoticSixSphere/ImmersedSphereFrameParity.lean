import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity
import Wikipedia.NoExoticSixSphere.ManifoldSphereFrameOperator

/-!
# The actual frame obstruction of an immersed three-sphere

The original derivative and manifold normal frame determine the same
twisted stabilized operator as for an embedded sphere. Its actual frame
parity is defined without a spanning disk or global injectivity. For an
embedding it agrees with the already constructed geometric disk parity.
No invariance under arbitrary homotopy of the underlying immersion is
asserted: singularities can change this frame obstruction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary SpanningDiskFrameCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

def immersedSphereFrameParity : ZMod 2 :=
  Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 7)
    (by have h := e.dimension_le_ambient (f (Stiefel.pole 3)); omega) (by omega)
    (twistedBlockMap (e.sphereFrameOperatorMap a f hf hd))

theorem immersedSphereFrameParity_zero_iff :
    e.immersedSphereFrameParity a f hf hd = 0 ↔
      Extends (twistedBlockMap (e.sphereFrameOperatorMap a f hf hd)) :=
  Monomorphism.sphereParityOfDimension_zero_iff _ _ _ _

theorem immersedSphereFrameParity_eq_sphereParity (hi : Injective f) :
    e.immersedSphereFrameParity a f hf hd = e.sphereParity a f hf hi hd := by
  apply zmodTwo_eq_of_zero_iff
  rw [immersedSphereFrameParity_zero_iff, sphereParity_zero_iff_twisted_extension]

theorem immersedSphereFrameParity_eq_of_frameHomotopic
    (g : Sphere 3 → M) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s))
    (H : (e.sphereFrameOperatorMap a f hf hd).Homotopic
      (e.sphereFrameOperatorMap a g hg hgd)) :
    e.immersedSphereFrameParity a f hf hd = e.immersedSphereFrameParity a g hg hgd :=
  Monomorphism.sphereParityOfDimension_homotopic _ _ _ (twistedBlockMap_homotopic H)

theorem immersedSphereFrameParity_congr {g : Sphere 3 → M} (hfg : f = g)
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) :
    e.immersedSphereFrameParity a f hf hd = e.immersedSphereFrameParity a g hg hgd := by
  subst g
  rfl

end NoExoticSixSphere.EuclideanEmbedding
