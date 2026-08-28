import Wikipedia.NoExoticSixSphere.AffineStabilizedSphereFrameComparison
import Wikipedia.NoExoticSixSphere.StabilizedSphereParity

/-!
# Original sphere parity under an affine stabilized framed comparison

The proved full raw-operator identity transports the original twisted
disk-extension condition through fixed source and ambient isometries and
ordinary stabilization. The constant point-map translation has already
been removed by differentiation, not by changing the actual embedding.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AffineStabilizedFramedDiffeomorph

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates DiskBoundary
open DiffeomorphSphereComposition

variable {M M' : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [TopologicalSpace M'] [ChartedSpace (Vector 6) M']
  {e : EuclideanEmbedding 6 M} {e' : EuclideanEmbedding 6 M'}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 6) e'.normalProjection e'.NormalModel}
  (F : AffineStabilizedFramedDiffeomorph e a e' a')
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

theorem raw_twisted_extension_iff :
    Extends (twistedBlockMap (e'.rawSphereFrameOperatorMap a' (F.diffeomorph ∘ f)
      (smooth F.diffeomorph f hf) (mfderiv_injective F.diffeomorph f hf hd))) ↔
    Extends (twistedBlockMap (e.rawSphereFrameOperatorMap a f hf hd)) := by
  have hdim := e.dimension_le_ambient (f (pole 3))
  have hN : e.ambientDimension = (e.ambientDimension - 6) + 6 := by omega
  have hs := NormalFrameSourceCoordinates.extends_twisted_sourceChange_iff
    F.normal.toContinuousLinearEquiv
    (e'.rawSphereFrameOperatorMap a' (F.diffeomorph ∘ f)
      (smooth F.diffeomorph f hf) (mfderiv_injective F.diffeomorph f hf hd))
  have ht := NormalFrameAmbientCoordinates.extends_twisted_targetChange_iff
    F.ambient.toContinuousLinearEquiv
    ((NormalFrameStabilization.map F.extra).comp (e.rawSphereFrameOperatorMap a f hf hd))
  have hb := NormalFrameStabilization.extends_twisted_stabilization_iff hN F.extra
    (e.rawSphereFrameOperatorMap a f hf hd)
  have he := congrArg Extends
    (congrArg twistedBlockMap (F.rawSphereFrameOperatorMap_comp f hf hd))
  exact hs.symm.trans (he.to_iff.trans (ht.trans hb))

theorem sphereParity_comp (hi : Injective f) :
    e'.sphereParity a' (F.diffeomorph ∘ f) (smooth F.diffeomorph f hf)
        (injective F.diffeomorph f hi) (mfderiv_injective F.diffeomorph f hf hd) =
      e.sphereParity a f hf hi hd := by
  apply zmodTwo_eq_of_zero_iff
  have ht := e'.sphereParity_zero_iff_raw_twisted_extension a' (F.diffeomorph ∘ f)
    (smooth F.diffeomorph f hf) (mfderiv_injective F.diffeomorph f hf hd)
    (injective F.diffeomorph f hi)
  have hs := e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi
  exact ht.trans ((F.raw_twisted_extension_iff f hf hd).trans hs.symm)

end NoExoticSixSphere.AffineStabilizedFramedDiffeomorph
