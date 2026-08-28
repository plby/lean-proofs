import Wikipedia.NoExoticSixSphere.ManifoldSphereFrameOperator

/-!
# The twisted sphere operator is the actual collar operator

The factorization uses the retained radial collar directly, without a
spanning disk or global injectivity hypothesis. It therefore applies to
every smooth immersion used in the corrected geometric parity.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SpanningDiskFrameCoordinates

open GLOrthonormalization Stiefel StabilizedSpanningDisk SphereThreeTangentFrame

variable {N k : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
  (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)

include hf

theorem collarOperator_comp_sourceSphere (s : Sphere 3) (a : Vector k →L[ℝ] Vector N) :
    (OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ (collar b f) s.val)).comp
      (sourceSphere k s).toContinuousLinearMap =
        (targetCoordinates N).toContinuousLinearMap.comp
          ((BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))).comp
            (sourceShuffle k).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ (collar b f) s.val)
      (sourceSphere k s v) = targetCoordinates N
        (BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s)) (sourceShuffle k v))
  simp only [sourceSphere_apply, sourceShuffle_apply, OperatorSum.operator_apply,
    BlockSum.operator_apply, targetCoordinates_apply, targetExtra_apply,
    boundaryFrameOperator_apply, fderiv_collar_radialCoordinates b f hf,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [← map_add]
  congr 1
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem collarOperator_factorization (s : Sphere 3) (a : Vector k →L[ℝ] Vector N) :
    OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ (collar b f) s.val) =
      (targetCoordinates N).toContinuousLinearMap.comp
        ((BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))).comp
          (sourceTwist k s).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ (collar b f) s.val) v =
    targetCoordinates N (BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))
      (sourceTwist k s v))
  rw [sourceTwist_apply]
  have he := congrArg (fun A : Vector ((k + 5) + 4) →L[ℝ] Vector (N + 6) ↦
      A ((sourceSphere k s).symm v)) (collarOperator_comp_sourceSphere b f hf s a)
  change OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ (collar b f) s.val)
      (sourceSphere k s ((sourceSphere k s).symm v)) = targetCoordinates N
        (BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))
          (sourceShuffle k ((sourceSphere k s).symm v))) at he
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  exact he

end SpanningDiskFrameCoordinates

namespace EuclideanEmbedding

open GLOrthonormalization SpanningDiskFrameCoordinates StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

theorem twistedSphereFrame_collar (b : Sphere 3) (s : Sphere 3) :
    (twistedBlockMap (e.sphereFrameOperatorMap a f hf hd) s).val =
      OperatorSum.operator (boundaryFrameOperator (e.normalFrameOnSphere a f s).val)
        (fderiv ℝ (collar b (e.toFun ∘ f)) s.val) := by
  rw [twistedBlockMap_value]
  exact (collarOperator_factorization b (e.toFun ∘ f) (e.smooth.comp hf) s
    (e.normalFrameOnSphere a f s).val).symm

end EuclideanEmbedding
end NoExoticSixSphere
