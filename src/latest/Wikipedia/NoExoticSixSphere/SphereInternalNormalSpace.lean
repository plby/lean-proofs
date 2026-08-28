import Wikipedia.NoExoticSixSphere.ManifoldSphereFrameOperator

/-!
# The actual internal normal space of a three-sphere in a six-manifold

This is the part of the original manifold tangent image perpendicular to the
actual sphere derivative. The original normal frame identifies it with the
orthogonal complement of the combined sphere-frame operator. Its dimension
is proved to be three, not imposed as a separate plane hypothesis.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

def sphereNormalSpace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Vector n) M] (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
    (s : Sphere 3) : Submodule ℝ (Vector e.ambientDimension) :=
  e.tangentImage (f s) ⊓ (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)

variable (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

include hf in
theorem sphereNormalSpace_eq_frameComplement (s : Sphere 3) :
    e.sphereNormalSpace f s = (e.sphereFrameOperator a f s).rangeᗮ := by
  rw [sphereFrameOperator, OperatorSum.range_operator, ← Submodule.inf_orthogonal,
    e.normalFrameOnSphere_range a f s,
    SphereThreeTangentFrame.range_framedDerivative (e.toFun ∘ f) (e.smooth.comp hf) s]
  change e.sphereNormalSpace f s =
    (e.tangentImage (f s))ᗮᗮ ⊓ (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ
  rw [Submodule.orthogonal_orthogonal]
  rfl

include a hf in
theorem finrank_sphereNormalSpace
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) (s : Sphere 3) :
    Module.finrank ℝ (e.sphereNormalSpace f s) = 3 := by
  rw [e.sphereNormalSpace_eq_frameComplement f a hf s]
  have h := (e.sphereFrameOperator a f s).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (e.injective_sphereFrameOperator a f hf hd s),
    finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
  have hN := e.dimension_le_ambient (f s)
  omega

end NoExoticSixSphere.EuclideanEmbedding
