import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph

/-!
# Actual stabilized framed comparisons with a fixed ambient translation

The point map retains a genuine constant offset. The full normal columns
are compared by fixed source and ambient isometries after ordinary
stabilization. Both independently supplied native manifold atlases remain
unchanged. No parity or bordism-invariance hypothesis is part of the data.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel

structure AffineStabilizedFramedDiffeomorph {n : ℕ} {M M' : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    [TopologicalSpace M'] [ChartedSpace (Vector n) M']
    (e : EuclideanEmbedding n M) (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
    (e' : EuclideanEmbedding n M')
    (a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel) where
  extra : ℕ
  ambient : Vector (e.ambientDimension + extra) ≃ₗᵢ[ℝ] Vector e'.ambientDimension
  offset : Vector e'.ambientDimension
  normal : Vector ((e.ambientDimension - n) + extra) ≃ₗᵢ[ℝ]
    Vector (e'.ambientDimension - n)
  diffeomorph : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M'
  embedding_eq : ∀ x, e'.toFun (diffeomorph x) =
    offset + ambient (appendZeroMap e.ambientDimension extra (e.toFun x))
  frame_eq : ∀ x v, a'.ambient (diffeomorph x) (normal v) =
    ambient (BlockSum.operator extra (a.ambient x) v)

namespace AffineStabilizedFramedDiffeomorph

variable {n : ℕ} {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [TopologicalSpace M'] [ChartedSpace (Vector n) M']
  {e : EuclideanEmbedding n M} {e' : EuclideanEmbedding n M'}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel}

def ofReverseNormal (k : ℕ) (D : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M')
    (J : Vector (e.ambientDimension + k) ≃ₗᵢ[ℝ] Vector e'.ambientDimension)
    (c : Vector e'.ambientDimension)
    (Q : Vector (e'.ambientDimension - n) ≃ₗᵢ[ℝ] Vector ((e.ambientDimension - n) + k))
    (he : ∀ x, e'.toFun (D x) = c + J (appendZeroMap e.ambientDimension k (e.toFun x)))
    (hf : ∀ x v, a'.ambient (D x) v = J (BlockSum.operator k (a.ambient x) (Q v))) :
    AffineStabilizedFramedDiffeomorph e a e' a' where
  extra := k
  ambient := J
  offset := c
  normal := Q.symm
  diffeomorph := D
  embedding_eq := he
  frame_eq x v := (hf x (Q.symm v)).trans
    (congrArg (fun w ↦ J (BlockSum.operator k (a.ambient x) w)) (Q.apply_symm_apply v))

end AffineStabilizedFramedDiffeomorph
end NoExoticSixSphere
