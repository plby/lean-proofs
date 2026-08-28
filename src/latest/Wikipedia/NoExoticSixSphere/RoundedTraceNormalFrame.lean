import Wikipedia.NoExoticSixSphere.RoundedTraceDifferential
import Wikipedia.NoExoticSixSphere.RoundedTraceSmoothFrame
import Wikipedia.NoExoticSixSphere.RoundedTraceBoundary

/-!
# A full smooth normal frame on the actual closed rounded trace

The descended field spans the orthogonal complement of the actual global
inclusion differential at every point, including the boundary. This is a
normally framed closed embedded boundary manifold in the actual dimension,
without a global compactness assumption. Identifying its original
end as a boundary diffeomorphism and its role in framed surgery remain separate
geometric obligations.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem traceNormalFrame_range (p : ambientSet A) :
    (traceNormalFrame A p).range = (traceAmbientDerivative A p).rangeᗮ := by
  obtain ⟨i, hi⟩ := pieceDomain_covers A p
  let q : pieceDomain A i := ⟨p, hi⟩
  have h := pieceNormalFrame_range A i q
  rw [← traceNormalFrame_on_piece A i q, range_pieceAmbientDerivative] at h
  exact h

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
