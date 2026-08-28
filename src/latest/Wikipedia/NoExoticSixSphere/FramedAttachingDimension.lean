import Wikipedia.NoExoticSixSphere.FramedAttachingProduct

/-!
# The actual attaching tube determines the model-space dimension

Its native derivative is an isomorphism from the sphere and transverse
tangent spaces to the original manifold tangent space. Thus the transverse
dimension has the required relation to the manifold dimension. This relation
is proved from the actual tube, not supplied as an extra hypothesis.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

include A in
theorem sphere_transverse_dimension : 3 + (n - 3) = n := by
  have h := A.tube_localDiffeomorph (pole 3) 0 (mem_closedBall_self A.radius_pos.le)
  let D := h.mfderivToContinuousLinearEquiv (by simp)
  have hdim := D.toLinearEquiv.finrank_eq
  change Module.finrank ℝ (Vector 3 × Vector (n - 3)) = Module.finrank ℝ (Vector n) at hdim
  simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using hdim

include A in
theorem three_le_dimension : 3 ≤ n := by
  have h := A.sphere_transverse_dimension
  omega

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct
