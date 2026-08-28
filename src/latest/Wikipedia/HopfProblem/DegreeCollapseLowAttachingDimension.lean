import Wikipedia.HopfProblem.DegreeCollapseLowAttachingTubeCoordinates

/-!

# The actual dimension of a low-dimensional attaching product

The native tube's invertible derivative identifies its actual sphere and
transverse tangent coordinates with the original seven-dimensional tangent
space. Thus the required dimension is a consequence of the supplied native
tube, not a new assumption or a replacement of its atlas.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

include A

theorem tube_dimension : d + (7 - d) = 7 := by
  have h0 : (0 : Vector (7 - d)) ∈ closedBall (0 : Vector (7 - d)) A.radius := by
    simpa only [mem_closedBall, dist_self] using A.radius_pos.le
  let L : (Vector d × Vector (7 - d)) ≃L[ℝ] Vector 7 :=
    (A.tube_localDiffeomorph (spherePole d) 0 h0).mfderivToContinuousLinearEquiv (by simp)
  have h := L.toLinearEquiv.finrank_eq
  simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using h

theorem sphere_dimension_le : d ≤ 7 := by
  have h := A.tube_dimension
  omega

theorem handle_dimension : (d + 1) + (7 - d) = 8 := by
  have h := A.tube_dimension
  omega

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
