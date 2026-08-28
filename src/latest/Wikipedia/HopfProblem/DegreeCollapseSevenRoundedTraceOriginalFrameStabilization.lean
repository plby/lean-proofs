import Wikipedia.HopfProblem.DegreeCollapseSevenInducedEndNormalFraming
import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalFrameStabilization

/-!
# The retained seven-dimensional end and its exact column permutation

The full induced frame is the original normal frame with six extra axes,
composed with the explicit permutation placing the height column last.
No reflection or column permutation is silently discarded.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem inducedBoundaryFrame_original_stabilization (m : M) :
    letI := boundaryChartedSpace A;
    inducedBoundaryFrame A (originalBoundaryDiffeomorph A m).val =
      (BlockSum.operator 6 (a.orthonormal m).val).comp
        (endColumnPermutation (e.ambientDimension - 7)).toContinuousLinearMap := by
  let := boundaryChartedSpace A
  rw [inducedBoundaryFrame_originalBoundary, append_heightUnit_eq_block]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
