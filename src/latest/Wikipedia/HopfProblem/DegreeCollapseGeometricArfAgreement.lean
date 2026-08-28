import Wikipedia.HopfProblem.DegreeCollapseGeometricArfDefined
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant

/-!
# Agreement of the two constructions of the actual geometric Arf invariant

Both definitions use the same original quadratic form and canonical finite
homology type. They differ only in the proof of polar nondegeneracy, so
proof irrelevance identifies them without a geometric comparison premise.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem actualGeometricArf_eq_invariant :
    actualGeometricArf e a r m = GeometricArf.invariant e a r m := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
