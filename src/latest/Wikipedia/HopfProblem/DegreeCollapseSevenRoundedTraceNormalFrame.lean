import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceDifferential
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceSmoothFrame
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundary

/-!
# A full smooth normal frame on the actual compact rounded trace

The descended field spans the orthogonal complement of the actual global
inclusion differential at every point, including the boundary. This is a
normally framed compact embedded boundary manifold. Identifying its original
end as a boundary diffeomorphism and its role in framed surgery remain separate
geometric obligations.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem traceNormalFrame_range (p : ambientSet A) :
    (traceNormalFrame A p).range = (traceAmbientDerivative A p).rangeᗮ := by
  obtain ⟨i, hi⟩ := pieceDomain_covers A p
  let q : pieceDomain A i := ⟨p, hi⟩
  have h := pieceNormalFrame_range A i q
  rw [← traceNormalFrame_on_piece A i q, range_pieceAmbientDerivative] at h
  exact h

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
