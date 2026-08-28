import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTracePieceFrames

/-!
# Smooth descent of the actual matching frame columns

Choose a piece at each point, then use exact agreement to prove that the
result equals the prescribed frame on every open piece. The global smooth
atlas therefore makes the resulting field smooth. Its normal-range proof
is supplied separately using the actual inclusion differential.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def traceNormalFrame (p : ambientSet A) :
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  pieceNormalFrame A ((openCover A).indexAt p).1 ((openCover A).indexAt p).2

theorem traceNormalFrame_on_piece (i : Piece) (p : pieceDomain A i) :
    traceNormalFrame A p.val = pieceNormalFrame A i p :=
  pieceNormalFrame_agree A _ i _ p rfl

theorem contMDiff_traceNormalFrame : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7))
      𝓘(ℝ, Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (traceNormalFrame A) := by
  let := traceChartedSpace A
  apply ((openCover A).contMDiff_iff_onPieces _).mpr
  intro i
  let := pieceAtlas A i
  intro p
  exact ((contMDiff_pieceNormalFrame A i) p).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (traceNormalFrame_on_piece A i))

theorem traceNormalFrame_norm (p : ambientSet A)
    (v : Vector ((e.ambientDimension - 7) + 5)) : ‖traceNormalFrame A p v‖ = ‖v‖ :=
  pieceNormalFrame_norm A ((openCover A).indexAt p).1 ((openCover A).indexAt p).2 v

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
