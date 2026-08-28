import Wikipedia.NoExoticSixSphere.RoundedTraceOutwardNormalOverlaps

/-! # The global smooth unit outward normal of the actual native boundary -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def outwardNormal (p : Boundary A) : Vector (e.ambientDimension + 6) :=
  pieceOutwardNormal A ((boundaryOpenCover A).indexAt p).1 ((boundaryOpenCover A).indexAt p).2

theorem outwardNormal_on_piece (i : Piece) (p : boundaryPieceDomain A i) :
    outwardNormal A p.val = pieceOutwardNormal A i p :=
  pieceOutwardNormal_agree A _ i _ p rfl

theorem contMDiff_outwardNormal : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (outwardNormal A) := by
  let := boundaryChartedSpace A
  apply ((boundaryOpenCover A).contMDiff_iff_onPieces _).mpr
  intro i
  let := boundaryPieceAtlas A i
  have he : (fun p : boundaryPieceDomain A i ↦ outwardNormal A p.val) = pieceOutwardNormal A i :=
    funext (outwardNormal_on_piece A i)
  rw [he]
  exact contMDiff_pieceOutwardNormal A i

theorem norm_outwardNormal (p : Boundary A) : ‖outwardNormal A p‖ = 1 :=
  norm_pieceOutwardNormal A ((boundaryOpenCover A).indexAt p).1 ((boundaryOpenCover A).indexAt p).2

theorem outwardNormal_mem_boundaryNormal (p : Boundary A) :
    outwardNormal A p ∈ (boundaryAmbientDerivative A p).rangeᗮ :=
  pieceOutwardNormal_mem_boundaryNormal A
    ((boundaryOpenCover A).indexAt p).1 ((boundaryOpenCover A).indexAt p).2

theorem outwardNormal_mem_trace (p : Boundary A) :
    outwardNormal A p ∈ (traceAmbientDerivative A p.val).range :=
  pieceOutwardNormal_mem_trace A ((boundaryOpenCover A).indexAt p).1
    ((boundaryOpenCover A).indexAt p).2

theorem outwardNormal_orthogonal_frame (p : Boundary A)
    (v : Vector ((e.ambientDimension - 6) + 5)) :
    inner ℝ (outwardNormal A p) (traceNormalFrame A p.val v) = 0 :=
  pieceOutwardNormal_orthogonal_frame A ((boundaryOpenCover A).indexAt p).1
    ((boundaryOpenCover A).indexAt p).2 v

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
