import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalEnd
import Wikipedia.NoExoticSixSphere.OpenSuperlevelBoundaryDifferential

/-!
# Immersion of the actual six-dimensional boundary

The native boundary inclusion has injective differential into the trace and
into the ambient Euclidean space. These are the differentials of the actual
subtype maps with the globally glued boundary and trace atlases.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem localBoundary_injective_mfderiv_inclusion (i : Piece) (p : LocalBoundary A i) :
    letI := pieceAtlas A i; letI := localBoundaryAtlas A i;
    Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (Subtype.val : LocalBoundary A i → pieceDomain A i) p) := by
  cases i with
  | cylinder =>
      exact OpenSuperlevelBoundary.injective_mfderiv_inclusion (cylinderLevelAtlas A)
        (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) (cylinderZeroAtlas A) p
  | handle =>
      exact OpenSuperlevelBoundary.injective_mfderiv_inclusion (handleLevelAtlas A)
        (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A) p
  | collar =>
      exact OpenSuperlevelBoundary.injective_mfderiv_inclusion (collarLevelAtlas A)
        (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A) p

theorem injective_mfderiv_boundaryTracePoint (i : Piece) (p : boundaryPieceDomain A i) :
    letI := pieceAtlas A i; letI := boundaryPieceAtlas A i;
    Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (boundaryTracePoint A i) p) := by
  let := pieceAtlas A i
  let := localBoundaryAtlas A i
  let := boundaryPieceAtlas A i
  let d := boundaryPieceDiffeomorph A i
  have hd : mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6)) (boundaryTracePoint A i) p =
      (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
        (Subtype.val : LocalBoundary A i → pieceDomain A i) (d p)).comp
          (mfderiv (𝓡 6) (𝓡 6) d p) :=
    mfderiv_comp p ((localBoundary_contMDiff_inclusion A i).mdifferentiable (by simp) _)
      (d.contMDiff_toFun.mdifferentiable (by simp) p)
  rw [hd]
  exact (localBoundary_injective_mfderiv_inclusion A i (d p)).comp
    (d.mfderivToContinuousLinearEquiv (by simp) p).injective

theorem boundaryPiece_injective_mfderiv_trace (i : Piece) (p : boundaryPieceDomain A i) :
    letI := traceChartedSpace A; letI := boundaryPieceAtlas A i;
    Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (fun q : boundaryPieceDomain A i ↦ q.val.val) p) := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  let := boundaryPieceAtlas A i
  have hi := (openCover A).isLocalDiffeomorphAt_inclusion i (boundaryTracePoint A i p)
  change Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
    ((Subtype.val : pieceDomain A i → ambientSet A) ∘ boundaryTracePoint A i) p)
  rw [mfderiv_comp p (hi.mdifferentiableAt (by simp))
    ((contMDiff_boundaryTracePoint A i).mdifferentiable (by simp) p)]
  exact (hi.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    (injective_mfderiv_boundaryTracePoint A i p)

theorem injective_mfderiv_boundaryInclusion (p : Boundary A) :
    letI := traceChartedSpace A; letI := boundaryChartedSpace A;
    Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (Subtype.val : Boundary A → ambientSet A) p) := by
  let := traceChartedSpace A
  exact (boundaryOpenCover A).injective_mfderiv_of_onPieces Subtype.val
    (contMDiff_boundaryInclusion A) (boundaryPiece_injective_mfderiv_trace A) p

theorem contMDiff_boundaryAmbientInclusion : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞
      (fun p : Boundary A ↦ p.val.val) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact (trace_contMDiff_ambient A).comp (contMDiff_boundaryInclusion A)

def boundaryAmbientDerivative (p : Boundary A) : Vector 6 →L[ℝ]
    Vector (e.ambientDimension + 6) := by
  let := boundaryChartedSpace A
  exact mfderiv (𝓡 6) (𝓡 (e.ambientDimension + 6)) (fun q : Boundary A ↦ q.val.val) p

theorem boundaryAmbientDerivative_eq (p : Boundary A) : letI := traceChartedSpace A;
    letI := boundaryChartedSpace A;
    boundaryAmbientDerivative A p = (traceAmbientDerivative A p.val).comp
      (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
        (Subtype.val : Boundary A → ambientSet A) p) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact mfderiv_comp p ((trace_contMDiff_ambient A).mdifferentiable (by simp) p.val)
    ((contMDiff_boundaryInclusion A).mdifferentiable (by simp) p)

theorem injective_boundaryAmbientDerivative (p : Boundary A) :
    Injective (boundaryAmbientDerivative A p) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  rw [boundaryAmbientDerivative_eq A p]
  exact (injective_traceAmbientDerivative A p.val).comp
    (injective_mfderiv_boundaryInclusion A p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
