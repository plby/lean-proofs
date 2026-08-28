import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryOverlaps

/-!
# The seven-dimensional smooth atlas on the actual native trace boundary

Glue the regular-zero atlases on the actual open boundary pieces. The
resulting boundary inclusion into the already constructed eight-dimensional
trace is smooth and retains the actual subtype map.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryOpenCover : SmoothOpenCover (𝓡 7) (boundaryPieceDomain A) where
  covers := boundaryPieceDomain_covers A
  localAtlas := boundaryPieceAtlas A
  localSmooth := boundaryPiece_isManifold A
  overlapSmooth := by
    intro i j
    cases i with
    | cylinder =>
        cases j with
        | cylinder =>
            let := boundaryPieceAtlas A .cylinder
            exact contMDiff_subtype_val
        | handle =>
            intro p
            exact (cylinder_handle_ne A (boundaryTracePoint A .cylinder p.val)
              (boundaryTracePoint A .handle (OpenOverlap.map _ _ p)) rfl).elim
        | collar => exact contMDiff_boundaryCylinderToCollar A
    | handle =>
        cases j with
        | cylinder =>
            intro p
            exact (cylinder_handle_ne A
              (boundaryTracePoint A .cylinder (OpenOverlap.map _ _ p))
              (boundaryTracePoint A .handle p.val) rfl).elim
        | handle =>
            let := boundaryPieceAtlas A .handle
            exact contMDiff_subtype_val
        | collar => exact contMDiff_boundaryHandleToCollar A
    | collar =>
        cases j with
        | cylinder => exact contMDiff_boundaryCollarToCylinder A
        | handle => exact contMDiff_boundaryCollarToHandle A
        | collar =>
            let := boundaryPieceAtlas A .collar
            exact contMDiff_subtype_val

@[instance_reducible]
def boundaryChartedSpace : ChartedSpace (Vector 7) (Boundary A) :=
  (boundaryOpenCover A).chartedSpace

theorem boundary_isManifold : letI := boundaryChartedSpace A;
    IsManifold (𝓡 7) ∞ (Boundary A) := (boundaryOpenCover A).isManifold

theorem contMDiff_boundaryInclusion : letI := traceChartedSpace A;
    letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞
      (Subtype.val : Boundary A → ambientSet A) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  apply ((boundaryOpenCover A).contMDiff_iff_onPieces _).mpr
  exact boundaryPiece_contMDiff_trace A

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
