import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceOverlaps
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverMaps

/-!

# A global smooth boundary atlas on the actual rounded attachment

The unchanged cylinder, unchanged handle, and rounded collar form an actual
open cover. All nonempty cross-overlaps have the proved smooth coordinate
changes; the unchanged cylinder and handle are disjoint. The resulting
global atlas retains the compact ambient subtype topology.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

@[instance_reducible]
def pieceAtlas (i : Piece) :
    ChartedSpace (ProductHalfSpace.Space (Vector 7)) (pieceDomain A i) := by
  cases i with
  | cylinder => exact unchangedCylinderChartedSpace A
  | handle => exact unchangedHandleChartedSpace A
  | collar => exact collarChartedSpace A

theorem piece_isManifold (i : Piece) : letI := pieceAtlas A i;
    IsManifold (ProductHalfSpace.model (Vector 7)) ∞ (pieceDomain A i) := by
  cases i with
  | cylinder => exact unchangedCylinder_isManifold A
  | handle => exact unchangedHandle_isManifold A
  | collar => exact collar_isManifold A

theorem piece_contMDiff_ambient (i : Piece) : letI := pieceAtlas A i;
    ContMDiff (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (fun p : pieceDomain A i ↦ p.val.val) := by
  cases i with
  | cylinder => exact contMDiff_unchangedCylinder_ambient A
  | handle => exact contMDiff_unchangedHandle_ambient A
  | collar => exact contMDiff_collar_ambient A

def openCover : SmoothOpenCover (ProductHalfSpace.model (Vector 7)) (pieceDomain A) where
  covers := pieceDomain_covers A
  localAtlas := pieceAtlas A
  localSmooth := piece_isManifold A
  overlapSmooth := by
    intro i j
    cases i with
    | cylinder =>
        cases j with
        | cylinder =>
            let := pieceAtlas A .cylinder
            exact contMDiff_subtype_val
        | handle =>
            intro p
            exact (p.property (Or.inl (cylinderOnlyPart_mem A p.val))).elim
        | collar => exact contMDiff_cylinderToCollar A
    | handle =>
        cases j with
        | cylinder =>
            intro p
            exact (p.val.property (Or.inl (cylinderOnlyPart_mem A
              (OpenOverlap.map (handleOnlyPart A) (cylinderOnlyPart A) p)))).elim
        | handle =>
            let := pieceAtlas A .handle
            exact contMDiff_subtype_val
        | collar => exact contMDiff_handleToCollar A
    | collar =>
        cases j with
        | cylinder => exact contMDiff_collarToCylinder A
        | handle => exact contMDiff_collarToHandle A
        | collar =>
            let := pieceAtlas A .collar
            exact contMDiff_subtype_val

@[instance_reducible]
def traceChartedSpace : ChartedSpace (ProductHalfSpace.Space (Vector 7)) (ambientSet A) :=
  (openCover A).chartedSpace

theorem trace_isManifold : letI := traceChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector 7)) ∞ (ambientSet A) :=
  (openCover A).isManifold

theorem trace_contMDiff_ambient : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      ((↑) : ambientSet A → Vector (e.ambientDimension + (1 + (1 + (d + 1))))) := by
  let := traceChartedSpace A
  apply ((openCover A).contMDiff_iff_onPieces _).mpr
  exact piece_contMDiff_ambient A

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

