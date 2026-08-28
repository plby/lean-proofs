import Wikipedia.NoExoticSixSphere.RoundedTraceOverlaps
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverMaps

/-!
# A global smooth boundary atlas on the actual rounded attachment

The unchanged cylinder, unchanged handle, and rounded collar form an actual
open cover. All nonempty cross-overlaps have the proved smooth coordinate
changes; the unchanged cylinder and handle are disjoint. The resulting
global atlas retains the ambient subtype topology in the actual dimension.
The original manifold need not be compact.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

@[instance_reducible]
def pieceAtlas (i : Piece) :
    ChartedSpace (ProductHalfSpace.Space (Vector n)) (pieceDomain A i) := by
  cases i with
  | cylinder => exact unchangedCylinderChartedSpace A
  | handle => exact unchangedHandleChartedSpace A
  | collar => exact collarChartedSpace A

theorem piece_isManifold (i : Piece) : letI := pieceAtlas A i;
    IsManifold (ProductHalfSpace.model (Vector n)) ∞ (pieceDomain A i) := by
  cases i with
  | cylinder => exact unchangedCylinder_isManifold A
  | handle => exact unchangedHandle_isManifold A
  | collar => exact collar_isManifold A

theorem piece_contMDiff_ambient (i : Piece) : letI := pieceAtlas A i;
    ContMDiff (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6)) ∞
      (fun p : pieceDomain A i ↦ p.val.val) := by
  cases i with
  | cylinder => exact contMDiff_unchangedCylinder_ambient A
  | handle => exact contMDiff_unchangedHandle_ambient A
  | collar => exact contMDiff_collar_ambient A

def openCover : SmoothOpenCover (ProductHalfSpace.model (Vector n)) (pieceDomain A) where
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
def traceChartedSpace : ChartedSpace (ProductHalfSpace.Space (Vector n)) (ambientSet A) :=
  (openCover A).chartedSpace

theorem trace_isManifold : letI := traceChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector n)) ∞ (ambientSet A) :=
  (openCover A).isManifold

theorem trace_contMDiff_ambient : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6)) ∞
      ((↑) : ambientSet A → Vector (e.ambientDimension + 6)) := by
  let := traceChartedSpace A
  apply ((openCover A).contMDiff_iff_onPieces _).mpr
  exact piece_contMDiff_ambient A

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
