import Wikipedia.NoExoticSixSphere.UnitSurgeryPieceAgreement
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverRestriction

/-!
# A smooth comparison from the actual complementary end to canonical surgery

The source uses its inherited native boundary atlas and the target uses its
independently constructed canonical surgery atlas. Exact agreement on actual
common boundary points allows smooth gluing of the three coordinate maps.
Bijectivity and smoothness of an inverse are separate obligations.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace SmoothOpenCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

abbrev comparisonDomain (i : Piece) :=
  restrictedDomain (U := boundaryPieceDomain A) (otherBoundaryPart A) i

def pieceMap (i : Piece) : comparisonDomain A i → Target A hR := by
  cases i with
  | cylinder =>
      let := boundaryPieceAtlas A .cylinder
      exact fun p ↦ exteriorMap A hR ((exteriorBoundaryDiffeomorph A).symm p)
  | handle =>
      let := boundaryPieceAtlas A .handle
      exact fun p ↦ handleMap A hR ((boundaryHandleDiffeomorph A).symm p.val)
  | collar =>
      let := boundaryPieceAtlas A .collar
      exact fun p ↦ collarMap A hR ((boundaryCollarDiffeomorph A).symm p.val)

theorem pieceMap_agree (i j : Piece) (p : comparisonDomain A i) (q : comparisonDomain A j)
    (he : p.val.val = q.val.val) : pieceMap A hR i p = pieceMap A hR j q := by
  cases i with
  | cylinder =>
      cases j with
      | cylinder => exact congrArg (pieceMap A hR .cylinder) (Subtype.ext (Subtype.ext he))
      | handle =>
          exact (cylinder_handle_ne A (boundaryTracePoint A .cylinder p.val)
            (boundaryTracePoint A .handle q.val) (congrArg Subtype.val he)).elim
      | collar =>
          let := boundaryPieceAtlas A .cylinder
          let := boundaryPieceAtlas A .collar
          apply Eq.symm
          apply collar_exterior_agreement A hR ((boundaryCollarDiffeomorph A).symm q.val) p
          rw [(boundaryCollarDiffeomorph A).apply_symm_apply]
          exact he.symm
  | handle =>
      cases j with
      | cylinder =>
          exact (cylinder_handle_ne A (boundaryTracePoint A .cylinder q.val)
            (boundaryTracePoint A .handle p.val) (congrArg Subtype.val he.symm)).elim
      | handle => exact congrArg (pieceMap A hR .handle) (Subtype.ext (Subtype.ext he))
      | collar =>
          let := boundaryPieceAtlas A .handle
          let := boundaryPieceAtlas A .collar
          apply Eq.symm
          apply collar_handle_agreement A hR ((boundaryCollarDiffeomorph A).symm q.val) p.val
          rw [(boundaryCollarDiffeomorph A).apply_symm_apply]
          exact he.symm
  | collar =>
      cases j with
      | cylinder =>
          let := boundaryPieceAtlas A .collar
          let := boundaryPieceAtlas A .cylinder
          apply collar_exterior_agreement A hR ((boundaryCollarDiffeomorph A).symm p.val) q
          rw [(boundaryCollarDiffeomorph A).apply_symm_apply]
          exact he
      | handle =>
          let := boundaryPieceAtlas A .collar
          let := boundaryPieceAtlas A .handle
          apply collar_handle_agreement A hR ((boundaryCollarDiffeomorph A).symm p.val) q.val
          rw [(boundaryCollarDiffeomorph A).apply_symm_apply]
          exact he
      | collar => exact congrArg (pieceMap A hR .collar) (Subtype.ext (Subtype.ext he))

theorem contMDiff_pieceMap (i : Piece) : letI := targetChartedSpace A hR;
    letI := boundaryPieceAtlas A i;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (pieceMap A hR i) := by
  let := targetChartedSpace A hR
  cases i with
  | cylinder =>
      let := boundaryPieceAtlas A .cylinder
      exact (contMDiff_exteriorMap A hR).comp
        (exteriorBoundaryDiffeomorph A).contMDiff_invFun
  | handle =>
      let := boundaryPieceAtlas A .handle
      exact (contMDiff_handleMap A hR).comp
        ((boundaryHandleDiffeomorph A).contMDiff_invFun.comp contMDiff_subtype_val)
  | collar =>
      let := boundaryPieceAtlas A .collar
      exact (contMDiff_collarMap A hR).comp
        ((boundaryCollarDiffeomorph A).contMDiff_invFun.comp contMDiff_subtype_val)

def comparisonMap : otherBoundaryPart A → Target A hR :=
  (boundaryOpenCover A).glueOnOpen (otherBoundaryPart A) (pieceMap A hR)

theorem comparisonMap_on_piece (i : Piece) (p : comparisonDomain A i) :
    comparisonMap A hR (restrictedInclusion (otherBoundaryPart A) i p) = pieceMap A hR i p :=
  (boundaryOpenCover A).glueOnOpen_on_piece (otherBoundaryPart A) (pieceMap A hR)
    (pieceMap_agree A hR) i p

theorem contMDiff_comparisonMap : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (comparisonMap A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact (boundaryOpenCover A).contMDiff_glueOnOpen (otherBoundaryPart A) (pieceMap A hR)
    (pieceMap_agree A hR) (contMDiff_pieceMap A hR)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
