import Wikipedia.NoExoticSixSphere.UnitSurgeryComparisonMap
import Wikipedia.NoExoticSixSphere.UnitSurgeryTargetCover

/-! # The actual complementary boundary maps onto canonical surgery -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace SmoothOpenCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def exteriorEndPoint (m : retainedExterior A) : otherBoundaryPart A :=
  letI := boundaryPieceAtlas A .cylinder
  restrictedInclusion (U := boundaryPieceDomain A) (otherBoundaryPart A) .cylinder
    (exteriorBoundaryDiffeomorph A m)

def handleEndPoint (p : boundaryHandleParameters A) : otherBoundaryPart A :=
  letI := boundaryPieceAtlas A .handle
  ⟨(boundaryHandleDiffeomorph A p).val,
    handleBoundary_mem_other A (boundaryHandleDiffeomorph A p)⟩

def collarEndPoint (p : boundaryCollarParameters A) : otherBoundaryPart A :=
  letI := boundaryPieceAtlas A .collar
  ⟨(boundaryCollarDiffeomorph A p).val,
    collarBoundary_mem_other A (boundaryCollarDiffeomorph A p)⟩

theorem comparisonMap_exteriorEndPoint (m : retainedExterior A) :
    comparisonMap A hR (exteriorEndPoint A m) = exteriorMap A hR m := by
  let := boundaryPieceAtlas A .cylinder
  have he := comparisonMap_on_piece A hR .cylinder (exteriorBoundaryDiffeomorph A m)
  change comparisonMap A hR (exteriorEndPoint A m) = exteriorMap A hR
    ((exteriorBoundaryDiffeomorph A).symm (exteriorBoundaryDiffeomorph A m)) at he
  rw [(exteriorBoundaryDiffeomorph A).symm_apply_apply] at he
  exact he

theorem comparisonMap_handleEndPoint (p : boundaryHandleParameters A) :
    comparisonMap A hR (handleEndPoint A p) = handleMap A hR p := by
  let := boundaryPieceAtlas A .handle
  let q : comparisonDomain A .handle := ⟨boundaryHandleDiffeomorph A p,
    handleBoundary_mem_other A (boundaryHandleDiffeomorph A p)⟩
  have he := comparisonMap_on_piece A hR .handle q
  change comparisonMap A hR (handleEndPoint A p) =
    handleMap A hR ((boundaryHandleDiffeomorph A).symm (boundaryHandleDiffeomorph A p)) at he
  rw [(boundaryHandleDiffeomorph A).symm_apply_apply] at he
  exact he

theorem comparisonMap_collarEndPoint (p : boundaryCollarParameters A) :
    comparisonMap A hR (collarEndPoint A p) = collarMap A hR p := by
  let := boundaryPieceAtlas A .collar
  let q : comparisonDomain A .collar := ⟨boundaryCollarDiffeomorph A p,
    collarBoundary_mem_other A (boundaryCollarDiffeomorph A p)⟩
  have he := comparisonMap_on_piece A hR .collar q
  change comparisonMap A hR (collarEndPoint A p) =
    collarMap A hR ((boundaryCollarDiffeomorph A).symm (boundaryCollarDiffeomorph A p)) at he
  rw [(boundaryCollarDiffeomorph A).symm_apply_apply] at he
  exact he

theorem surjective_comparisonMap : Surjective (comparisonMap A hR) := by
  intro q
  rcases target_cover A hR q with (⟨m, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · exact ⟨exteriorEndPoint A m, comparisonMap_exteriorEndPoint A hR m⟩
  · exact ⟨handleEndPoint A p, comparisonMap_handleEndPoint A hR p⟩
  · exact ⟨collarEndPoint A p, comparisonMap_collarEndPoint A hR p⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
