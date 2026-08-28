import Wikipedia.NoExoticSixSphere.UnitSurgeryInducedFrame

/-! # Exact ambient and frame formulas on all three actual surgery pieces -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedTrace RoundedHandleCorner StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem boundaryPoint_exterior (p : retainedExterior A) :
    boundaryPoint A hR (exteriorMap A hR p) = (exteriorEndPoint A p).val :=
  congrArg Subtype.val (comparisonEquiv_symm_exterior A hR p)

theorem boundaryPoint_handle (p : boundaryHandleParameters A) :
    boundaryPoint A hR (handleMap A hR p) = (handleEndPoint A p).val :=
  congrArg Subtype.val (comparisonEquiv_symm_handle A hR p)

theorem boundaryPoint_collar (p : boundaryCollarParameters A) :
    boundaryPoint A hR (collarMap A hR p) = (collarEndPoint A p).val :=
  congrArg Subtype.val (comparisonEquiv_symm_collar A hR p)

theorem ambientMap_exterior (p : retainedExterior A) :
    ambientMap A hR (exteriorMap A hR p) = e.heightCylinder (p.val, 0) := by
  change (boundaryPoint A hR _).val.val = _
  rw [boundaryPoint_exterior]
  rfl

theorem ambientMap_handle (p : boundaryHandleParameters A) :
    ambientMap A hR (handleMap A hR p) =
      A.map (p.val.1, UnroundedTrace.handleRadius A • p.val.2.val) := by
  change (boundaryPoint A hR _).val.val = _
  rw [boundaryPoint_handle]
  exact boundaryHandleDiffeomorph_ambient A p

theorem ambientMap_collar (p : boundaryCollarParameters A) :
    ambientMap A hR (collarMap A hR p) =
      A.collarSheet (collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val) := by
  change (boundaryPoint A hR _).val.val = _
  rw [boundaryPoint_collar]
  exact boundaryCollarDiffeomorph_ambient A p

theorem inducedNormalFrame_exterior (p : retainedExterior A) :
    inducedNormalFrame A hR (exteriorMap A hR p) = OrthogonalFrameAppend.operator
      (boundaryFrameOperator (a.orthonormal p.val).val) (-heightUnit e.ambientDimension) := by
  change inducedBoundaryFrame A (boundaryPoint A hR _) = _
  rw [boundaryPoint_exterior]
  change inducedBoundaryFrame A (exteriorBoundaryLift A p).val = _
  rw [inducedBoundaryFrame_on_piece, pieceOutwardNormal_cylinder_bottom A _
    (congrArg Prod.snd (exteriorBoundaryLift_coordinates A p))]
  congr 1
  change boundaryFrameOperator
    (a.orthonormal (cylinderBoundaryCoordinates A (exteriorBoundaryLift A p)).1).val = _
  rw [exteriorBoundaryLift_coordinates]

theorem inducedNormalFrame_handle (p : boundaryHandleParameters A) :
    letI := boundaryPieceAtlas A .handle;
    inducedNormalFrame A hR (handleMap A hR p) = OrthogonalFrameAppend.operator
      (A.normalFrame (p.val.1, UnroundedTrace.handleRadius A • p.val.2.val))
      (pieceOutwardNormal A .handle (boundaryHandleDiffeomorph A p)) := by
  let := boundaryPieceAtlas A .handle
  change inducedBoundaryFrame A (boundaryPoint A hR _) = _
  rw [boundaryPoint_handle]
  change inducedBoundaryFrame A (boundaryHandleDiffeomorph A p).val = _
  rw [inducedBoundaryFrame_on_piece]
  congr 1
  change A.normalFrame (handleBoundaryCoordinates A (boundaryHandleDiffeomorph A p)) = _
  rw [boundaryHandleDiffeomorph_coordinates]

theorem inducedNormalFrame_collar (p : boundaryCollarParameters A) :
    letI := boundaryPieceAtlas A .collar;
    inducedNormalFrame A hR (collarMap A hR p) = OrthogonalFrameAppend.operator
      (boundaryFrameOperator (a.orthonormal
        (A.tube (collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val).1)).val)
      (pieceOutwardNormal A .collar (boundaryCollarDiffeomorph A p)) := by
  let := boundaryPieceAtlas A .collar
  change inducedBoundaryFrame A (boundaryPoint A hR _) = _
  rw [boundaryPoint_collar]
  change inducedBoundaryFrame A (boundaryCollarDiffeomorph A p).val = _
  rw [inducedBoundaryFrame_on_piece]
  congr 1
  change boundaryFrameOperator
    (a.orthonormal (A.tube (collarBoundaryCoordinates A (boundaryCollarDiffeomorph A p)).1)).val = _
  rw [boundaryCollarDiffeomorph_coordinates]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
