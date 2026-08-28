import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryPieces

/-!
# Actual parameter criteria for the seven-dimensional boundary pieces

Smoothness into each boundary piece is detected by the same original
ambient parameter maps already used to compare the trace pieces. The
regular-zero atlases justify the reverse implication.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderBoundaryCoordinates (p : boundaryPieceDomain A .cylinder) : M × ℝ :=
  (unchangedCylinderHomeomorph A (boundaryTracePoint A .cylinder p)).val.val

def handleBoundaryCoordinates (p : boundaryPieceDomain A .handle) : Vector 4 × Vector 4 :=
  (unchangedHandleHomeomorph A (boundaryTracePoint A .handle p)).val.val

def collarBoundaryCoordinates (p : boundaryPieceDomain A .collar) : Collar :=
  ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).val

theorem contMDiff_cylinderBoundaryCoordinates : letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞ (cylinderBoundaryCoordinates A) := by
  let := boundaryPieceAtlas A .cylinder
  let := pieceAtlas A .cylinder
  let := unchangedCylinderChartedSpace A
  have hp : ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞
      (boundaryTracePoint A .cylinder : boundaryPieceDomain A .cylinder → cylinderOnlyPart A) :=
    contMDiff_boundaryTracePoint A .cylinder
  exact (contMDiff_unchangedCylinder_parameters A).comp hp

theorem contMDiff_handleBoundaryCoordinates : letI := boundaryPieceAtlas A .handle;
    ContMDiff (𝓡 7) 𝓘(ℝ, Vector 4 × Vector 4) ∞ (handleBoundaryCoordinates A) := by
  let := boundaryPieceAtlas A .handle
  let := pieceAtlas A .handle
  let := unchangedHandleChartedSpace A
  have hp : ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞
      (boundaryTracePoint A .handle : boundaryPieceDomain A .handle → handleOnlyPart A) :=
    contMDiff_boundaryTracePoint A .handle
  exact (contMDiff_unchangedHandle_parameters A).comp hp

theorem contMDiff_collarBoundaryCoordinates : letI := boundaryPieceAtlas A .collar;
    ContMDiff (𝓡 7) collarModel ∞ (collarBoundaryCoordinates A) := by
  let := boundaryPieceAtlas A .collar
  let := pieceAtlas A .collar
  let := collarChartedSpace A
  have hp : ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞
      (boundaryTracePoint A .collar : boundaryPieceDomain A .collar → collarPart A) :=
    contMDiff_boundaryTracePoint A .collar
  exact (contMDiff_collarParameters A).comp hp

variable {B H P : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {J : ModelWithCorners ℝ B H}
  [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiff_cylinderBoundary_iff_coordinates (g : P → boundaryPieceDomain A .cylinder) :
    letI := boundaryPieceAtlas A .cylinder;
    ContMDiff J (𝓡 7) ∞ g ↔
      ContMDiff J ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞ (cylinderBoundaryCoordinates A ∘ g) := by
  let := localBoundaryAtlas A .cylinder
  let := boundaryPieceAtlas A .cylinder
  exact (contMDiff_boundaryPiece_iff_local A .cylinder g).trans
    (OpenSuperlevelBoundary.contMDiff_iff_coordinates (cylinderLevelAtlas A)
      (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) (cylinderZeroAtlas A)
      (boundaryPieceHomeomorph A .cylinder ∘ g))

theorem contMDiff_handleBoundary_iff_coordinates (g : P → boundaryPieceDomain A .handle) :
    letI := boundaryPieceAtlas A .handle;
    ContMDiff J (𝓡 7) ∞ g ↔
      ContMDiff J 𝓘(ℝ, Vector 4 × Vector 4) ∞ (handleBoundaryCoordinates A ∘ g) := by
  let := localBoundaryAtlas A .handle
  let := boundaryPieceAtlas A .handle
  exact (contMDiff_boundaryPiece_iff_local A .handle g).trans
    (OpenSuperlevelBoundary.contMDiff_iff_coordinates (handleLevelAtlas A)
      (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A)
      (boundaryPieceHomeomorph A .handle ∘ g))

theorem contMDiff_collarBoundary_iff_coordinates (g : P → boundaryPieceDomain A .collar) :
    letI := boundaryPieceAtlas A .collar;
    ContMDiff J (𝓡 7) ∞ g ↔ ContMDiff J collarModel ∞ (collarBoundaryCoordinates A ∘ g) := by
  let := localBoundaryAtlas A .collar
  let := boundaryPieceAtlas A .collar
  exact (contMDiff_boundaryPiece_iff_local A .collar g).trans
    (OpenSuperlevelBoundary.contMDiff_iff_coordinates (collarLevelAtlas A)
      (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A)
      (boundaryPieceHomeomorph A .collar ∘ g))

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
