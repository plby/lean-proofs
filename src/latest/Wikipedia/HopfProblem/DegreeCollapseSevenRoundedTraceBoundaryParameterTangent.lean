import Wikipedia.HopfProblem.DegreeCollapseSevenNativeBoundaryEnds
import Wikipedia.NoExoticSixSphere.OpenSuperlevelBoundaryTangent

/-! # Exact tangent-kernel identities in the three actual boundary parameter systems -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem handleBoundary_level_zero (p : boundaryPieceDomain A .handle) :
    Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.level (UnroundedTrace.handleRadius A)
      (handleBoundaryCoordinates A p) = 0 := by
  let := traceChartedSpace A
  let := unchangedHandleChartedSpace A
  let q : handleOnlyPart A := boundaryTracePoint A .handle p
  apply (Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.zero_iff (UnroundedTrace.handleRadius_pos A) _).mpr
  exact (unchangedHandle_isBoundaryPoint_iff A q).mp
    (((openCover A).isBoundaryPoint_inclusion_iff .handle q).mpr p.val.property)

theorem range_cylinderBoundaryCoordinates (p : boundaryPieceDomain A .cylinder) :
    letI := boundaryPieceAtlas A .cylinder;
    (mfderiv (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) (cylinderBoundaryCoordinates A) p).range =
      (mfderiv ((𝓡 7).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A))
          (cylinderBoundaryCoordinates A p)).ker := by
  let := localBoundaryAtlas A .cylinder
  let := boundaryPieceAtlas A .cylinder
  have hz : IntervalSuperlevel.level (UnroundedTrace.height A)
      (cylinderBoundaryCoordinates A p) = 0 :=
    (IntervalSuperlevel.zero_iff _ _).mpr (cylinderBoundary_time_cases A p)
  exact OpenSuperlevelBoundary.range_mfderiv_coordinates_comp (cylinderLevelAtlas A)
    (unchangedCylinderWindow A) (unchangedCylinderHomeomorph A) (cylinderZeroAtlas A)
    (boundaryPieceDiffeomorph A .cylinder) p
    ((IntervalSuperlevel.contMDiff_level (I := 𝓡 7)
      (UnroundedTrace.height A)).mdifferentiableAt (by simp))
    (IntervalSuperlevel.regular_zero (I := 𝓡 7) (UnroundedTrace.height_pos A) hz)
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self])

theorem range_handleBoundaryCoordinates (p : boundaryPieceDomain A .handle) :
    letI := boundaryPieceAtlas A .handle;
    (mfderiv (𝓡 7) 𝓘(ℝ, Vector 4 × Vector 4) (handleBoundaryCoordinates A) p).range =
      (fderiv ℝ (Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)).ker := by
  let := localBoundaryAtlas A .handle
  let := boundaryPieceAtlas A .handle
  have hr : Surjective (mfderiv 𝓘(ℝ, Vector 4 × Vector 4) 𝓘(ℝ, ℝ)
      (Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)) := by
    rw [mfderiv_eq_fderiv]
    exact Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.regular_zero
      (UnroundedTrace.handleRadius_pos A) (handleBoundary_level_zero A p)
  have hs := Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel.contDiff_level (UnroundedTrace.handleRadius A)
  have he := OpenSuperlevelBoundary.range_mfderiv_coordinates_comp (handleLevelAtlas A)
    (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A)
    (boundaryPieceDiffeomorph A .handle) p
    (hs.contMDiff.mdifferentiableAt (by simp)) hr
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])
  rw [mfderiv_eq_fderiv] at he
  exact he

theorem range_collarBoundaryCoordinates (p : boundaryPieceDomain A .collar) :
    letI := boundaryPieceAtlas A .collar;
    (mfderiv (𝓡 7) collarModel (collarBoundaryCoordinates A) p).range =
      (mfderiv collarModel 𝓘(ℝ, ℝ) (collarLevel (bump A) (UnroundedTrace.handleRadius A))
        (collarBoundaryCoordinates A p)).ker := by
  let := localBoundaryAtlas A .collar
  let := boundaryPieceAtlas A .collar
  have hs := contMDiff_collarLevel (bump A) (UnroundedTrace.handleRadius A)
  exact OpenSuperlevelBoundary.range_mfderiv_coordinates_comp (collarLevelAtlas A)
    (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A)
    (boundaryPieceDiffeomorph A .collar) p
    (hs.mdifferentiableAt (by simp))
    (regular_collarLevel_zero (bump A) (UnroundedTrace.handleRadius_pos A)
      (collarBoundary_level_zero A p))
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self])

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
