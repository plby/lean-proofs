import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceOtherEndPieces
import Wikipedia.NoExoticSixSphere.OpenSuperlevelBoundaryTangent

/-! # Exact tangent-kernel identities in the three actual boundary parameter systems -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem handleBoundary_level_zero (p : boundaryPieceDomain A .handle) :
    LowHandleSuperlevel.level (UnroundedTrace.handleRadius A)
      (handleBoundaryCoordinates A p) = 0 := by
  let := traceChartedSpace A
  let := unchangedHandleChartedSpace A
  let q : handleOnlyPart A := boundaryTracePoint A .handle p
  apply (LowHandleSuperlevel.zero_iff (UnroundedTrace.handleRadius_pos A) _).mpr
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
    (mfderiv (𝓡 7) 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) (handleBoundaryCoordinates A) p).range =
      (fderiv ℝ (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)).ker := by
  let := localBoundaryAtlas A .handle
  let := boundaryPieceAtlas A .handle
  have hr : Surjective (mfderiv 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) 𝓘(ℝ, ℝ)
      (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)) := by
    rw [mfderiv_eq_fderiv]
    exact LowHandleSuperlevel.regular_zero
      (UnroundedTrace.handleRadius_pos A) (handleBoundary_level_zero A p)
  have hs := LowHandleSuperlevel.contDiff_level (n := d + 1) (q := 7 - d)
    (UnroundedTrace.handleRadius A)
  have he := OpenSuperlevelBoundary.range_mfderiv_coordinates_comp (handleLevelAtlas A)
    (unchangedHandleWindow A) (unchangedHandleHomeomorph A) (handleZeroAtlas A)
    (boundaryPieceDiffeomorph A .handle) p
    (hs.contMDiff.mdifferentiableAt (by simp)) hr
    (by
      have hdim := A.handle_dimension
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
      omega)
  rw [mfderiv_eq_fderiv] at he
  exact he

theorem range_collarBoundaryCoordinates (p : boundaryPieceDomain A .collar) :
    letI := boundaryPieceAtlas A .collar;
    (mfderiv (𝓡 7) (collarModel d (7 - d)) (collarBoundaryCoordinates A) p).range =
      (mfderiv (collarModel d (7 - d)) 𝓘(ℝ, ℝ)
        (collarLevel (bump A) (UnroundedTrace.handleRadius A))
        (collarBoundaryCoordinates A p)).ker := by
  let := localBoundaryAtlas A .collar
  let := boundaryPieceAtlas A .collar
  have hs := contMDiff_collarLevel (d := d) (q := 7 - d) (bump A) (UnroundedTrace.handleRadius A)
  exact OpenSuperlevelBoundary.range_mfderiv_coordinates_comp (collarLevelAtlas A)
    (collarWindow A) (collarWindowHomeomorph A) (collarZeroAtlas A)
    (boundaryPieceDiffeomorph A .collar) p
    (hs.mdifferentiableAt (by simp))
    (regular_collarLevel_zero (bump A) (UnroundedTrace.handleRadius_pos A)
      (collarBoundary_level_zero A p))
    (by
      have hdim := A.tube_dimension
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
      omega)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
