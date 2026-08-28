import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryComparisonSurjective

/-! # The actual piece parametrizations into the inherited complementary-end atlas -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner RoundedTrace SmoothOpenCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_exteriorEndPoint : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorEndPoint A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  have hi : ContMDiff (𝓡 7) (𝓡 7) ∞
      (restrictedInclusion (U := boundaryPieceDomain A) (otherBoundaryPart A) .cylinder) :=
    fun p ↦ ((boundaryOpenCover A).isLocalDiffeomorphAt_restrictedInclusion
      (otherBoundaryPart A) .cylinder p).contMDiffAt
  exact hi.comp (exteriorBoundaryDiffeomorph A).contMDiff_toFun

theorem contMDiff_handleEndPoint : letI := boundaryChartedSpace A;
    ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 7) ∞ (handleEndPoint A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .handle
  apply (ContMDiff.subtypeVal_comp_iff (otherBoundaryPart A) (handleEndPoint A)).mp
  have hi : ContMDiff (𝓡 7) (𝓡 7) ∞
      (Subtype.val : boundaryPieceDomain A .handle → Boundary A) :=
    (boundaryOpenCover A).contMDiff_inclusion .handle
  exact hi.comp (boundaryHandleDiffeomorph A).contMDiff_toFun

theorem contMDiff_collarEndPoint : letI := boundaryChartedSpace A;
    ContMDiff boundaryParameterModel (𝓡 7) ∞ (collarEndPoint A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .collar
  apply (ContMDiff.subtypeVal_comp_iff (otherBoundaryPart A) (collarEndPoint A)).mp
  have hi : ContMDiff (𝓡 7) (𝓡 7) ∞
      (Subtype.val : boundaryPieceDomain A .collar → Boundary A) :=
    (boundaryOpenCover A).contMDiff_inclusion .collar
  exact hi.comp (boundaryCollarDiffeomorph A).contMDiff_toFun

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
