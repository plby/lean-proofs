import Wikipedia.NoExoticSixSphere.UnitSurgeryComparisonSurjective

/-! # The actual piece parametrizations into the inherited complementary-end atlas -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace SmoothOpenCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_exteriorEndPoint : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (exteriorEndPoint A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  have hi : ContMDiff (𝓡 6) (𝓡 6) ∞
      (restrictedInclusion (U := boundaryPieceDomain A) (otherBoundaryPart A) .cylinder) :=
    fun p ↦ ((boundaryOpenCover A).isLocalDiffeomorphAt_restrictedInclusion
      (otherBoundaryPart A) .cylinder p).contMDiffAt
  exact hi.comp (exteriorBoundaryDiffeomorph A).contMDiff_toFun

theorem contMDiff_handleEndPoint : letI := boundaryChartedSpace A;
    ContMDiff ((𝓡 4).prod (𝓡 2)) (𝓡 6) ∞ (handleEndPoint A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .handle
  apply (ContMDiff.subtypeVal_comp_iff (otherBoundaryPart A) (handleEndPoint A)).mp
  have hi : ContMDiff (𝓡 6) (𝓡 6) ∞
      (Subtype.val : boundaryPieceDomain A .handle → Boundary A) :=
    (boundaryOpenCover A).contMDiff_inclusion .handle
  exact hi.comp (boundaryHandleDiffeomorph A).contMDiff_toFun

theorem contMDiff_collarEndPoint : letI := boundaryChartedSpace A;
    ContMDiff boundaryParameterModel (𝓡 6) ∞ (collarEndPoint A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .collar
  apply (ContMDiff.subtypeVal_comp_iff (otherBoundaryPart A) (collarEndPoint A)).mp
  have hi : ContMDiff (𝓡 6) (𝓡 6) ∞
      (Subtype.val : boundaryPieceDomain A .collar → Boundary A) :=
    (boundaryOpenCover A).contMDiff_inclusion .collar
  exact hi.comp (boundaryCollarDiffeomorph A).contMDiff_toFun

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
