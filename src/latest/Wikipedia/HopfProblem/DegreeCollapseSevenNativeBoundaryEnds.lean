import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceOtherEndPieces
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryNormalProjection

/-!
# Exact retained-end values and an actual embedding of the complementary end

The original boundary diffeomorphism has the same trace points and columns
as the end map fixed before the atlas was constructed. The complementary end
has its inherited native atlas and a constructed closed Euclidean embedding.
The restricted trace columns are normal to the boundary but have one fewer
column than its full normal rank; the outward boundary column is not assumed.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem originalBoundaryDiffeomorph_tracePoint (m : M) : letI := boundaryChartedSpace A;
    (originalBoundaryDiffeomorph A m).val.val = originalEnd A m := rfl

theorem originalBoundaryDiffeomorph_columns (m : M) : letI := boundaryChartedSpace A;
    columns A (originalBoundaryDiffeomorph A m).val.val =
      boundaryFrameOperator (a.orthonormal m).val := columns_originalEnd A m

theorem boundaryEndsDiffeomorph_inl_tracePoint (m : M) : letI := boundaryChartedSpace A;
    (boundaryEndsDiffeomorph A (Sum.inl m)).val = originalEnd A m := rfl

theorem contMDiff_otherBoundaryAmbient : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 (e.ambientDimension + 6)) ∞
      (fun p : otherBoundaryPart A ↦ p.val.val.val) := by
  let := boundaryChartedSpace A
  exact (contMDiff_boundaryAmbientInclusion A).comp
    (_root_.contMDiff_subtype_val (I := 𝓡 7) (U := otherBoundaryPart A) (n := ∞))

theorem injective_mfderiv_otherBoundaryAmbient (p : otherBoundaryPart A) :
    letI := boundaryChartedSpace A;
    Injective (mfderiv (𝓡 7) (𝓡 (e.ambientDimension + 6))
      (fun q : otherBoundaryPart A ↦ q.val.val.val) p) := by
  let := boundaryChartedSpace A
  change Injective (mfderiv (𝓡 7) (𝓡 (e.ambientDimension + 6))
    ((fun q : Boundary A ↦ q.val.val) ∘ (Subtype.val : otherBoundaryPart A → Boundary A)) p)
  rw [mfderiv_comp p ((contMDiff_boundaryAmbientInclusion A).mdifferentiableAt (by simp))
    ((_root_.contMDiff_subtype_val (I := 𝓡 7) (U := otherBoundaryPart A) (n := ∞)).mdifferentiableAt
      (by simp))]
  exact (injective_boundaryAmbientDerivative A p.val).comp
    (mfderiv_openSubset_val_bijective (I := 𝓡 7) (otherBoundaryPart A) p).1

theorem isClosedEmbedding_otherBoundaryAmbient :
    IsClosedEmbedding (fun p : otherBoundaryPart A ↦ p.val.val.val) :=
  (isClosedEmbedding_boundaryAmbient A).comp
    (isClosed_otherBoundaryPart A).isClosedEmbedding_subtypeVal

def otherBoundaryEuclideanEmbedding : letI := boundaryChartedSpace A;
    EuclideanEmbedding 7 (otherBoundaryPart A) := by
  let := boundaryChartedSpace A
  exact
    { ambientDimension := e.ambientDimension + 6
      toFun := fun p ↦ p.val.val.val
      smooth := contMDiff_otherBoundaryAmbient A
      closedEmbedding := isClosedEmbedding_otherBoundaryAmbient A
      injective_mfderiv := injective_mfderiv_otherBoundaryAmbient A }

theorem traceColumns_boundary_normal (p : Boundary A) :
    (columns A p.val).range ≤ (boundaryAmbientDerivative A p).rangeᗮ := by
  rw [columns_range]
  exact Submodule.orthogonal_le (boundaryTangent_le_traceTangent A p)

theorem boundary_normal_rank_eq_trace_rank_add_one (p : Boundary A) :
    Module.finrank ℝ (boundaryAmbientDerivative A p).rangeᗮ =
      Module.finrank ℝ (columns A p.val).range + 1 := by
  rw [columns_range]
  have hT := (traceAmbientDerivative A p.val).range.finrank_add_finrank_orthogonal
  have hB := (boundaryAmbientDerivative A p).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (injective_traceAmbientDerivative A p.val)] at hT
  rw [LinearMap.finrank_range_of_inj (injective_boundaryAmbientDerivative A p)] at hB
  simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin] at hT hB
  omega

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
