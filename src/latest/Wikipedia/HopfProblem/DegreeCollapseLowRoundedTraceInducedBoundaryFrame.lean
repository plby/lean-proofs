import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceGlobalOutwardNormal
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppend

/-!

# The full induced normal framing on the actual native trace boundary

The trace normal columns come first, followed by the outward unit normal.
The frame uses the genuine Euclidean block norm. Its range is the orthogonal
complement of the differential of the actual boundary inclusion.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def inducedBoundaryFrame (p : Boundary A) :
    Vector (((e.ambientDimension - 7) + (1 + (d + 1))) + 1) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  OrthogonalFrameAppend.operator (traceNormalFrame A p.val) (outwardNormal A p)

theorem inducedBoundaryFrame_apply (p : Boundary A)
    (w : Vector (((e.ambientDimension - 7) + (1 + (d + 1))) + 1)) :
    inducedBoundaryFrame A p w =
      traceNormalFrame A p.val (EuclideanSpace.finAddEquivProd w).1 +
        EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2 •
          outwardNormal A p := rfl

theorem inducedBoundaryFrame_on_piece (i : Piece) (p : boundaryPieceDomain A i) :
    inducedBoundaryFrame A p.val = OrthogonalFrameAppend.operator
      (pieceNormalFrame A i (boundaryTracePoint A i p)) (pieceOutwardNormal A i p) := by
  have ht := traceNormalFrame_on_piece A i (boundaryTracePoint A i p)
  change traceNormalFrame A p.val.val = _ at ht
  change OrthogonalFrameAppend.operator _ _ = _
  rw [ht, outwardNormal_on_piece]

theorem inducedBoundaryFrame_norm (p : Boundary A)
    (w : Vector (((e.ambientDimension - 7) + (1 + (d + 1))) + 1)) :
    ‖inducedBoundaryFrame A p w‖ = ‖w‖ :=
  OrthogonalFrameAppend.norm_operator
    ⟨traceNormalFrame A p.val, traceNormalFrame_norm A p.val⟩
    (outwardNormal A p) (norm_outwardNormal A p) (outwardNormal_orthogonal_frame A p) w

theorem contMDiff_inducedBoundaryFrame : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7)
      𝓘(ℝ, Vector (((e.ambientDimension - 7) + (1 + (d + 1))) + 1) →L[ℝ]
        Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ∞ (inducedBoundaryFrame A) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact OrthogonalFrameAppend.contMDiff_operator
    ((contMDiff_traceNormalFrame A).comp (contMDiff_boundaryInclusion A))
    (contMDiff_outwardNormal A)

theorem inducedBoundaryFrame_range_le (p : Boundary A) :
    (inducedBoundaryFrame A p).range ≤ (boundaryAmbientDerivative A p).rangeᗮ := by
  rintro _ ⟨w, rfl⟩
  change inducedBoundaryFrame A p w ∈ (boundaryAmbientDerivative A p).rangeᗮ
  rw [inducedBoundaryFrame_apply]
  apply Submodule.add_mem
  · apply Submodule.orthogonal_le (boundaryTangent_le_traceTangent A p)
    rw [← traceNormalFrame_range]
    exact ⟨_, rfl⟩
  · exact Submodule.smul_mem _ _ (outwardNormal_mem_boundaryNormal A p)

theorem inducedBoundaryFrame_range (p : Boundary A) :
    (inducedBoundaryFrame A p).range = (boundaryAmbientDerivative A p).rangeᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq (inducedBoundaryFrame_range_le A p)
  rw [LinearMap.finrank_range_of_inj
    (Stiefel.injective ⟨inducedBoundaryFrame A p, inducedBoundaryFrame_norm A p⟩),
    finrank_euclideanSpace_fin]
  have hd := (boundaryAmbientDerivative A p).range.finrank_add_finrank_orthogonal
  simp only [LinearMap.finrank_range_of_inj (injective_boundaryAmbientDerivative A p),
    finrank_euclideanSpace_fin] at hd
  have hN := e.dimension_le_ambient (f (spherePole d))
  omega

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
