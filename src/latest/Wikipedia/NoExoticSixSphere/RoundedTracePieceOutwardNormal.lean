import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryNormalProjection
import Wikipedia.NoExoticSixSphere.RoundedTraceOutwardDirections

/-!
# Actual unit outward normal columns on the three boundary pieces

The vector starts in the actual trace tangent image and is projected using
the actual boundary embedding's normal projection. The defining differential
proves the projection nonzero. It stays tangent to the trace, is normal to the
boundary, and is orthogonal to every existing trace-normal frame column.
Smoothness and agreement across pieces are separate obligations.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def pieceOutwardVector : ∀ i : Piece, boundaryPieceDomain A i → Vector (e.ambientDimension + 6)
  | .cylinder, p => e.heightCylinderDerivative (cylinderBoundaryCoordinates A p)
      (cylinderOutwardDirection A p)
  | .handle, p => fderiv ℝ A.map (handleBoundaryCoordinates A p) (handleOutwardDirection A p)
  | .collar, p => A.collarSheetDerivative (collarBoundaryCoordinates A p)
      (collarOutwardDirection A p)

def pieceOutwardNormal (i : Piece) (p : boundaryPieceDomain A i) :
    Vector (e.ambientDimension + 6) :=
  NormedSpace.normalize (boundaryNormalProjection A p.val (pieceOutwardVector A i p))

theorem projected_pieceOutwardVector_ne_zero (i : Piece) (p : boundaryPieceDomain A i) :
    boundaryNormalProjection A p.val (pieceOutwardVector A i p) ≠ 0 := by
  cases i with
  | cylinder =>
      simp only [boundaryNormalProjection_eq, boundaryTangent_cylinder]
      exact fun hz ↦ (cylinderOutwardDirection_negative A p).ne
        ((CoorientedHypersurfaceNormal.projected_eq_zero_iff _ _
          (e.injective_heightCylinderDerivative _) _).mp hz)
  | handle =>
      simp only [boundaryNormalProjection_eq, boundaryTangent_handle]
      let q := unchangedHandleHomeomorph A (boundaryTracePoint A .handle p)
      have hi : Injective (fderiv ℝ A.map (handleBoundaryCoordinates A p)) :=
        A.immersive q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
          (handleSuperlevel_vector_mem A q.val)
      exact fun hz ↦ (handleOutwardDirection_negative A p).ne
        ((CoorientedHypersurfaceNormal.projected_eq_zero_iff _ _ hi _).mp hz)
  | collar =>
      simp only [boundaryNormalProjection_eq, boundaryTangent_collar]
      have hi := A.injective_collarSheetDerivative (collarParameters_subset_source A
        ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property)
      exact fun hz ↦ (collarOutwardDirection_negative A p).ne
        ((CoorientedHypersurfaceNormal.projected_eq_zero_iff _ _ hi _).mp hz)

theorem norm_pieceOutwardNormal (i : Piece) (p : boundaryPieceDomain A i) :
    ‖pieceOutwardNormal A i p‖ = 1 :=
  NormedSpace.norm_normalize (projected_pieceOutwardVector_ne_zero A i p)

theorem pieceOutwardNormal_mem_boundaryNormal (i : Piece) (p : boundaryPieceDomain A i) :
    pieceOutwardNormal A i p ∈ (boundaryAmbientDerivative A p.val).rangeᗮ :=
  (boundaryAmbientDerivative A p.val).rangeᗮ.smul_mem _
    (boundaryNormalProjection_mem A p.val (pieceOutwardVector A i p))

theorem pieceOutwardVector_mem_trace (i : Piece) (p : boundaryPieceDomain A i) :
    pieceOutwardVector A i p ∈ (traceAmbientDerivative A p.val.val).range := by
  have hr := range_pieceAmbientDerivative A i (boundaryTracePoint A i p)
  apply hr.le
  cases i with
  | cylinder =>
      let := unchangedCylinderChartedSpace A
      let q : cylinderOnlyPart A := boundaryTracePoint A .cylinder p
      obtain ⟨w, hw⟩ := (bijective_mfderiv_unchangedCylinder_parameters A q).surjective
        (cylinderOutwardDirection A p)
      refine ⟨w, ?_⟩
      exact (congrArg (fun L : (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) ↦ L w)
        (cylinder_pieceDerivative_eq A q)).trans
          (congrArg (e.heightCylinderDerivative (cylinderBoundaryCoordinates A p)) hw)
  | handle =>
      let := unchangedHandleChartedSpace A
      let q : handleOnlyPart A := boundaryTracePoint A .handle p
      obtain ⟨w, hw⟩ := (bijective_mfderiv_unchangedHandle_parameters A q).surjective
        (handleOutwardDirection A p)
      refine ⟨w, ?_⟩
      exact (congrArg (fun L : (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) ↦ L w)
        (handle_pieceDerivative_eq A q)).trans
          (congrArg (fderiv ℝ A.map (handleBoundaryCoordinates A p)) hw)
  | collar =>
      let q : collarPart A := boundaryTracePoint A .collar p
      obtain ⟨w, hw⟩ := (bijective_collarParameterDerivative A q).surjective
        (collarOutwardDirection A p)
      refine ⟨w, ?_⟩
      exact (congrArg (fun L : (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) ↦ L w)
        (collarAmbientDerivative_eq A q)).trans
          (congrArg (A.collarSheetDerivative (collarBoundaryCoordinates A p)) hw)

theorem pieceOutwardNormal_mem_trace (i : Piece) (p : boundaryPieceDomain A i) :
    pieceOutwardNormal A i p ∈ (traceAmbientDerivative A p.val.val).range :=
  (traceAmbientDerivative A p.val.val).range.smul_mem _
    (boundaryNormalProjection_mem_trace A p.val (pieceOutwardVector_mem_trace A i p))

theorem pieceOutwardNormal_orthogonal_frame (i : Piece) (p : boundaryPieceDomain A i)
    (v : Vector ((e.ambientDimension - 6) + 5)) :
    inner ℝ (pieceOutwardNormal A i p) (traceNormalFrame A p.val.val v) = 0 := by
  have hv : traceNormalFrame A p.val.val v ∈ (traceAmbientDerivative A p.val.val).rangeᗮ := by
    rw [← traceNormalFrame_range]
    exact ⟨v, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal (pieceOutwardNormal_mem_trace A i p) hv

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
