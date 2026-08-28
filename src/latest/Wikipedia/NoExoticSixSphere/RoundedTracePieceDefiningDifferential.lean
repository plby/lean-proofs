import Wikipedia.NoExoticSixSphere.RoundedTracePieceDefiningFunctions

/-! # Each native defining function decreases along the actual outward tangent lift -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem cylinder_pieceLevelDifferential_eq (p : boundaryPieceDomain A .cylinder) :
    letI := pieceAtlas A .cylinder;
    letI := unchangedCylinderChartedSpace A;
    pieceLevelDifferential A .cylinder (boundaryTracePoint A .cylinder p) =
      (cylinderBoundaryLevelDerivative A p).comp
        (show (ℝ × Vector 6) →L[ℝ] (Vector 6 × ℝ) from
          mfderiv (ProductHalfSpace.model (Vector 6)) ((𝓡 6).prod 𝓘(ℝ, ℝ))
            (fun q : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A q).val.val)
            (boundaryTracePoint A .cylinder p)) := by
  let := pieceAtlas A .cylinder
  let := unchangedCylinderChartedSpace A
  exact mfderiv_comp (boundaryTracePoint A .cylinder p)
    ((IntervalSuperlevel.contMDiff_level (I := 𝓡 6)
      (UnroundedTrace.height A)).mdifferentiableAt (by simp))
    ((contMDiff_unchangedCylinder_parameters A).mdifferentiableAt (by simp))

theorem handle_pieceLevelDifferential_eq (p : boundaryPieceDomain A .handle) :
    letI := pieceAtlas A .handle;
    letI := unchangedHandleChartedSpace A;
    pieceLevelDifferential A .handle (boundaryTracePoint A .handle p) =
      (fderiv ℝ (NoExoticSixSphere.HandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)).comp
          (show (ℝ × Vector 6) →L[ℝ] (Vector 4 × Vector 3) from
            mfderiv (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, Vector 4 × Vector 3)
              (fun q : handleOnlyPart A ↦ (unchangedHandleHomeomorph A q).val.val)
              (boundaryTracePoint A .handle p)) := by
  let := pieceAtlas A .handle
  let := unchangedHandleChartedSpace A
  have hd := mfderiv_comp (boundaryTracePoint A .handle p)
    ((NoExoticSixSphere.HandleSuperlevel.contDiff_level
      (UnroundedTrace.handleRadius A)).contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_unchangedHandle_parameters A).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  exact hd

theorem collar_pieceLevelDifferential_eq (p : boundaryPieceDomain A .collar) :
    pieceLevelDifferential A .collar (boundaryTracePoint A .collar p) =
      (collarBoundaryLevelDerivative A p).comp
        (collarParameterDerivative A (boundaryTracePoint A .collar p)) := by
  let := pieceAtlas A .collar
  let := collarChartedSpace A
  exact mfderiv_comp (boundaryTracePoint A .collar p)
    ((contMDiff_collarLevel (bump A) (UnroundedTrace.handleRadius A)).mdifferentiableAt (by simp))
    ((contMDiff_collarParameters A).mdifferentiableAt (by simp))

theorem pieceLevelDifferential_outward_negative (i : Piece) (p : boundaryPieceDomain A i)
    (w : ℝ × Vector 6)
    (hw : pieceAmbientDerivative A i (boundaryTracePoint A i p) w = outwardNormal A p.val) :
    pieceLevelDifferential A i (boundaryTracePoint A i p) w < 0 := by
  cases i with
  | cylinder =>
      let := pieceAtlas A .cylinder
      let := unchangedCylinderChartedSpace A
      let q := boundaryTracePoint A .cylinder p
      let C : (ℝ × Vector 6) →L[ℝ] (Vector 6 × ℝ) :=
        mfderiv (ProductHalfSpace.model (Vector 6)) ((𝓡 6).prod 𝓘(ℝ, ℝ))
          (fun z : cylinderOnlyPart A ↦ (unchangedCylinderHomeomorph A z).val.val) q
      have hD := congrArg (fun D : (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) ↦ D w)
        (cylinder_pieceDerivative_eq A q)
      rw [cylinder_pieceLevelDifferential_eq]
      exact cylinder_outward_lift_negative A p (C w) (hD.symm.trans hw)
  | handle =>
      let := pieceAtlas A .handle
      let := unchangedHandleChartedSpace A
      let q := boundaryTracePoint A .handle p
      let C : (ℝ × Vector 6) →L[ℝ] (Vector 4 × Vector 3) :=
        mfderiv (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, Vector 4 × Vector 3)
          (fun z : handleOnlyPart A ↦ (unchangedHandleHomeomorph A z).val.val) q
      have hD := congrArg (fun D : (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) ↦ D w)
        (handle_pieceDerivative_eq A q)
      rw [handle_pieceLevelDifferential_eq]
      exact handle_outward_lift_negative A p (C w) (hD.symm.trans hw)
  | collar =>
      let q := boundaryTracePoint A .collar p
      have hD := congrArg (fun D : (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) ↦ D w)
        (collarAmbientDerivative_eq A q)
      rw [collar_pieceLevelDifferential_eq]
      exact collar_outward_lift_negative A p (collarParameterDerivative A q w)
        (hD.symm.trans hw)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
