import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceBoundaryParameterTangent
import Wikipedia.NoExoticSixSphere.CoorientedHypersurfaceNormal

/-! # The actual ambient boundary tangent image in the three superlevel coordinate systems -/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def pieceBoundaryAmbientDerivative (i : Piece) (p : boundaryPieceDomain A i) :
    Vector 7 →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1)))) := by
  let := boundaryPieceAtlas A i
  exact mfderiv (𝓡 7) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
    (fun q : boundaryPieceDomain A i ↦ q.val.val.val) p

theorem range_pieceBoundaryAmbientDerivative (i : Piece) (p : boundaryPieceDomain A i) :
    (pieceBoundaryAmbientDerivative A i p).range = (boundaryAmbientDerivative A p.val).range := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A i
  have hi := (boundaryOpenCover A).isLocalDiffeomorphAt_inclusion i p
  have hd : pieceBoundaryAmbientDerivative A i p = (boundaryAmbientDerivative A p.val).comp
      (mfderiv (𝓡 7) (𝓡 7) (Subtype.val : boundaryPieceDomain A i → Boundary A) p) :=
    mfderiv_comp p ((contMDiff_boundaryAmbientInclusion A).mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))
  rw [hd]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (hi.mfderivToContinuousLinearEquiv (by simp)).surjective)

theorem cylinderBoundaryDerivative_eq (p : boundaryPieceDomain A .cylinder) :
    letI := boundaryPieceAtlas A .cylinder;
    pieceBoundaryAmbientDerivative A .cylinder p =
      ((LowHeightCylinder.heightCylinderDerivative d e) (cylinderBoundaryCoordinates A p)).comp
        (mfderiv (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) (cylinderBoundaryCoordinates A) p) := by
  let := boundaryPieceAtlas A .cylinder
  have he : (fun q : boundaryPieceDomain A .cylinder ↦ q.val.val.val) =
      (LowHeightCylinder.heightCylinder d e) ∘ cylinderBoundaryCoordinates A := funext (fun q ↦
    (unchangedCylinderHomeomorph_ambient A (boundaryTracePoint A .cylinder q)).symm)
  change mfderiv (𝓡 7) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
    (fun q : boundaryPieceDomain A .cylinder ↦ q.val.val.val) p = _
  rw [he]
  exact mfderiv_comp p
    ((LowHeightCylinder.contMDiff_heightCylinder d e).mdifferentiableAt (by simp))
    ((contMDiff_cylinderBoundaryCoordinates A).mdifferentiableAt (by simp))

theorem handleBoundaryDerivative_eq (p : boundaryPieceDomain A .handle) :
    letI := boundaryPieceAtlas A .handle;
    pieceBoundaryAmbientDerivative A .handle p =
      (fderiv ℝ A.map (handleBoundaryCoordinates A p)).comp
        (mfderiv (𝓡 7) 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) (handleBoundaryCoordinates A) p) := by
  let := boundaryPieceAtlas A .handle
  let q := unchangedHandleHomeomorph A (boundaryTracePoint A .handle p)
  have hs : ContDiffAt ℝ ∞ A.map q.val.val := A.smooth q.val.val.1
    (ball_subset_closedBall q.property.1) q.val.val.2 (handleSuperlevel_vector_mem A q.val)
  have he : (fun q : boundaryPieceDomain A .handle ↦ q.val.val.val) =
      A.map ∘ handleBoundaryCoordinates A := funext (fun q ↦
    (unchangedHandleHomeomorph_ambient A (boundaryTracePoint A .handle q)).symm)
  change mfderiv (𝓡 7) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
    (fun q : boundaryPieceDomain A .handle ↦ q.val.val.val) p = _
  rw [he, mfderiv_comp p (hs.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_handleBoundaryCoordinates A).mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  rfl

theorem collarBoundaryDerivative_eq (p : boundaryPieceDomain A .collar) :
    letI := boundaryPieceAtlas A .collar;
    pieceBoundaryAmbientDerivative A .collar p =
      (A.collarSheetDerivative (collarBoundaryCoordinates A p)).comp
        (mfderiv (𝓡 7) (collarModel d (7 - d)) (collarBoundaryCoordinates A) p) := by
  let := boundaryPieceAtlas A .collar
  have hp := collarParameters_subset_source A
    ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have he : (fun q : boundaryPieceDomain A .collar ↦ q.val.val.val) =
      A.collarSheet ∘ collarBoundaryCoordinates A := funext (fun q ↦
    (collarHomeomorph_symm_ambient A (boundaryTracePoint A .collar q)).symm)
  change mfderiv (𝓡 7) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
    (fun q : boundaryPieceDomain A .collar ↦ q.val.val.val) p = _
  rw [he]
  exact mfderiv_comp p (hs.mdifferentiableAt (by simp))
    ((contMDiff_collarBoundaryCoordinates A).mdifferentiableAt (by simp))

theorem boundaryTangent_cylinder (p : boundaryPieceDomain A .cylinder) :
    (boundaryAmbientDerivative A p.val).range = CoorientedHypersurfaceNormal.tangent
      ((LowHeightCylinder.heightCylinderDerivative d e) (cylinderBoundaryCoordinates A p))
      (mfderiv ((𝓡 7).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A))
          (cylinderBoundaryCoordinates A p)) := by
  let := boundaryPieceAtlas A .cylinder
  let C : Vector 7 →L[ℝ] (Vector 7 × ℝ) :=
    mfderiv (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) (cylinderBoundaryCoordinates A) p
  let D := (LowHeightCylinder.heightCylinderDerivative d e) (cylinderBoundaryCoordinates A p)
  have hC : C.range = (mfderiv ((𝓡 7).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A))
        (cylinderBoundaryCoordinates A p)).ker := range_cylinderBoundaryCoordinates A p
  rw [← range_pieceBoundaryAmbientDerivative A .cylinder p, cylinderBoundaryDerivative_eq]
  change (D.comp C).range = _
  exact (LinearMap.range_comp C.toLinearMap D.toLinearMap).trans
    (congrArg (Submodule.map D.toLinearMap) hC)

theorem boundaryTangent_handle (p : boundaryPieceDomain A .handle) :
    (boundaryAmbientDerivative A p.val).range = CoorientedHypersurfaceNormal.tangent
      (fderiv ℝ A.map (handleBoundaryCoordinates A p))
      (fderiv ℝ (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)) := by
  let := boundaryPieceAtlas A .handle
  let C : Vector 7 →L[ℝ] (Vector (d + 1) × Vector (7 - d)) :=
    mfderiv (𝓡 7) 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) (handleBoundaryCoordinates A) p
  let D := fderiv ℝ A.map (handleBoundaryCoordinates A p)
  have hC : C.range =
      (fderiv ℝ (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)).ker := range_handleBoundaryCoordinates A p
  rw [← range_pieceBoundaryAmbientDerivative A .handle p, handleBoundaryDerivative_eq]
  change (D.comp C).range = _
  exact (LinearMap.range_comp C.toLinearMap D.toLinearMap).trans
    (congrArg (Submodule.map D.toLinearMap) hC)

theorem boundaryTangent_collar (p : boundaryPieceDomain A .collar) :
    (boundaryAmbientDerivative A p.val).range = CoorientedHypersurfaceNormal.tangent
      (A.collarSheetDerivative (collarBoundaryCoordinates A p))
      (mfderiv (collarModel d (7 - d)) 𝓘(ℝ, ℝ)
        (collarLevel (bump A) (UnroundedTrace.handleRadius A))
        (collarBoundaryCoordinates A p)) := by
  let := boundaryPieceAtlas A .collar
  let C : Vector 7 →L[ℝ] ((Vector d × Vector (7 - d)) × ℝ) :=
    mfderiv (𝓡 7) (collarModel d (7 - d)) (collarBoundaryCoordinates A) p
  let D := A.collarSheetDerivative (collarBoundaryCoordinates A p)
  have hC : C.range =
      (mfderiv (collarModel d (7 - d)) 𝓘(ℝ, ℝ)
        (collarLevel (bump A) (UnroundedTrace.handleRadius A))
        (collarBoundaryCoordinates A p)).ker := range_collarBoundaryCoordinates A p
  rw [← range_pieceBoundaryAmbientDerivative A .collar p, collarBoundaryDerivative_eq]
  change (D.comp C).range = _
  exact (LinearMap.range_comp C.toLinearMap D.toLinearMap).trans
    (congrArg (Submodule.map D.toLinearMap) hC)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
