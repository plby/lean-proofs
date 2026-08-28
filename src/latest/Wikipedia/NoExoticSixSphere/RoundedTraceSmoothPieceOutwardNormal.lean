import Wikipedia.NoExoticSixSphere.RoundedTracePieceOutwardNormal
import Wikipedia.NoExoticSixSphere.CollarTransverseDerivative

/-!
# Smoothness of the actual outward unit normal on every native boundary piece

The collar derivative is differentiated only in its fixed transverse and
height variables, with the sphere retained as a smooth manifold parameter.
The already proved smooth normal projection then gives smooth unit normals.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_cylinderOutwardVector : letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (pieceOutwardVector A .cylinder) := by
  let := boundaryPieceAtlas A .cylinder
  have he : pieceOutwardVector A .cylinder =
      (fun p : boundaryPieceDomain A .cylinder ↦ coordinates e.ambientDimension 4
        ((0, 2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A), 0)) := by
    funext p
    change e.heightCylinderDerivative _ _ = _
    rw [e.heightCylinderDerivative_apply]
    let D : Vector 6 →L[ℝ] Vector e.ambientDimension :=
      mfderiv (𝓡 6) (𝓡 e.ambientDimension) e.toFun (cylinderBoundaryCoordinates A p).1
    change coordinates e.ambientDimension 4
      ((D 0, 2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A), 0) = _
    rw [map_zero]
  rw [he]
  have ht : ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞
      (fun p : boundaryPieceDomain A .cylinder ↦
        2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A) :=
    (contMDiff_const.mul
      (contMDiff_snd.comp (contMDiff_cylinderBoundaryCoordinates A))).sub contMDiff_const
  exact (coordinates e.ambientDimension 4).contDiff.contMDiff.comp
    ((contMDiff_const.prodMk_space ht).prodMk_space contMDiff_const)

theorem contMDiff_handleOutwardVector : letI := boundaryPieceAtlas A .handle;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (pieceOutwardVector A .handle) := by
  let := boundaryPieceAtlas A .handle
  have hc := contMDiff_handleBoundaryCoordinates A
  have hv : ContMDiff (𝓡 6) (𝓡 3) ∞
      (fun p : boundaryPieceDomain A .handle ↦ (handleBoundaryCoordinates A p).2) :=
    (ContinuousLinearMap.snd ℝ (Vector 4) (Vector 3)).contDiff.contMDiff.comp hc
  have hu : ContMDiff (𝓡 6) 𝓘(ℝ, Vector 4 × Vector 3) ∞ (handleOutwardDirection A) :=
    contMDiff_const.prodMk_space hv
  intro p
  let q := unchangedHandleHomeomorph A (boundaryTracePoint A .handle p)
  have hs : ContDiffAt ℝ ∞ A.map q.val.val := A.smooth q.val.val.1
    (ball_subset_closedBall q.property.1) q.val.val.2 (handleSuperlevel_vector_mem A q.val)
  have hD : ContMDiffAt (𝓡 6)
      𝓘(ℝ, (Vector 4 × Vector 3) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (fun p : boundaryPieceDomain A .handle ↦ fderiv ℝ A.map (handleBoundaryCoordinates A p)) p :=
    (hs.fderiv_right (by simp)).contMDiffAt.comp p (hc p)
  exact hD.clm_apply (hu p)

theorem contMDiff_collarOutwardVector : letI := boundaryPieceAtlas A .collar;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (pieceOutwardVector A .collar) := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPiece_isManifold A .collar
  have hc := contMDiff_collarBoundaryCoordinates A
  have hsource (p : boundaryPieceDomain A .collar) :
      collarBoundaryCoordinates A p ∈ A.tubeHeightCoordinates.source :=
    collarParameters_subset_source A
      ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property
  have hv : ContMDiff (𝓡 6) (𝓡 3) ∞
      (fun p : boundaryPieceDomain A .collar ↦ (collarBoundaryCoordinates A p).1.2) :=
    contMDiff_snd.comp (contMDiff_fst.comp hc)
  have hn : ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞
      (fun p : boundaryPieceDomain A .collar ↦ ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).contMDiff.comp hv
  have hne (p : boundaryPieceDomain A .collar) : (collarBoundaryCoordinates A p).1.2 ≠ 0 :=
    transverse_ne_zero_of_level_zero (bump A) (UnroundedTrace.handleRadius_pos A)
      (collarBoundary_level_zero A p)
  have hr : ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞
      (fun p : boundaryPieceDomain A .collar ↦
        (2 * ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)⁻¹) :=
    (contMDiff_const.mul hn).inv₀ (fun p ↦
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne p))))
  have hu : ContMDiff (𝓡 6) 𝓘(ℝ, Vector 3 × ℝ) ∞
      (fun p : boundaryPieceDomain A .collar ↦
        ((2 * ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)⁻¹ •
          (collarBoundaryCoordinates A p).1.2, (-1 : ℝ))) :=
    (hr.smul hv).prodMk_space contMDiff_const
  have hD : ContMDiff (𝓡 6)
      𝓘(ℝ, (Vector 3 × ℝ) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (fun p : boundaryPieceDomain A .collar ↦
        A.collarTransverseDerivative (collarBoundaryCoordinates A p)) :=
    fun p ↦ (A.contMDiffAt_collarTransverseDerivative (hsource p)).comp p (hc p)
  have he : pieceOutwardVector A .collar =
      (fun p : boundaryPieceDomain A .collar ↦
        A.collarTransverseDerivative (collarBoundaryCoordinates A p)
          ((2 * ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)⁻¹ •
            (collarBoundaryCoordinates A p).1.2, -1)) :=
    funext (fun p ↦ (A.collarTransverseDerivative_apply (hsource p)
      ((2 * ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)⁻¹ •
        (collarBoundaryCoordinates A p).1.2, -1)).symm)
  rw [he]
  exact hD.clm_apply hu

theorem contMDiff_pieceOutwardVector (i : Piece) : letI := boundaryPieceAtlas A i;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (pieceOutwardVector A i) := by
  cases i with
  | cylinder => exact contMDiff_cylinderOutwardVector A
  | handle => exact contMDiff_handleOutwardVector A
  | collar => exact contMDiff_collarOutwardVector A

theorem contMDiff_pieceOutwardNormal (i : Piece) : letI := boundaryPieceAtlas A i;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (pieceOutwardNormal A i) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A i
  have hP : ContMDiff (𝓡 6)
      𝓘(ℝ, Vector (e.ambientDimension + 6) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (fun p : boundaryPieceDomain A i ↦ boundaryNormalProjection A p.val) :=
    (contMDiff_boundaryNormalProjection A).comp ((boundaryOpenCover A).contMDiff_inclusion i)
  exact contMDiff_normalize (hP.clm_apply (contMDiff_pieceOutwardVector A i))
    (projected_pieceOutwardVector_ne_zero A i)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
