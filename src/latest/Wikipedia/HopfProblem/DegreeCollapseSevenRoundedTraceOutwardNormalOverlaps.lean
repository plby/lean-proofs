import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceSmoothPieceOutwardNormal
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceNormalOverlapCoordinates
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedCornerBranchDifferential
import Wikipedia.HopfProblem.DegreeCollapseSevenCollarSheetNormalDirections

/-!
# Exact agreement of the actual outward unit normals

On each overlap the other piece's actual outward vector is written in the
collar-sheet tangent coordinates. Both vectors have negative defining
differential, so their normalized boundary-normal projections coincide.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem normalized_collarVector (p : boundaryPieceDomain A .collar)
    (w : (Vector 3 × Vector 4) × ℝ) :
    NormedSpace.normalize (boundaryNormalProjection A p.val
      (A.collarSheetDerivative (collarBoundaryCoordinates A p) w)) =
      CoorientedHypersurfaceNormal.unitNormal
        (A.collarSheetDerivative (collarBoundaryCoordinates A p))
        (collarBoundaryLevelDerivative A p) w := by
  simp only [boundaryNormalProjection_eq, boundaryTangent_collar]
  rfl

theorem collar_cylinder_outwardVector (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .cylinder) (he : p.val = q.val) :
    pieceOutwardVector A .cylinder q =
      A.collarSheetDerivative (collarBoundaryCoordinates A p)
        ((0, 0), -UnroundedTrace.height A) := by
  have hp := collarParameters_subset_source A
    ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property
  have hdir : cylinderOutwardDirection A q = (0, -UnroundedTrace.height A) := by
    apply Prod.ext
    · rfl
    · change 2 * (cylinderBoundaryCoordinates A q).2 - UnroundedTrace.height A = _
      rw [cylinderBoundary_zero_of_collar A p q he]
      ring
  change (HeightCylinder.heightCylinderDerivative e) (cylinderBoundaryCoordinates A q) _ = _
  rw [hdir, (SevenSurgery.heightCylinderDerivative_vertical e)]
  exact (A.collarSheetDerivative_vertical hp _).symm

theorem collar_cylinder_outwardNormal (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .cylinder) (he : p.val = q.val) :
    pieceOutwardNormal A .collar p = pieceOutwardNormal A .cylinder q := by
  let D := A.collarSheetDerivative (collarBoundaryCoordinates A p)
  let L := collarBoundaryLevelDerivative A p
  let w : (Vector 3 × Vector 4) × ℝ := ((0, 0), -UnroundedTrace.height A)
  have hd : L w = 2 * (-UnroundedTrace.height A) :=
    collarDifferential_of_right (bump A) (UnroundedTrace.handleRadius A)
      (collarBoundaryCoordinates A p) (boundaryCollarDifference_cylinder A p q he) w
  have hw : L w < 0 := by rw [hd]; linarith [UnroundedTrace.height_pos A]
  have hn := CoorientedHypersurfaceNormal.unitNormal_eq_of_negative D L
    (collarOutwardDirection A p) w (collarOutwardDirection_negative A p) hw
  have hq : pieceOutwardNormal A .cylinder q = CoorientedHypersurfaceNormal.unitNormal D L w := by
    change NormedSpace.normalize
      (boundaryNormalProjection A q.val (pieceOutwardVector A .cylinder q)) = _
    rw [← he, collar_cylinder_outwardVector A p q he]
    exact normalized_collarVector A p w
  exact (normalized_collarVector A p (collarOutwardDirection A p)).trans (hn.trans hq.symm)

theorem collar_handle_outwardVector (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .handle) (he : p.val = q.val) :
    pieceOutwardVector A .handle q = A.collarSheetDerivative (collarBoundaryCoordinates A p)
      ((0, (collarBoundaryCoordinates A p).1.2), 0) := by
  let z := unchangedHandleHomeomorph A (boundaryTracePoint A .handle q)
  have hi := handle_collar_inner_lt A (boundaryTracePoint A .handle q)
    (boundaryTracePoint A .collar p) (congrArg Subtype.val he.symm)
  have hv : (handleBoundaryCoordinates A q).2 ∈ ball (0 : Vector 4) A.radius :=
    (closedBall_subset_ball (UnroundedTrace.handleRadius_lt A))
      (handleSuperlevel_transverse A z.val)
  have hc := handle_collar_boundary_coordinates A p q he
  have hd := A.map_transverseDerivative_eq_sheet (x := (handleBoundaryCoordinates A q).1)
    (ball_subset_closedBall z.property.1) hi.le hv (handleBoundaryCoordinates A q).2
  rw [← hc] at hd
  have hvc := congrArg (fun r : Collar ↦ r.1.2) hc
  change fderiv ℝ A.map (handleBoundaryCoordinates A q) (0, (handleBoundaryCoordinates A q).2) = _
  rw [hvc]
  exact hd

theorem collar_handle_outwardNormal (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .handle) (he : p.val = q.val) :
    pieceOutwardNormal A .collar p = pieceOutwardNormal A .handle q := by
  let D := A.collarSheetDerivative (collarBoundaryCoordinates A p)
  let L := collarBoundaryLevelDerivative A p
  let w : (Vector 3 × Vector 4) × ℝ := ((0, (collarBoundaryCoordinates A p).1.2), 0)
  have hd : L w = -4 * inner ℝ (collarBoundaryCoordinates A p).1.2
      (collarBoundaryCoordinates A p).1.2 :=
    collarDifferential_of_left (bump A) (UnroundedTrace.handleRadius A)
      (collarBoundaryCoordinates A p) (boundaryCollarDifference_handle A p q he) w
  have hne : (collarBoundaryCoordinates A p).1.2 ≠ 0 :=
    GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero (bump A) (UnroundedTrace.handleRadius_pos A)
      (collarBoundary_level_zero A p)
  have hw : L w < 0 := by
    rw [hd, real_inner_self_eq_norm_sq]
    nlinarith [norm_pos_iff.mpr hne]
  have hn := CoorientedHypersurfaceNormal.unitNormal_eq_of_negative D L
    (collarOutwardDirection A p) w (collarOutwardDirection_negative A p) hw
  have hq : pieceOutwardNormal A .handle q = CoorientedHypersurfaceNormal.unitNormal D L w := by
    change NormedSpace.normalize (boundaryNormalProjection A q.val (pieceOutwardVector A .handle q))
      = _
    rw [← he, collar_handle_outwardVector A p q he]
    exact normalized_collarVector A p w
  exact (normalized_collarVector A p (collarOutwardDirection A p)).trans (hn.trans hq.symm)

theorem pieceOutwardNormal_agree (i j : Piece) (p : boundaryPieceDomain A i)
    (q : boundaryPieceDomain A j) (he : p.val = q.val) :
    pieceOutwardNormal A i p = pieceOutwardNormal A j q := by
  cases i with
  | cylinder =>
      cases j with
      | cylinder => exact congrArg (pieceOutwardNormal A .cylinder) (Subtype.ext he)
      | handle => exact (cylinder_handle_ne A (boundaryTracePoint A .cylinder p)
          (boundaryTracePoint A .handle q) (congrArg Subtype.val he)).elim
      | collar => exact (collar_cylinder_outwardNormal A q p he.symm).symm
  | handle =>
      cases j with
      | cylinder => exact (cylinder_handle_ne A (boundaryTracePoint A .cylinder q)
          (boundaryTracePoint A .handle p) (congrArg Subtype.val he.symm)).elim
      | handle => exact congrArg (pieceOutwardNormal A .handle) (Subtype.ext he)
      | collar => exact (collar_handle_outwardNormal A q p he.symm).symm
  | collar =>
      cases j with
      | cylinder => exact collar_cylinder_outwardNormal A p q he
      | handle => exact collar_handle_outwardNormal A p q he
      | collar => exact congrArg (pieceOutwardNormal A .collar) (Subtype.ext he)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
