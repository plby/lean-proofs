import Wikipedia.NoExoticSixSphere.RoundedTraceSurgeryOverlaps
import Wikipedia.NoExoticSixSphere.RoundedTraceOutwardDirections

/-! # Actual common boundary points determine the unchanged collar branches and coordinates -/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner SmoothCornerRounding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryCollarDifference (p : boundaryPieceDomain A .collar) : ℝ :=
  (collarBoundaryCoordinates A p).2 -
    ((UnroundedTrace.handleRadius A) ^ 2 - ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)

theorem boundaryCollarDifference_parameters (p : boundaryCollarParameters A) :
    letI := boundaryPieceAtlas A .collar;
    boundaryCollarDifference A (boundaryCollarDiffeomorph A p) = p.val.2.2 := by
  let := boundaryPieceAtlas A .collar
  unfold boundaryCollarDifference
  rw [boundaryCollarDiffeomorph_coordinates]
  have he := congrArg (fun q : ℝ × ℝ ↦ q.1 - q.2)
    (coordinates_zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val.2)
  exact he.trans (graph_difference (bump A) p.val.2.2)

theorem boundaryCollarDifference_cylinder (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .cylinder) (he : p.val = q.val) :
    (bump A).rOut < boundaryCollarDifference A p := by
  let := boundaryPieceAtlas A .collar
  let z := (boundaryCollarDiffeomorph A).symm p
  have hz : boundaryCollarDiffeomorph A z = p := (boundaryCollarDiffeomorph A).apply_symm_apply p
  have hmem : (boundaryCollarDiffeomorph A z).val.val ∈ cylinderOnlyPart A := by
    rw [hz, he]
    exact q.property
  have hu := (boundaryCollar_mem_cylinder_iff A z).mp hmem
  have hd : boundaryCollarDifference A p = z.val.2.2 := by
    rw [← hz]
    exact boundaryCollarDifference_parameters A z
  rw [hd]
  linarith [(bump A).rOut_pos]

theorem boundaryCollarDifference_handle (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .handle) (he : p.val = q.val) :
    boundaryCollarDifference A p < -(bump A).rOut := by
  let := boundaryPieceAtlas A .collar
  let z := (boundaryCollarDiffeomorph A).symm p
  have hz : boundaryCollarDiffeomorph A z = p := (boundaryCollarDiffeomorph A).apply_symm_apply p
  have hmem : (boundaryCollarDiffeomorph A z).val.val ∈ handleOnlyPart A := by
    rw [hz, he]
    exact q.property
  have hu := (boundaryCollar_mem_handle_iff A z).mp hmem
  have hd : boundaryCollarDifference A p = z.val.2.2 := by
    rw [← hz]
    exact boundaryCollarDifference_parameters A z
  rw [hd]
  linarith [(bump A).rOut_pos]

theorem cylinderBoundary_zero_of_collar (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .cylinder) (he : p.val = q.val) :
    (cylinderBoundaryCoordinates A q).2 = 0 :=
  (cylinderBoundary_mem_other_iff A q).mp (he ▸ collarBoundary_mem_other A p)

theorem handle_collar_boundary_coordinates (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .handle) (he : p.val = q.val) :
    collarBoundaryCoordinates A p =
      ((SphereRadialRetraction.retract (pole 3) (handleBoundaryCoordinates A q).1,
        (handleBoundaryCoordinates A q).2), ‖(handleBoundaryCoordinates A q).1‖ ^ 2 - 1) := by
  let qh := unchangedHandleHomeomorph A (boundaryTracePoint A .handle q)
  have hc := handle_collar_coordinate_eq A (boundaryTracePoint A .handle q)
    (boundaryTracePoint A .collar p) (congrArg Subtype.val he.symm)
  have ht := congrArg Prod.snd hc
  have hm := congrArg Prod.fst hc
  have hvh : (handleBoundaryCoordinates A q).2 ∈ closedBall (0 : Vector 3) A.radius :=
    handleSuperlevel_vector_mem A qh.val
  have hvc : (collarBoundaryCoordinates A p).1.2 ∈ closedBall (0 : Vector 3) A.radius :=
    ball_subset_closedBall ((A.mem_tubeHeightCoordinates_source _).mp
      (collarParameters_subset_source A
        ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property))
  have hp : (SphereRadialRetraction.retract (pole 3) (handleBoundaryCoordinates A q).1,
      (⟨(handleBoundaryCoordinates A q).2, hvh⟩ : closedBall (0 : Vector 3) A.radius)) =
      ((collarBoundaryCoordinates A p).1.1, ⟨(collarBoundaryCoordinates A p).1.2, hvc⟩) :=
    A.tube_embedded.injective hm
  have hs := congrArg Prod.fst hp
  have hv := congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) A.radius ↦ z.2.val) hp
  exact Prod.ext (Prod.ext hs.symm hv.symm) ht.symm

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
