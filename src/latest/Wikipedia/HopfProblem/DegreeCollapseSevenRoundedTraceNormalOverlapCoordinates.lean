import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceOutwardDirections

/-!
# Direct collar-branch bounds from the actual rounding support

A boundary point in an unchanged cylinder or handle piece is excluded from
the added compact rounding region. Its actual height and transverse radius
therefore place it strictly in the corresponding unchanged branch. No separate
parametrization of the surgery end is needed for this normal comparison.
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

def boundaryCollarDifference (p : boundaryPieceDomain A .collar) : ℝ :=
  (collarBoundaryCoordinates A p).2 -
    ((UnroundedTrace.handleRadius A) ^ 2 - ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)

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
  have hvh : (handleBoundaryCoordinates A q).2 ∈ closedBall (0 : Vector 4) A.radius :=
    handleSuperlevel_vector_mem A qh.val
  have hvc : (collarBoundaryCoordinates A p).1.2 ∈ closedBall (0 : Vector 4) A.radius :=
    ball_subset_closedBall ((A.mem_tubeHeightCoordinates_source _).mp
      (collarParameters_subset_source A
        ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property))
  have hp : (SphereRadialRetraction.retract (pole 3) (handleBoundaryCoordinates A q).1,
      (⟨(handleBoundaryCoordinates A q).2, hvh⟩ : closedBall (0 : Vector 4) A.radius)) =
      ((collarBoundaryCoordinates A p).1.1, ⟨(collarBoundaryCoordinates A p).1.2, hvc⟩) :=
    A.tube_embedded.injective hm
  have hs := congrArg Prod.fst hp
  have hv := congrArg (fun z : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦ z.2.val) hp
  exact Prod.ext (Prod.ext hs.symm hv.symm) ht.symm

theorem boundaryCollarDifference_cylinder (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .cylinder) (he : p.val = q.val) :
    (bump A).rOut < boundaryCollarDifference A p := by
  let z := collarBoundaryCoordinates A p
  have hc := cylinder_collar_coordinate_eq A (boundaryTracePoint A .cylinder q)
    (boundaryTracePoint A .collar p) (congrArg Subtype.val he.symm)
  have ht : (cylinderBoundaryCoordinates A q).2 = z.2 := congrArg Prod.snd hc
  have ht0 : z.2 = 0 := ht.symm.trans (cylinderBoundary_zero_of_collar A p q he)
  have hzpoint : A.collarSheet z = q.val.val.val :=
    (collarHomeomorph_symm_ambient A (boundaryTracePoint A .collar p)).trans
      (congrArg (fun b : Boundary A ↦ b.val.val) he)
  have hvnot : z.1.2 ∉ closedBall (0 : Vector 4) (outerRadius A) := by
    intro hv
    apply q.property
    apply Or.inr
    refine ⟨z, ⟨hv, ?_, ?_⟩, hzpoint⟩
    · rw [ht0]
      exact ⟨by linarith [(bump A).rOut_pos], le_rfl⟩
    · exact (collarBoundary_level_zero A p).ge
  have hv : outerRadius A < ‖z.1.2‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hvnot
  change (bump A).rOut < z.2 - ((UnroundedTrace.handleRadius A) ^ 2 - ‖z.1.2‖ ^ 2)
  rw [ht0]
  nlinarith [outerRadius_sq A, outerRadius_nonneg A, norm_nonneg z.1.2, (bump A).rOut_pos]

theorem boundaryCollarDifference_handle (p : boundaryPieceDomain A .collar)
    (q : boundaryPieceDomain A .handle) (he : p.val = q.val) :
    boundaryCollarDifference A p < -(bump A).rOut := by
  let z := collarBoundaryCoordinates A p
  have hvc : z.1.2 = (handleBoundaryCoordinates A q).2 :=
    congrArg (fun c : Collar ↦ c.1.2) (handle_collar_boundary_coordinates A p q he)
  have hn : ‖z.1.2‖ = UnroundedTrace.handleRadius A := by
    rw [hvc]
    simpa only [mem_sphere, dist_zero_right] using
      (EightDimensionalHandleSuperlevel.zero_iff (UnroundedTrace.handleRadius_pos A) _).mp
        (handleBoundary_level_zero A q)
  have hv : z.1.2 ∈ closedBall (0 : Vector 4) (outerRadius A) := by
    rw [mem_closedBall, dist_zero_right, hn]
    exact (outerRadius_gt_handle A).le
  have hzpoint : A.collarSheet z = q.val.val.val :=
    (collarHomeomorph_symm_ambient A (boundaryTracePoint A .collar p)).trans
      (congrArg (fun b : Boundary A ↦ b.val.val) he)
  have ht : z.2 < -2 * (bump A).rOut := by
    by_contra h
    apply q.property
    apply Or.inr
    exact ⟨z, ⟨hv, ⟨le_of_not_gt h, collarBoundary_height_nonpos A p⟩,
      (collarBoundary_level_zero A p).ge⟩, hzpoint⟩
  change z.2 - ((UnroundedTrace.handleRadius A) ^ 2 - ‖z.1.2‖ ^ 2) < -(bump A).rOut
  rw [hn]
  linarith [(bump A).rOut_pos]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
