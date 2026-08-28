import Wikipedia.HopfProblem.DegreeCollapseLowClosedCapInverseCoordinates

/-!

# Recovering cap points from the actual rounded zero collar

The difference coordinate of a native zero-level collar point is greater
than the lower collar bound. Its source radius therefore stays strictly
outside the original inner disk. If that radius is at most the face radius,
the actual inverse graph coordinates give a preimage in the glued cap.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def collarDifference (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) : ℝ :=
  p.2 - ((1 : ℝ) ^ 2 - ‖p.1.2‖ ^ 2)

def collarSource (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) : Vector (d + 1) :=
  LowRadialHeightCoordinates.point (p.1.1, collarDifference p)

theorem collarGraph_height (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.1.2, p.2) = 0) :
    SmoothCornerRounding.graphHeight (bump A) (collarDifference p) = p.2 :=
  congrArg (Prod.fst : ℝ × ℝ → ℝ) (SmoothCornerRounding.graph_of_level_zero (bump A) hp)

theorem collarGraph_radial (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.1.2, p.2) = 0) :
    SmoothCornerRounding.graphRadial (bump A) (collarDifference p) =
      (1 : ℝ) ^ 2 - ‖p.1.2‖ ^ 2 :=
  congrArg (Prod.snd : ℝ × ℝ → ℝ) (SmoothCornerRounding.graph_of_level_zero (bump A) hp)

theorem collarDifference_gt_neg_height (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0) :
    -collarHeight A < collarDifference p.val := by
  have hd := SmoothCornerRounding.graph_difference (bump A) (collarDifference p.val)
  change SmoothCornerRounding.graphHeight (bump A) (collarDifference p.val) -
    SmoothCornerRounding.graphRadial (bump A) (collarDifference p.val) =
      collarDifference p.val at hd
  rw [collarGraph_height A p.val hp] at hd
  linarith [p.property.2.1.1,
    SmoothCornerRounding.graphRadial_nonpos (bump A) (collarDifference p.val)]

theorem collarDifference_gt_neg_one (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0) :
    -1 < collarDifference p.val := by
  nlinarith [collarDifference_gt_neg_height A p hp, collarHeight_lt_gap A,
    sq_nonneg A.innerRadius]

theorem collarSource_norm_sq (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0) :
    ‖collarSource p.val‖ ^ 2 = 1 + collarDifference p.val := by
  rw [collarSource, LowRadialHeightCoordinates.norm_point]
  exact Real.sq_sqrt (by linarith [collarDifference_gt_neg_one A p hp])

theorem collarSource_norm_gt_inner (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0) :
    A.innerRadius < ‖collarSource p.val‖ := by
  nlinarith [collarSource_norm_sq A p hp, collarDifference_gt_neg_height A p hp,
    collarHeight_lt_gap A, norm_nonneg (collarSource p.val), A.innerRadius_pos]

theorem collarSource_retract (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0) :
    SphereRadialRetraction.retract (spherePole d) (collarSource p.val) = p.val.1.1 :=
  LowRadialHeightCoordinates.retract_point (spherePole d) (collarDifference_gt_neg_one A p hp)

theorem exists_capPoint_collar (hR : A.radius = 2) (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0)
    (hr : ‖collarSource p.val‖ ≤ oldRadius A) :
    ∃ c : CapDomain d, capPoint A c = A.collarSheet p.val := by
  let z := LowRoundedZeroPoint.parameters (bump A) (by norm_num : (0 : ℝ) < 1)
    ⟨(p.val.1.2, p.val.2), hp⟩
  have hz : LowRoundedZeroPoint.point (bump A) 1 z = (p.val.1.2, p.val.2) :=
    LowRoundedZeroPoint.point_parameters (bump A) (by norm_num : (0 : ℝ) < 1) _
  let c := capFromDisk A (collarSource p.val) hr z.1
  have hx : capDisk A c = collarSource p.val := capDisk_fromDisk A _ hr z.1
  have hu : capParameter A c = collarDifference p.val := by
    rw [capParameter, hx]
    nlinarith [collarSource_norm_sq A p hp]
  have hc : capCollar A c = p.val := by
    change ((SphereRadialRetraction.retract (spherePole d) (capDisk A c),
      (LowRoundedZeroPoint.point (bump A) 1 (z.1, capParameter A c)).1),
        (LowRoundedZeroPoint.point (bump A) 1 (z.1, capParameter A c)).2) = p.val
    rw [hx, hu, collarSource_retract A p hp]
    change ((p.val.1.1, (LowRoundedZeroPoint.point (bump A) 1 z).1),
      (LowRoundedZeroPoint.point (bump A) 1 z).2) = p.val
    rw [hz]
  have hi : A.innerRadius ≤ ‖capDisk A c‖ := by
    rw [hx]
    exact (collarSource_norm_gt_inner A p hp).le
  refine ⟨c, ?_⟩
  rw [capPoint_eq_outer_of_innerRadius_le A hR c hi, capOuter, hc]

theorem collar_source_large (hR : A.radius = 2) (p : collarParameters A)
    (hp : GeneralRoundedHandleCorner.level (bump A) 1 (p.val.1.2, p.val.2) = 0)
    (hr : oldRadius A ≤ ‖collarSource p.val‖) :
    p.val.2 = 0 ∧ A.tube p.val.1 ∈ closedExterior A := by
  have hu : (bump A).rOut ≤ collarDifference p.val := by
    nlinarith [collarSource_norm_sq A p hp, oldParameter_gt_twice_outer A hR,
      oldRadius_pos A, norm_nonneg (collarSource p.val), (bump A).rOut_pos]
  have ht : p.val.2 = 0 := (collarGraph_height A p.val hp).symm.trans
    (SmoothCornerRounding.graphHeight_of_right (bump A) hu)
  have hg := collarGraph_radial A p.val hp
  rw [SmoothCornerRounding.graphRadial_of_right (bump A) hu] at hg
  have hn : ‖p.val.1.2‖ = ‖collarSource p.val‖ := by
    nlinarith [collarSource_norm_sq A p hp, norm_nonneg p.val.1.2,
      norm_nonneg (collarSource p.val)]
  refine ⟨ht, (tube_mem_closedExterior_iff A p.val.1.1 p.property.1).mpr ?_⟩
  rw [hn]
  exact hr

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
