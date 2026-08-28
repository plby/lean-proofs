import Wikipedia.HopfProblem.DegreeCollapseLowClosedCapBottomAnnulus

/-!

# The closed cap and exterior cover the entire actual native new end

Use the original three-piece native boundary cover. The unchanged handle
lies in the cap, the rounded zero collar is split by its recovered source
radius, and the bottom cylinder is split by the actual closed exterior.
Every comparison is an equality of the original ambient points.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

theorem mem_cap_of_ambient (hR : A.radius = 2) (y : otherBoundaryPart A)
    (hy : ∃ p : CapDomain d, capPoint A p = y.val.val.val) :
    y ∈ range (nativeCapPoint A hR) := by
  obtain ⟨p, hp⟩ := hy
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [nativeCapPoint_ambient]
  exact hp

theorem mem_exterior_of_ambient (y : otherBoundaryPart A)
    (hy : ∃ r : closedExterior A,
      LowHeightCylinder.heightCylinder d e (r.val, 0) = y.val.val.val) :
    y ∈ range (newExterior A) := by
  obtain ⟨r, hr⟩ := hy
  refine ⟨r, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [newExterior_ambient]
  exact hr

theorem cylinder_new_cover (hR : A.radius = 2) (y : nativeExteriorPart A) :
    y.val ∈ range (newExterior A) ∪ range (nativeCapPoint A hR) := by
  let z := (exteriorNativeHomeomorph A).symm y
  have he : LowHeightCylinder.heightCylinder d e (z.val, 0) = y.val.val.val.val :=
    congrArg (fun q : nativeExteriorPart A ↦ q.val.val.val.val)
      ((exteriorNativeHomeomorph A).apply_symm_apply y)
  by_cases hm : z.val ∈ closedExterior A
  · exact Or.inl (mem_exterior_of_ambient A y.val ⟨⟨z.val, hm⟩, he⟩)
  · have ht : z.val ∈ A.tube '' ((univ : Set (NoExoticSixSphere.Sphere d)) ×ˢ
        ball (0 : Vector (7 - d)) (oldRadius A)) := by
      simpa only [closedExterior, mem_compl_iff, not_not] using hm
    obtain ⟨⟨s, v⟩, hv, hsv⟩ := ht
    have hn : ‖v‖ < oldRadius A := by
      simpa only [mem_ball, dist_zero_right] using hv.2
    have hlo : outerRadius A ≤ ‖v‖ := by
      by_contra hl
      apply z.property
      refine ⟨(s, v), ⟨mem_univ _, ?_⟩, hsv⟩
      simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge hl).le
    obtain ⟨p, hp⟩ := exists_capPoint_bottom_annulus A hR s v hlo hn.le
    rw [hsv] at hp
    exact Or.inr (mem_cap_of_ambient A hR y.val ⟨p, hp.trans he⟩)

theorem handle_new_cover (hR : A.radius = 2) (y : otherBoundaryPart A)
    (hy : y.val ∈ boundaryPieceDomain A .handle) :
    y ∈ range (nativeCapPoint A hR) := by
  let := traceChartedSpace A
  let := pieceAtlas A .handle
  let bp : boundaryPieceDomain A .handle := ⟨y.val, hy⟩
  let q : handleOnlyPart A := boundaryTracePoint A .handle bp
  let z := unchangedHandleHomeomorph A q
  have hs := (piece_isBoundaryPoint_iff A .handle q).mp
    (((openCover A).isBoundaryPoint_inclusion_iff .handle q).mpr y.val.property)
  change z.val.val.2 ∈ sphere (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A) at hs
  have hn : ‖z.val.val.2‖ = 1 :=
    (mem_sphere_zero_iff_norm.mp hs).trans (handleRadius_eq_one A hR)
  let w : sphere (0 : Vector (7 - d)) 1 := ⟨z.val.val.2, mem_sphere_zero_iff_norm.mpr hn⟩
  have hx : ‖z.val.val.1‖ ≤ 1 := by
    exact (show ‖z.val.val.1‖ < 1 from by
      simpa only [mem_ball, dist_zero_right] using z.property.1).le
  have hcore : ‖z.val.val.1‖ < handleCoreRadius A := by
    have hw := (mem_unchangedHandleWindow_iff A z.val).mp z.property
    simpa only [mem_ball, dist_zero_right] using hw
  have hu : ‖z.val.val.1‖ ^ 2 - 1 ≤ -(bump A).rOut := by
    nlinarith [handleCoreRadius_sq A, handleCoreRadius_pos A, (bump A).rOut_pos,
      norm_nonneg z.val.val.1]
  obtain ⟨p, hp⟩ := exists_capPoint_handle A hR z.val.val.1 hx w hu
  have he : A.map z.val.val = y.val.val.val := unchangedHandleHomeomorph_ambient A q
  exact mem_cap_of_ambient A hR y ⟨p, hp.trans he⟩

theorem collar_new_cover (hR : A.radius = 2) (y : otherBoundaryPart A)
    (hy : y.val ∈ boundaryPieceDomain A .collar) :
    y ∈ range (newExterior A) ∪ range (nativeCapPoint A hR) := by
  let bp : boundaryPieceDomain A .collar := ⟨y.val, hy⟩
  let q : collarPart A := boundaryTracePoint A .collar bp
  let p : collarParameters A := (collarHomeomorph A).symm q
  have hz := collarBoundary_level_zero A bp
  change GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)
    (p.val.1.2, p.val.2) = 0 at hz
  rw [handleRadius_eq_one A hR] at hz
  have he : A.collarSheet p.val = y.val.val.val := collarHomeomorph_symm_ambient A q
  by_cases hr : ‖collarSource p.val‖ ≤ oldRadius A
  · obtain ⟨c, hc⟩ := exists_capPoint_collar A hR p hz hr
    exact Or.inr (mem_cap_of_ambient A hR y ⟨c, hc.trans he⟩)
  · obtain ⟨ht, hm⟩ := collar_source_large A hR p hz (lt_of_not_ge hr).le
    have hc : LowHeightCylinder.heightCylinder d e (A.tube p.val.1, 0) = y.val.val.val := by
      exact (congrArg (fun t : ℝ ↦ LowHeightCylinder.heightCylinder d e
        (A.tube p.val.1, t)) ht).symm.trans he
    exact Or.inl (mem_exterior_of_ambient A y ⟨⟨A.tube p.val.1, hm⟩, hc⟩)

theorem new_cover (hR : A.radius = 2) :
    range (newExterior A) ∪ range (nativeCapPoint A hR) = univ := by
  apply eq_univ_of_forall
  intro y
  obtain ⟨i, hi⟩ := boundaryPieceDomain_covers A y.val
  cases i with
  | cylinder => exact cylinder_new_cover A hR ⟨y, hi⟩
  | handle => exact Or.inr (handle_new_cover A hR y hi)
  | collar => exact collar_new_cover A hR y hi

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
