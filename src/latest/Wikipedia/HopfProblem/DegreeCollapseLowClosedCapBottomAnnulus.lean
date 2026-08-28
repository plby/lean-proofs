import Wikipedia.HopfProblem.DegreeCollapseLowClosedCapCollarInverse

/-!

# The retained bottom annulus is covered by the actual closed cap

Outside the full rounding radius, the height-zero tube lies on the
unchanged right branch of the rounded zero graph. Its recovered source
radius is exactly its transverse norm. Up to the closed face radius these
points therefore have actual cap preimages.
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

theorem bottom_level_zero (hR : A.radius = 2) (v : Vector (7 - d))
    (hv : outerRadius A ≤ ‖v‖) :
    GeneralRoundedHandleCorner.level (bump A) 1 (v, 0) = 0 := by
  let u := ‖v‖ ^ 2 - 1
  have hs := outerRadius_sq A
  rw [handleRadius_eq_one A hR] at hs
  have hu : (bump A).rOut ≤ u := by
    dsimp only [u]
    nlinarith [outerRadius_nonneg A, norm_nonneg v, (bump A).rOut_pos]
  have hg : SmoothCornerRounding.graph (bump A) u = ((0 : ℝ), (1 : ℝ) ^ 2 - ‖v‖ ^ 2) := by
    apply Prod.ext
    · exact SmoothCornerRounding.graphHeight_of_right (bump A) hu
    · change SmoothCornerRounding.graphRadial (bump A) u = _
      rw [SmoothCornerRounding.graphRadial_of_right (bump A) hu]
      dsimp only [u]
      ring
  change SmoothCornerRounding.level (bump A) ((0 : ℝ), (1 : ℝ) ^ 2 - ‖v‖ ^ 2) = 0
  rw [← hg]
  exact SmoothCornerRounding.level_graph (bump A) u

theorem collarSource_bottom_norm (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    ‖collarSource ((s, v), 0)‖ = ‖v‖ := by
  rw [collarSource, LowRadialHeightCoordinates.norm_point]
  change Real.sqrt (1 + (0 - ((1 : ℝ) ^ 2 - ‖v‖ ^ 2))) = ‖v‖
  have he : 1 + (0 - ((1 : ℝ) ^ 2 - ‖v‖ ^ 2)) = ‖v‖ ^ 2 := by ring
  rw [he, Real.sqrt_sq (norm_nonneg v)]

theorem exists_capPoint_bottom_annulus (hR : A.radius = 2) (s : NoExoticSixSphere.Sphere d)
    (v : Vector (7 - d)) (hvlo : outerRadius A ≤ ‖v‖) (hvhi : ‖v‖ ≤ oldRadius A) :
    ∃ c : CapDomain d, capPoint A c =
      LowHeightCylinder.heightCylinder d e (A.tube (s, v), 0) := by
  have hv : v ∈ ball (0 : Vector (7 - d)) A.radius := by
    rw [mem_ball, dist_zero_right]
    exact hvhi.trans_lt (oldRadius_lt A)
  have hzero := bottom_level_zero A hR v hvlo
  let p : collarParameters A :=
    ⟨((s, v), 0), hv, ⟨neg_neg_of_pos (collarHeight_pos A), collarHeight_pos A⟩, by
      rw [handleRadius_eq_one A hR, hzero]⟩
  have hr : ‖collarSource p.val‖ ≤ oldRadius A := by
    change ‖collarSource ((s, v), 0)‖ ≤ oldRadius A
    rw [collarSource_bottom_norm]
    exact hvhi
  exact exists_capPoint_collar A hR p hzero hr

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
