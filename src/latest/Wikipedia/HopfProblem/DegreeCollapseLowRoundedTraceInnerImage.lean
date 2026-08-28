import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceSupport

/-!

# Separating the actual rounded collar from the compact inner handle

The rounded set outside the compact inner handle image lies in the original
height cylinder. Every point of the uniform collar sheet avoids that inner
image, including all points added by rounding. This provides an actual open
piece of the rounded set, rather than only a membership test on a sheet.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def innerImage : Set (Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :=
  A.map '' (closedBall (0 : Vector (d + 1)) A.innerRadius ×ˢ
    closedBall (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A))

omit [CompactSpace M] in
theorem isCompact_innerImage : IsCompact (innerImage A) := by
  apply ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image_of_continuousOn
  intro p hp
  exact (A.smooth p.1 ((closedBall_subset_closedBall A.innerRadius_lt_one.le) hp.1)
    p.2 ((closedBall_subset_closedBall (UnroundedTrace.handleRadius_lt A).le)
      hp.2)).continuousAt.continuousWithinAt

omit [CompactSpace M] in
theorem isClosed_innerImage : IsClosed (innerImage A) := (isCompact_innerImage A).isClosed

theorem innerImage_subset_unrounded : innerImage A ⊆ UnroundedTrace.ambientSet A := by
  rintro _ ⟨⟨x, v⟩, hp, rfl⟩
  exact Or.inr ⟨(⟨x, (closedBall_subset_closedBall A.innerRadius_lt_one.le) hp.1⟩,
    ⟨v, hp.2⟩), rfl⟩

theorem outside_inner_in_cylinder {y : Vector (e.ambientDimension + (1 + (1 + (d + 1))))}
    (hy : y ∈ ambientSet A) (hi : y ∉ innerImage A) :
    y ∈ range (LowHeightCylinder.heightCylinder d e) := by
  rcases hy with (⟨q, rfl⟩ | ⟨p, rfl⟩) | ⟨q, hq, rfl⟩
  · exact ⟨(q.1, q.2.val), rfl⟩
  · have hx : A.innerRadius ≤ ‖p.1.val‖ := by
      by_contra h
      apply hi
      refine ⟨(p.1.val, p.2.val), ⟨?_, p.2.property⟩, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge h).le
    exact ⟨A.collarCoordinates (p.1.val, p.2.val),
      (A.map_eq_cylinder_collarCoordinates p.1.property hx
        (UnroundedTrace.handle_vector_mem A p)).symm⟩
  · exact ⟨A.tubeHeightCoordinates q, rfl⟩

theorem sheet_band_avoids_inner (s : NoExoticSixSphere.Sphere d) {v : Vector (7 - d)}
    (hv : v ∈ ball (0 : Vector (7 - d)) A.radius) {t : ℝ} (ht : ‖t‖ ≤ collarHeight A) :
    A.collarSheet ((s, v), t) ∉ innerImage A := by
  rintro ⟨⟨x, w⟩, hp, he⟩
  have hx : x ∈ closedBall (0 : Vector (d + 1)) 1 :=
    (closedBall_subset_closedBall A.innerRadius_lt_one.le) hp.1
  have hw : w ∈ closedBall (0 : Vector (7 - d)) A.radius :=
    (closedBall_subset_closedBall (UnroundedTrace.handleRadius_lt A).le) hp.2
  have hxnorm : ‖x‖ ≤ A.innerRadius := by
    simpa only [mem_closedBall, dist_zero_right] using hp.1
  have htbound : -collarHeight A ≤ t ∧ t ≤ collarHeight A :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using ht)
  by_cases hti : 0 ≤ t
  · have htI : t ∈ Icc (0 : ℝ) (UnroundedTrace.height A) :=
      ⟨hti, htbound.2.trans (collarHeight_lt_height A).le⟩
    obtain ⟨z, hz, _, _⟩ :=
      (UnroundedTrace.intersection_iff A hx hw (A.tube (s, v)) htI).mp he
    rw [← hz, ClosedHemisphere.unit_norm] at hxnorm
    exact (not_le_of_gt A.innerRadius_lt_one) hxnorm
  · have hlo : A.innerRadius ^ 2 - 1 < t := by
      linarith [collarHeight_lt_gap A, htbound.1]
    have hx0 := A.radialPoint_mem_collar s hlo.le (le_of_not_ge hti)
    have hmap := A.map_radialPoint_eq_sheet s (ball_subset_closedBall hv) hlo.le
      (le_of_not_ge hti)
    have hpq :
        ((⟨x, hx⟩, ⟨w, hw⟩) : closedBall (0 : Vector (d + 1)) 1 ×
          closedBall (0 : Vector (7 - d)) A.radius) =
        (⟨LowRadialHeightCoordinates.point (s, t), hx0.1⟩,
          ⟨v, ball_subset_closedBall hv⟩) := A.embedded.injective (he.trans hmap.symm)
    have hx0eq : x = LowRadialHeightCoordinates.point (s, t) := congrArg
      (fun p : closedBall (0 : Vector (d + 1)) 1 ×
        closedBall (0 : Vector (7 - d)) A.radius ↦ p.1.val) hpq
    rw [hx0eq] at hxnorm
    exact (not_le_of_gt (A.radialPoint_norm_gt s hlo)) hxnorm

theorem addedImage_avoids_inner {y : Vector (e.ambientDimension + (1 + (1 + (d + 1))))}
    (hy : y ∈ A.collarSheet '' addedParameters A) : y ∉ innerImage A := by
  obtain ⟨p, hp, rfl⟩ := hy
  have hv : p.1.2 ∈ ball (0 : Vector (7 - d)) A.radius :=
    (closedBall_subset_ball (outerRadius_lt A)) hp.1
  have ht : ‖p.2‖ ≤ collarHeight A := by
    rw [Real.norm_eq_abs, abs_of_nonpos hp.2.1.2]
    linarith [hp.2.1.1, twice_outer_lt_height A]
  exact sheet_band_avoids_inner A p.1.1 hv ht

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
