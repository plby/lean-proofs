import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryData

/-!
# Regular-zero neighborhoods containing the original local boundary

Keep a whole closed ball inside the prescribed chart neighborhood and retain
the actual derivative estimate on every point of that ball. The half-radius
boundary lies strictly inside its open ball, and the center is the only zero.
This supplies room for the open cover used in local-to-global homology.
-/

noncomputable section

open Set Metric Topology Filter ContinuousMap
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure NeighborhoodData (f : E → F) (L : E ≃L[ℝ] F) (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  center_zero : f 0 = 0
  ball_subset : closedBall 0 radius ⊆ s
  continuous : ContinuousOn f (closedBall 0 radius)
  remainder_bound : ∀ x ∈ closedBall 0 radius, ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖

theorem nonempty_neighborhoodData {f : E → F} (L : E ≃L[ℝ] F) {s : Set E}
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) :
    Nonempty (NeighborhoodData f L s) := by
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  obtain ⟨b⟩ := nonempty_boundaryData L hf hzero (inter_mem hs (ball_mem_nhds 0 hε))
    (hc.mono inter_subset_left)
  have hbs : closedBall (0 : E) b.radius ⊆ s := b.ball_subset.trans inter_subset_left
  exact ⟨⟨b.radius, b.radius_pos, hzero, hbs, hc.mono hbs,
    fun x hx => hεb x (b.ball_subset hx).2⟩⟩

theorem nonempty_neighborhoodData_of_contDiffAt {f : E → F} (L : E ≃L[ℝ] F) {s : Set E}
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) :
    Nonempty (NeighborhoodData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨d⟩ := nonempty_neighborhoodData L hf hzero (inter_mem hs ht)
    (htc.mono inter_subset_right)
  exact ⟨{ d with ball_subset := d.ball_subset.trans inter_subset_left }⟩

namespace NeighborhoodData

variable {f : E → F} {L : E ≃L[ℝ] F} {s : Set E} (d : NeighborhoodData f L s)

theorem image_ne_zero {x : E} (hx : x ∈ closedBall 0 d.radius) (hx0 : x ≠ 0) : f x ≠ 0 :=
  LocalDegree.image_ne_zero L hx0 (d.remainder_bound x hx)

theorem image_eq_zero_iff {x : E} (hx : x ∈ closedBall 0 d.radius) : f x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx0
    exact d.image_ne_zero hx hx0 h
  · rintro rfl
    exact d.center_zero

/-- The local boundary is placed at half the neighborhood radius. -/
def innerBoundary : BoundaryData f L s := by
  have hr : 0 < d.radius / 2 := half_pos d.radius_pos
  have hballs : closedBall (0 : E) (d.radius / 2) ⊆ closedBall 0 d.radius :=
    closedBall_subset_closedBall (half_le_self d.radius_pos.le)
  have hparam (u : sphere (0 : E) 1) :
      (d.radius / 2) • (u : E) ∈ closedBall (0 : E) d.radius := by
    rw [mem_closedBall_zero_iff, norm_radius_smul (d.radius / 2) hr u]
    exact half_le_self d.radius_pos.le
  refine ⟨d.radius / 2, hr, hballs.trans d.ball_subset, ?_, ?_⟩
  · exact d.continuous.comp_continuous (continuous_const.smul continuous_subtype_val) hparam
  · exact fun u => d.remainder_bound _ (hparam u)

theorem innerBoundary_radius : d.innerBoundary.radius = d.radius / 2 := rfl

theorem innerBoundary_mem_ball (u : sphere (0 : E) 1) :
    d.innerBoundary.radius • (u : E) ∈ ball (0 : E) d.radius := by
  rw [mem_ball_zero_iff, norm_radius_smul _ d.innerBoundary.radius_pos,
    innerBoundary_radius]
  exact half_lt_self d.radius_pos

end NeighborhoodData

end Wikipedia.SmoothSixDPoincare.LocalDegree
