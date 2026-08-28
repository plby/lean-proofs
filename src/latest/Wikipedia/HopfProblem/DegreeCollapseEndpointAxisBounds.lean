import Wikipedia.HopfProblem.DegreeCollapseCubicHalfOrbitLimits

/-!
# Whole endpoint-axis segments and their exact clock bounds

The actual cubic longitudinal coordinate is strictly increasing. A cut
inside an endpoint box therefore controls the complete axis segment up
to that endpoint, including the critical point, and the inverse clock
has the required one-sided bound throughout the regular segment.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem strictMono_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    StrictMono (cubicAxisParameter a) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left
    (strictMono_tanh (mul_lt_mul_of_pos_left hst ha)) ha

variable {m : ℕ}

theorem tendsto_cubicFlowCylinder_axis_atTop (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => cubicFlowCylinder σ a (0, t)) atTop
      (𝓝 (a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atTop (m := m) ha

theorem tendsto_cubicFlowCylinder_axis_atBot (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => cubicFlowCylinder σ a (0, t)) atBot
      (𝓝 (-a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atBot (m := m) ha

theorem cubicFlowCylinder_zero_clock (σ : Fin m → ℝ) {a s : ℝ} (ha : 0 < a)
    (hs : s ∈ Ioo (-a) a) :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
  rw [cubicFlowCylinder_axis]
  change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
  rw [cubicAxisParameter_clock ha hs]

theorem incoming_axis_segment_in_box (σ : Fin m → ℝ) {a r T : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ closedBall (a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Icc (cubicAxisParameter a T) a,
      (s, (0 : Fin m → ℝ)) ∈ closedBall (a, (0 : Fin m → ℝ)) r ∧
      (s < a → T ≤ cubicAxisClock a s) := by
  intro s hs
  rcases hs.2.lt_or_eq with hsa | hsa
  · have hs' : s ∈ Ioo (-a) a := ⟨(cubicAxisParameter_mem ha T).1.trans_le hs.1, hsa⟩
    have ht : T ≤ cubicAxisClock a s := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.1
    have hb := cubicFlowCylinder_forward_stays_box σ ha 0 hr
      (tendsto_cubicFlowCylinder_axis_atTop σ ha) hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩
  · subst s
    exact ⟨mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩

theorem outgoing_axis_segment_in_box (σ : Fin m → ℝ) {a r T : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ closedBall (-a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Icc (-a) (cubicAxisParameter a T),
      (s, (0 : Fin m → ℝ)) ∈ closedBall (-a, (0 : Fin m → ℝ)) r ∧
      (-a < s → cubicAxisClock a s ≤ T) := by
  intro s hs
  rcases hs.1.eq_or_lt with has | has
  · subst s
    exact ⟨mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩
  · have hs' : s ∈ Ioo (-a) a := ⟨has, hs.2.trans_lt (cubicAxisParameter_mem ha T).2⟩
    have ht : cubicAxisClock a s ≤ T := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.2
    have hb := cubicFlowCylinder_backward_stays_box σ ha 0 hr
      (tendsto_cubicFlowCylinder_axis_atBot σ ha) hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
