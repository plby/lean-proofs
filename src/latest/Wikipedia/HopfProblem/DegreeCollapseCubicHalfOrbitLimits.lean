import Wikipedia.HopfProblem.DegreeCollapseCubicCurveBox

/-!
# Cubic half-orbit limits and endpoint-box invariance

The correct transverse coordinate planes have the actual cubic endpoint
limits. Convergence together with the proved between-endpoints box estimate
keeps every point of the relevant half-orbit inside its endpoint box.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

/-- Vanishing of the expanding transverse coordinates gives the actual
forward endpoint limit of the complete explicit cubic curve. -/
theorem tendsto_cubicFlowCylinder_atTop (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a) (z : Fin m → ℝ)
    (hzero : ∀ i, σ i = -1 → z i = 0) :
    Tendsto (fun t => cubicFlowCylinder σ a (z, t)) atTop (𝓝 (a, (0 : Fin m → ℝ))) := by
  have hz : Tendsto (fun t : ℝ => fun i => Real.exp (-σ i * t) * z i) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    rcases hσ i with hi | hi
    · simp only [hzero i hi, mul_zero, Pi.zero_apply]
      exact tendsto_const_nhds
    · have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const (z i)
      simpa only [hi, neg_one_mul, zero_mul, Pi.zero_apply, comp_def] using hh
  exact (tendsto_cubicAxisParameter_atTop ha).prodMk_nhds hz

/-- Vanishing of the backward-expanding transverse coordinates gives the
actual backward endpoint limit. -/
theorem tendsto_cubicFlowCylinder_atBot (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a) (z : Fin m → ℝ)
    (hzero : ∀ i, σ i = 1 → z i = 0) :
    Tendsto (fun t => cubicFlowCylinder σ a (z, t)) atBot (𝓝 (-a, (0 : Fin m → ℝ))) := by
  have hz : Tendsto (fun t : ℝ => fun i => Real.exp (-σ i * t) * z i) atBot (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    rcases hσ i with hi | hi
    · have hh := Real.tendsto_exp_atBot.mul_const (z i)
      simpa only [hi, neg_neg, one_mul, zero_mul, Pi.zero_apply] using hh
    · simp only [hzero i hi, mul_zero, Pi.zero_apply]
      exact tendsto_const_nhds
  exact (tendsto_cubicAxisParameter_atBot ha).prodMk_nhds hz

/-- A convergent cubic forward half-orbit cannot leave its endpoint box,
by applying the finite-segment estimate to arbitrarily late points. -/
theorem cubicFlowCylinder_forward_stays_box (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim : Tendsto (fun t => cubicFlowCylinder σ a (z, t)) atTop
      (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    {t : ℝ} (ht : T ≤ t) :
    cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear : ∀ᶠ u in atTop, cubicFlowCylinder σ a (z, u) ∈
      ball (c, (0 : Fin m → ℝ)) r := hlim.eventually (ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (eventually_ge_atTop t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨ht, hut⟩ hT (ball_subset_closedBall hu)

/-- The same endpoint-box control holds on the backward half-orbit. -/
theorem cubicFlowCylinder_backward_stays_box (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim : Tendsto (fun t => cubicFlowCylinder σ a (z, t)) atBot
      (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    {t : ℝ} (ht : t ≤ T) :
    cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear : ∀ᶠ u in atBot, cubicFlowCylinder σ a (z, u) ∈
      ball (c, (0 : Fin m → ℝ)) r := hlim.eventually (ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (eventually_le_atBot t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨hut, ht⟩ (ball_subset_closedBall hu) hT

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
