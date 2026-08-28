import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local flows that stay in a prescribed coordinate neighborhood

Picard–Lindelöf supplies joint continuity in initial point and time. Shrinking
that joint neighborhood keeps every trajectory inside a prescribed open set.
The derivative equations use the original vector field.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A local continuous flow, uniformly defined for nearby initial points and staying in `U`. -/
theorem exists_localFlow_in_open {v : E → E} {x₀ : E}
    (hv : ContDiffAt ℝ 1 v x₀) {U : Set E} (hU : IsOpen U) (hxU : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ ball x₀ r, α (x, 0) = x ∧
        ∀ t ∈ Ioo (-ε) ε, α (x, t) ∈ U ∧
          HasDerivAt (fun s => α (x, s)) (v (α (x, t))) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  obtain ⟨α, hα, hc⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hα hc
  have hr' : (0 : ℝ) < r := hr
  have hc₀ : ContinuousAt α (x₀, 0) := hc.continuousAt
    (prod_mem_nhds (closedBall_mem_nhds x₀ hr')
      (Icc_mem_nhds (neg_lt_zero.mpr hε) hε))
  have hα₀ : α (x₀, 0) = x₀ := (hα x₀ (mem_closedBall_self hr'.le)).1
  have hpre : α ⁻¹' U ∈ 𝓝 (x₀, 0) :=
    hc₀.preimage_mem_nhds (hU.mem_nhds (hα₀.symm ▸ hxU))
  have hD : ball x₀ (r : ℝ) ×ˢ Ioo (-ε) ε ∈ 𝓝 (x₀, 0) :=
    prod_mem_nhds (ball_mem_nhds x₀ hr') (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hD hpre)
  have hs : ball x₀ δ ×ˢ Ioo (-δ) δ ⊆
      (ball x₀ (r : ℝ) ×ˢ Ioo (-ε) ε) ∩ α ⁻¹' U := by
    intro q hq
    apply hδsub
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hq.1, by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hq.2⟩
  refine ⟨δ, hδ, δ, hδ, α, hc.mono ?_, ?_⟩
  · intro q hq
    exact ⟨ball_subset_closedBall (hs hq).1.1, Ioo_subset_Icc_self (hs hq).1.2⟩
  · intro x hx
    have hx₀ : (x, (0 : ℝ)) ∈ ball x₀ δ ×ˢ Ioo (-δ) δ :=
      ⟨hx, neg_lt_zero.mpr hδ, hδ⟩
    have hx' : x ∈ closedBall x₀ (r : ℝ) :=
      ball_subset_closedBall (hs hx₀).1.1
    refine ⟨(hα x hx').1, ?_⟩
    intro t ht
    have hq : (x, t) ∈ ball x₀ δ ×ˢ Ioo (-δ) δ := ⟨hx, ht⟩
    refine ⟨(hs hq).2, ?_⟩
    have ht' := (hs hq).1.2
    exact ((hα x hx').2 t (Ioo_subset_Icc_self ht')).hasDerivAt
      (Icc_mem_nhds ht'.1 ht'.2)

end Wikipedia.SmoothSixDPoincare.FlowConstruction
