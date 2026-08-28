import Wikipedia.SmoothSixDPoincare.SmoothImplicitFlowCurve
import Wikipedia.SmoothSixDPoincare.RescaledFlowCurve
import Wikipedia.SmoothSixDPoincare.EuclideanLocalFlow

/-!
# Jointly smooth local flows in a prescribed open set

The existing Picard--Lindelöf trajectories stay close enough to the constant
curve to lie in the implicit graph chart. The integral equation and the
chart's exact inverse identity identify their endpoints with a jointly
smooth function. The resulting time derivative is still the original
vector field, not merely an equation in the auxiliary curve parameter.
-/

noncomputable section

open Set Metric Filter Topology ContinuousMap
open scoped ContDiff unitInterval

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

open FunctionSpaceCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_localFlow_in_open {v : E → E} (hv : ContDiff ℝ ∞ v)
    {x₀ : E} {U : Set E} (hU : IsOpen U) (hxU : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContDiffOn ℝ ∞ α (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ ball x₀ r, α (x, 0) = x ∧
        ∀ t ∈ Ioo (-ε) ε, α (x, t) ∈ U ∧
          HasDerivAt (fun s => α (x, s)) (v (α (x, t))) t := by
  let v₀ : C(E, E) := ⟨v, hv.continuous⟩
  let g := flowGraphChart v₀ hv x₀
  have hbase : ((x₀, 0), ContinuousMap.const I x₀) ∈ g.source :=
    flowGraphChart_base_source v₀ hv x₀
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (g.open_source.mem_nhds hbase)
  obtain ⟨W, hW, hxW, hψ, _⟩ := exists_smooth_implicitFlowCurve_neighborhood v₀ hv x₀
  obtain ⟨r, hr, ε, hε, α, hc, hα⟩ := exists_localFlow_in_open
    (hv.contDiffAt.of_le (by simp) : ContDiffAt ℝ 1 v x₀)
    (hU.inter isOpen_ball) (show x₀ ∈ U ∩ ball x₀ (δ / 2) from
      ⟨hxU, mem_ball_self (half_pos hδ)⟩)
  have hD : (ball x₀ r ×ˢ Ioo (-ε) ε) ∩ ball (x₀, (0 : ℝ)) δ ∩ W ∈ 𝓝 (x₀, 0) :=
    inter_mem (inter_mem
      (prod_mem_nhds (ball_mem_nhds x₀ hr) (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε))
      (ball_mem_nhds (x₀, (0 : ℝ)) hδ)) (hW.mem_nhds hxW)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hD
  have hsmall : ball x₀ ρ ×ˢ Ioo (-ρ) ρ ⊆
      (ball x₀ r ×ˢ Ioo (-ε) ε) ∩ ball (x₀, (0 : ℝ)) δ ∩ W := by
    intro p hp
    apply hρsub
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hp.1, by
      simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hp.2⟩
  have hident (p : E × ℝ) (hp : p ∈ ball x₀ ρ ×ˢ Ioo (-ρ) ρ) :
      implicitFlowCurve v₀ hv x₀ p (1 : I) = α p := by
    have hx := (hsmall hp).1.1.1
    have ht := (hsmall hp).1.1.2
    let a := rescaledFlowCurve α hc hx ht
    have ha : ‖a - ContinuousMap.const I x₀‖ ≤ δ / 2 := by
      apply (ContinuousMap.norm_le _ (half_pos hδ).le).mpr
      intro s
      have hs := ((hα p.1 hx).2 (p.2 * (s : ℝ)) (time_mul_unitInterval ht s)).1.2
      change ‖α (p.1, p.2 * (s : ℝ)) - x₀‖ ≤ δ / 2
      exact (show ‖α (p.1, p.2 * (s : ℝ)) - x₀‖ < δ / 2 from by
        simpa only [mem_ball, dist_eq_norm] using hs).le
    have hgraph : (p, a) ∈ g.source := by
      apply hδsub
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(hsmall hp).1.2, by
        rw [dist_eq_norm]
        exact ha.trans_lt (half_lt_self hδ)⟩
    have hsol : flowEquation v₀ (p, a) = 0 :=
      flowEquation_rescaledFlowCurve v₀ α hc hx ht (hα p.1 hx).1
        (fun u hu => ((hα p.1 hx).2 u hu).2)
    have heq : implicitFlowCurve v₀ hv x₀ p = a :=
      implicitFlowCurve_of_source v₀ hv x₀ hgraph hsol
    exact (congrArg (fun b : C(I, E) => b 1) heq).trans
      (rescaledFlowCurve_one α hc hx ht)
  refine ⟨ρ, hρ, ρ, hρ, α, ?_, ?_⟩
  · have hsmooth : ContDiffOn ℝ ∞
        (fun p => implicitFlowCurve v₀ hv x₀ p (1 : I)) (ball x₀ ρ ×ˢ Ioo (-ρ) ρ) :=
      (ContinuousMap.evalCLM ℝ (1 : I) : C(I, E) →L[ℝ] E).contDiff.comp_contDiffOn
        (hψ.mono (fun _ hp => (hsmall hp).2))
    exact hsmooth.congr (fun p hp => (hident p hp).symm)
  · intro x hx
    have hx' : x ∈ ball x₀ r :=
      (hsmall (show (x, (0 : ℝ)) ∈ ball x₀ ρ ×ˢ Ioo (-ρ) ρ from
        ⟨hx, neg_lt_zero.mpr hρ, hρ⟩)).1.1.1
    refine ⟨(hα x hx').1, ?_⟩
    intro t ht
    have ht' : t ∈ Ioo (-ε) ε := (hsmall (a := (x, t)) ⟨hx, ht⟩).1.1.2
    exact ⟨((hα x hx').2 t ht').1.1, ((hα x hx').2 t ht').2⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
