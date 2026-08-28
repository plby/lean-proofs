import Wikipedia.SmoothSixDPoincare.SmoothLocalFlowOn
import Wikipedia.SmoothSixDPoincare.SmoothChartVectorField

/-!
# Jointly smooth local flows of native manifold vector fields

The coordinate field is smooth on the actual chart target. Its local flow
is lifted through the same inverse chart. Joint smoothness, the initial
condition, and the native tangent-bundle differential equation are retained.
-/

noncomputable section

open Set Metric Manifold Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_smooth_manifoldLocalFlow
    {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ), ∃ F : M × ℝ → M,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ F (U ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ U, F (x, 0) = x ∧
        IsMIntegralCurveOn (fun t => F (x, t)) v (Ioo (-ε) ε) := by
  let e := chartAt E p
  obtain ⟨r, hr, ε, hε, α, hαsmooth, hα⟩ := exists_smooth_localFlow_on_open
    (contDiffOn_coordinateField hv p) e.open_target (e.map_source (mem_chart_source E p))
  let U : Set M := e.source ∩ e ⁻¹' ball (e p) r
  have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hpU : p ∈ U := ⟨mem_chart_source E p, mem_ball_self hr⟩
  let F : M × ℝ → M := fun q => e.symm (α (e q.1, q.2))
  have hc : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
      (fun q : M × ℝ => (e q.1, q.2)) (U ×ˢ Ioo (-ε) ε) := by
    apply (contMDiffOn_prod_module_iff _).mpr
    exact ⟨(contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := p)).comp contMDiffOn_fst
      (fun _ hq => hq.1.1), contMDiffOn_snd⟩
  have hd : MapsTo (fun q : M × ℝ => (e q.1, q.2))
      (U ×ˢ Ioo (-ε) ε) (ball (e p) r ×ˢ Ioo (-ε) ε) :=
    fun _ hq => ⟨hq.1.2, hq.2⟩
  have hFsmooth : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      F (U ×ˢ Ioo (-ε) ε) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p)).comp
      (hαsmooth.contMDiffOn.comp hc hd)
      (fun q hq => ((hα (e q.1) hq.1.2).2 q.2 hq.2).1)
  refine ⟨U, hU, hpU, ε, hε, F, hFsmooth, ?_⟩
  intro x hx
  refine ⟨?_, ?_⟩
  · change e.symm (α (e x, 0)) = x
    rw [(hα (e x) hx.2).1, e.left_inv hx.1]
  · intro t ht
    have hcurve := (hα (e x) hx.2).2 t ht
    exact (hasMFDerivAt_lift_coordinateCurve hcurve.2 hcurve.1).hasMFDerivWithinAt

end Wikipedia.SmoothSixDPoincare.FlowConstruction
