import Wikipedia.SmoothSixDPoincare.EuclideanLocalFlow
import Wikipedia.SmoothSixDPoincare.ChartVectorField

/-!
# Continuous local flows on the original manifold

The Euclidean local flow stays in a genuine chart target and is lifted by
the inverse chart. Both joint continuity and the native integral-curve
equations are retained, uniformly for nearby starting points.
-/

noncomputable section

open Set Metric Manifold Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

/-- Construct a jointly continuous local flow near every point of a boundaryless manifold. -/
theorem exists_manifoldLocalFlow {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} (p : M)
    (hv : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) p) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ), ∃ F : M × ℝ → M,
      ContinuousOn F (U ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ U, F (x, 0) = x ∧
        IsMIntegralCurveOn (fun t => F (x, t)) v (Ioo (-ε) ε) := by
  let e := chartAt E p
  obtain ⟨r, hr, ε, hε, α, hαc, hα⟩ := exists_localFlow_in_open
    (contDiffAt_coordinateField hv) e.open_target (e.map_source (mem_chart_source E p))
  let U : Set M := e.source ∩ e ⁻¹' ball (e p) r
  have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hpU : p ∈ U := ⟨mem_chart_source E p, mem_ball_self hr⟩
  let F : M × ℝ → M := fun q => e.symm (α (e q.1, q.2))
  have hc : ContinuousOn (fun q : M × ℝ => (e q.1, q.2)) (U ×ˢ Ioo (-ε) ε) :=
    (e.continuousOn.comp continuous_fst.continuousOn
      (fun _ hq => hq.1.1)).prodMk continuous_snd.continuousOn
  have hd : MapsTo (fun q : M × ℝ => (e q.1, q.2))
      (U ×ˢ Ioo (-ε) ε) (ball (e p) r ×ˢ Ioo (-ε) ε) :=
    fun _ hq => ⟨hq.1.2, hq.2⟩
  have hFc : ContinuousOn F (U ×ˢ Ioo (-ε) ε) :=
    e.symm.continuousOn.comp (hαc.comp hc hd)
      (fun q hq => ((hα (e q.1) hq.1.2).2 q.2 hq.2).1)
  refine ⟨U, hU, hpU, ε, hε, F, hFc, ?_⟩
  intro x hx
  refine ⟨?_, ?_⟩
  · change e.symm (α (e x, 0)) = x
    rw [(hα (e x) hx.2).1, e.left_inv hx.1]
  · intro t ht
    have hcurve := (hα (e x) hx.2).2 t ht
    exact (hasMFDerivAt_lift_coordinateCurve hcurve.2 hcurve.1).hasMFDerivWithinAt

end Wikipedia.SmoothSixDPoincare.FlowConstruction
