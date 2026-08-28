import Wikipedia.HopfProblem.DegreeCollapseCubicCurveBox
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowSegment

/-!
# Exact native cubic flow comparison in an endpoint-chart box

The actual cubic trajectory stays in the box between its endpoints.
Native ODE uniqueness on that closed segment therefore identifies the
original flow in either time direction. No complete ambient cubic flow,
trajectory-domain premise, or local-flow comparison is assumed.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The two endpoints inside an axis-centered chart box determine the
exact original native flow segment in either time direction. -/
theorem native_cubic_flow_between_box_points (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c r : ℝ} (hbox : closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source)
    (z : Fin m → ℝ) {s t : ℝ}
    (hs : cubicFlowCylinder σ a (z, s) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    (ht : cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r) :
    F (t - s) (Φ (cubicFlowCylinder σ a (z, s))) = Φ (cubicFlowCylinder σ a (z, t)) := by
  let γ : ℝ → M := fun u => Φ (cubicFlowCylinder σ a (z, u))
  have hforward {u v : ℝ} (huv : u < v)
      (hu : cubicFlowCylinder σ a (z, u) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
      (hv : cubicFlowCylinder σ a (z, v) ∈ closedBall (c, (0 : Fin m → ℝ)) r) :
      F (v - u) (γ u) = γ v := by
    have hstay (w : ℝ) (hw : w ∈ Icc u v) : cubicFlowCylinder σ a (z, w) ∈ Φ.source :=
      hbox (cubicFlowCylinder_stays_axis_ball σ ha z hw hu hv)
    have hcont : ContinuousOn γ (Icc u v) := Φ.contMDiffOn_toFun.continuousOn.comp
      (((contDiff_cubicFlowCylinder σ a).continuous.comp
        (continuous_const.prodMk continuous_id)).continuousOn) hstay
    have hcurve : IsMIntegralCurveOn γ V (Ioo u v) := by
      intro w hw
      have hp := hstay w ⟨hw.1.le, hw.2.le⟩
      have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
        (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicFlowCylinder σ a z w) hp
      have hd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ w
          ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeCubicDescent σ Φ (-(a ^ 2)) (γ w))) := hd
      rw [← hmodel (γ w) (Φ.map_source' hp)] at hd'
      exact hd'.hasMFDerivWithinAt
    exact FlowSuspension.native_flow_segment_endpoints hV F hF huv hcont hcurve
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hforward hst hs ht
  · subst t
    rw [sub_self, F.map_zero_apply]
  · have hh := congrArg (F (t - s)) (hforward hts ht hs)
    rw [← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply] at hh
    exact hh.symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
