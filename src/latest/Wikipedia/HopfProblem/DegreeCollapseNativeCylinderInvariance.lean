import Wikipedia.HopfProblem.DegreeCollapseNativeFlowSegment

/-!
# Exact native flow and invariance on an entire coordinate cylinder

If the coordinate trajectories stay in the actual chart for all real
times, native uniqueness identifies the complete lifted flow. The chart
target and its complement are both invariant, so an exterior trajectory
cannot acquire an unaccounted entry into the modified cylinder.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {B M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}

/-- Complete coordinate trajectories in the actual source give the exact complete native flow. -/
theorem native_chart_flow_all_time
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, B) E M ∞)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (F : Flow ℝ E) (W : E → E)
    (hF : ∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t)
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm W x)
    {p : E} (hstay : ∀ t, F t p ∈ Φ.source) :
    ∀ t, G t (Φ p) = Φ (F t p) := by
  let γ : ℝ → M := fun t => Φ (F t p)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve
      Φ.symm W (hF p t) (hstay t)
    have hy := Φ.map_source' (hstay t)
    have hd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (FlowConstruction.partialChartField Φ.symm W (γ t))) := hd
    rw [← hmodel (γ t) hy] at hd'
    exact hd'
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hG (Φ p)) hγ
    (t₀ := 0) (by simp only [γ, G.map_zero_apply, F.map_zero_apply])
  exact fun t => congrFun heq t

/-- Full coordinate-source invariance gives full native chart-target invariance. -/
theorem native_chart_target_invariant
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, B) E M ∞)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (F : Flow ℝ E) (W : E → E)
    (hF : ∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t)
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm W x)
    (hstay : ∀ p ∈ Φ.source, ∀ t, F t p ∈ Φ.source) :
    ∀ x ∈ Φ.target, ∀ t, G t x ∈ Φ.target := by
  intro x hx t
  have hp := Φ.map_target' hx
  have heq := native_chart_flow_all_time Φ hV G hG F W hF hmodel (hstay _ hp) t
  rw [Φ.right_inv' hx] at heq
  rw [heq]
  exact Φ.map_source' (hstay _ hp t)

/-- An invariant set for all real times also has invariant complement, by inverse flow. -/
theorem flow_complement_invariant {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S : Set X} (hS : ∀ x ∈ S, ∀ t, F t x ∈ S) :
    ∀ x ∉ S, ∀ t, F t x ∉ S := by
  intro x hx t ht
  have hh := hS (F t x) ht (-t)
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  exact hx hh

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
