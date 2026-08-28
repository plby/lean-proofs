import Wikipedia.HopfProblem.DegreeCollapseIsolatedConnection
import Wikipedia.SmoothSixDPoincare.DescendingFlow

/-!
# Critical endpoint limits and no-return neighborhoods for the original native field

The abstract strict-height hypotheses are proved from the actual manifold
integral-curve equation. The critical set and values are those of the original
smooth function. Uniqueness of the selected connection remains geometric
input; no-return and endpoint convergence are conclusions.
-/

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Actual forward and backward critical endpoints of every native descending trajectory. -/
theorem exists_native_descent_endpoints
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (ManifoldMorse.criticalPoints E f)) (x : M) :
    ∃ p ∈ ManifoldMorse.criticalPoints E f, ∃ q ∈ ManifoldMorse.criticalPoints E f,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 p) ∧
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 q) ∧
      (x ∉ ManifoldMorse.criticalPoints E f → f q < f x ∧ f x < f p) := by
  exact exists_strict_descent_flow_endpoints F hf.continuous hinj
    (FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
    (fun x hx => FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp))
      F hcurve hzero hdesc hx) x

/-- The original native field and unique connection construct a no-return neighborhood. -/
theorem exists_native_connection_no_return
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (ManifoldMorse.criticalPoints E f))
    {p q z : M} (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Icc (f p) (f q))
    (hunique : ∀ x ∉ ManifoldMorse.criticalPoints E f,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 q) →
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U)
    (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set M, IsOpen N ∧ N ⊆ U ∧ p ∈ N ∧ q ∈ N ∧
      (∀ t : ℝ, F t z ∈ N) ∧
      ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N →
        ∀ s ∈ Icc (0 : ℝ) t, F s x ∈ U := by
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hV.of_le (by simp)
  exact exists_isolated_connection_no_return F hf.continuous hinj
    (FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
    (fun x hx => FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx)
    (fun x hx t => FlowConstruction.flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t)
    hp hq hpq hpair hzband hunique hU hpU hqU hzU

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
