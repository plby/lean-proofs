import Wikipedia.HopfProblem.DegreeCollapseFlowBandCrossing
import Wikipedia.HopfProblem.DegreeCollapseAdaptedHeightField
import Wikipedia.SmoothSixDPoincare.CompactFlow

/-!
# Constructing the complete crossing flow of the modified native field

The field's finite residence and negative boundary derivatives construct
one complete flow and one time giving both directed crossings. The lower
entry time is continuous on the entire original upper sublevel.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Construct the complete native flow, uniform crossings, and continuous actual entry time. -/
theorem exists_native_flow_band_crossing {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {c d : ℝ}
    (hlower : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hupper : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, f (γ t) ∉ Icc c d) :
    ∃ F : Flow ℝ M, (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
      (∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧
        ∀ x, c ≤ f x → d < f (F (-T) x)) ∧
      ContinuousOn (FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let F := FlowConstruction.compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V :=
    FlowConstruction.isMIntegralCurve_compactFlow hV₁ x
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hres' : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Icc (0 : ℝ) T, f (F t x) ∉ Icc c d := by
    obtain ⟨T, hT, hbound⟩ := hres
    exact ⟨T, hT, fun x => hbound (fun t => F t x) (hcurve x)⟩
  exact ⟨F, hcurve, exists_uniform_directed_band_crossing F hf.continuous hD hder
    hlower hupper hres', continuousOn_band_entryTime F hf.continuous hD hder
    hlower hupper hres'⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
