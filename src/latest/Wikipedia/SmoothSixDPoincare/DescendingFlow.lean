import Wikipedia.SmoothSixDPoincare.AdaptedMorseField
import Wikipedia.SmoothSixDPoincare.RegularBandFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Complete descending flows for the original Morse function

The constructed flow fixes the critical points. Every regular trajectory
stays regular and strictly decreases the original function, while all
trajectories have nonincreasing height.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Native integral-curve uniqueness makes every zero of the field a fixed point of its flow. -/
theorem flow_fixed_of_zero
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hx : V x = 0) (t : ℝ) : F t x = x := by
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve x)
    (isMIntegralCurve_const hx) (t₀ := 0) (F.map_zero_apply x)
  exact congrFun heq t

/-- A flow with stationary critical points preserves the regular locus. -/
theorem flow_preserves_regular {f : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    {x : M} (hx : x ∉ ManifoldMorse.criticalPoints E f) (t : ℝ) :
    F t x ∉ ManifoldMorse.criticalPoints E f := by
  intro hy
  have hfix := flow_fixed_of_zero hV F hcurve (hzero (F t x) hy) (-t)
  have hinv : F (-t) (F t x) = x := by
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have hxy : x = F t x := hinv.symm.trans hfix
  exact hx (hxy.symm ▸ hy)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- Every trajectory of a descending field has nonincreasing height. -/
theorem antitone_flow_height {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (x : M) : Antitone (fun t => f (F t x)) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
  intro t
  change mvfderiv 𝓘(ℝ, E) f (F t x) (V (F t x)) ≤ 0
  by_cases ht : F t x ∈ ManifoldMorse.criticalPoints E f
  · rw [hzero (F t x) ht, map_zero]
  · exact (hdesc (F t x) ht).le

/-- Every regular trajectory strictly decreases the original function at all times. -/
theorem strictAnti_flow_height {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hx : x ∉ ManifoldMorse.criticalPoints E f) : StrictAnti (fun t => f (F t x)) :=
  strictAnti_of_hasDerivAt_neg (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
    (fun t => hdesc (F t x) (flow_preserves_regular hV F hcurve hzero hx t))

variable [FiniteDimensional ℝ E] [CompactSpace M]

/-- Construct a complete descending flow, preserving the exact Morse-coordinate field near every
critical point, directly from the original smooth Morse function. -/
theorem exists_adaptedDescentFlow {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
      (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      (∀ p ∈ ManifoldMorse.criticalPoints E f,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f p,
          ∀ᶠ x in 𝓝 p, V x = c.descentField x) ∧
      (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ t, F t x = x) ∧
      (∀ x, x ∉ ManifoldMorse.criticalPoints E f → StrictAnti (fun t => f (F t x))) ∧
      ∀ x, Antitone (fun t => f (F t x)) := by
  obtain ⟨V, hV, hzero, hdesc, hcharts⟩ := ManifoldMorse.exists_adaptedDescentField hf hm
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hV.of_le (by simp)
  let F := compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V :=
    isMIntegralCurve_compactFlow hV₁ x
  exact ⟨V, F, hV, hcurve, hzero, hdesc, hcharts,
    fun x hx t => flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t,
    fun x hx => strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx,
    fun x => antitone_flow_height hf F hcurve hzero hdesc x⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
