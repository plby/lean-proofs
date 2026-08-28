import Wikipedia.HopfProblem.DegreeCollapseCompactTransportedBasins
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Compact endpoint sections on every level of a regular band

The actual native bridge is constructed from the original complete
descending flow. It transfers compactness of any invariant section in
both directions; in particular both entire critical endpoint sections
can be moved from their small original core levels to the middle level.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem isCompact_invariant_section_iff_of_regular_band {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f)
    {P : M → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {x : {y : M // f y = b} | P (x : M)} ↔
      IsCompact {x : {y : M // f y = a} | P (x : M)} := by
  have ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨le_rfl, hab⟩)
  have hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨hab, le_rfl⟩)
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨D, e, -, he, horbit⟩ :=
    FlowTimeChange.exists_orbit_preserving_native_band_bridge hf hV hdesc F hF hab hband ha hb
  apply isCompact_flow_invariant_section_iff F e.toHomeomorph Subtype.val Subtype.val _ hP
  intro x
  obtain ⟨t, ht⟩ := horbit x
  exact ⟨t, ht.trans (he x).symm⟩

theorem isCompact_forward_section_iff_of_regular_band {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact {x : {y : M // f y = b} | Tendsto (fun t => F t (x : M)) atTop (𝓝 p)} ↔
      IsCompact {x : {y : M // f y = a} | Tendsto (fun t => F t (x : M)) atTop (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband
    (P := fun x => Tendsto (fun t => F t x) atTop (𝓝 p))
    (fun t x => flow_time_atTop_limit_iff F t x p)

theorem isCompact_backward_section_iff_of_regular_band {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact {x : {y : M // f y = b} | Tendsto (fun t => F t (x : M)) atBot (𝓝 p)} ↔
      IsCompact {x : {y : M // f y = a} | Tendsto (fun t => F t (x : M)) atBot (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband
    (P := fun x => Tendsto (fun t => F t x) atBot (𝓝 p))
    (fun t x => flow_time_atBot_limit_iff F t x p)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
