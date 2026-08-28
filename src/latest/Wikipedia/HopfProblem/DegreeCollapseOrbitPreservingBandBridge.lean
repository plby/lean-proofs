import Wikipedia.HopfProblem.DegreeCollapseNormalizedBandTransport
import Wikipedia.HopfProblem.DegreeCollapseOrbitPreservingNormalization
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowTimeDiffeomorph
import Wikipedia.SmoothSixDPoincare.RegularBandDiffeomorph

/-!
# A native regular-band bridge along the prescribed complete flow

Positive normalization gives a globally smooth time map of the original
manifold. It carries both whole sublevels and their native boundary levels
onto one another, and every image lies on the original prescribed orbit.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem exists_orbit_preserving_ambient_band_bridge {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧
      D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} ∧
      ∀ x, ∃ t, F t x = D x := by
  obtain ⟨U, W, G, hU, hIU, hW, hG, -, -, hspeed, -, -, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hf hV hdesc F hF hband
  have hshift := native_local_height_translation hf G hG hU hIU hspeed
  let D := SmoothODE.nativeFlowTimeDiffeomorph_of_field hW G hG (a - b)
  refine ⟨D, normalized_flow_level_image G hab hshift,
    normalized_flow_sublevel_image G hf.continuous hab hshift, ?_⟩
  intro x
  have hm : D x ∈ range (fun t => G t x) := ⟨a - b, rfl⟩
  rw [(hgeometry x).1] at hm
  exact hm

theorem exists_orbit_preserving_native_band_bridge {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f)
    (ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf ha
    letI := RegularLevel.chartedSpace hf hb
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {x : M // f x = a} {x : M // f x = b} ∞,
        D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} ∧
        (∀ x, (e x : M) = D x) ∧
        ∀ x, ∃ t, F t x = D x := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨D, hlevel, hsublevel, horbit⟩ :=
    exists_orbit_preserving_ambient_band_bridge hf hV hdesc F hF hab hband
  obtain ⟨e, he⟩ := RegularLevel.exists_levelDiffeomorph_of_ambient hf ha hb D hlevel
  exact ⟨D, e, hsublevel, he, horbit⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
