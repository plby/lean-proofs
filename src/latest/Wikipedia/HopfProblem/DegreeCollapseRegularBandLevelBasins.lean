import Wikipedia.HopfProblem.DegreeCollapseOrbitPreservingBandBridge
import Wikipedia.HopfProblem.DegreeCollapseSignedLevelTime

/-!
# Equal entire level basins across an actual regular band

The constructed ambient bridge carries the whole lower level to the
whole upper level and stays on the original complete orbits. Hence a
trajectory meets one boundary level exactly when it meets the other.
This allows the small original core sections to use the middle-level
cylinder without changing the no-connection field.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

theorem levelBasin_eq_of_orbit_level_bridge {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a b : ℝ) (D : X → X)
    (hlevel : D '' {x | f x = a} = {x | f x = b})
    (horbit : ∀ x, ∃ t, F t x = D x) : levelBasin F f a = levelBasin F f b := by
  ext x
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := horbit (F s x)
    have hDy : f (D (F s x)) = b := by
      have hh : D (F s x) ∈ D '' {y | f y = a} := mem_image_of_mem D hs
      rw [hlevel] at hh
      exact hh
    exact ⟨t + s, by rw [F.map_add, ht]; exact hDy⟩
  · rintro ⟨s, hs⟩
    have hy : F s x ∈ D '' {y | f y = a} := by rw [hlevel]; exact hs
    obtain ⟨y, hy, heq⟩ := hy
    change f y = a at hy
    obtain ⟨t, ht⟩ := horbit y
    have hyB : y ∈ levelBasin F f a := ⟨0, by simpa only [F.map_zero_apply] using hy⟩
    have hh := (levelBasin_flow_iff F f a t y).mpr hyB
    rw [ht, heq] at hh
    exact (levelBasin_flow_iff F f a s x).mp hh

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem levelBasin_eq_of_regular_band {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    levelBasin F f a = levelBasin F f b := by
  obtain ⟨D, hlevel, -, horbit⟩ :=
    FlowTimeChange.exists_orbit_preserving_ambient_band_bridge hf hV hdesc F hF hab hband
  exact levelBasin_eq_of_orbit_level_bridge F f a b D hlevel horbit

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
