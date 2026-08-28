import Wikipedia.HopfProblem.DegreeCollapseSignedLevelTime
import Wikipedia.HopfProblem.DegreeCollapseAdaptedHeightField

/-!
# Original regular-level points cannot share distinct positions on one orbit

Strict native descent at the actual level gives uniqueness of its real
crossing time. Thus two points on that level with a common complete orbit
are the same point.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem native_same_level_orbit_points
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x y : M} {s t : ℝ} (hx : f x = c) (hy : f y = c) (hxy : F s x = F t y) : x = y := by
  have hmove : F (s - t) x = y := by
    calc
      F (s - t) x = F (-t) (F s x) := by
        rw [← F.map_add]
        congr 1
        ring
      _ = F (-t) (F t y) := congrArg (F (-t)) hxy
      _ = y := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have htime := FlowCancellation.flow_level_time_unique F hf.continuous
    (contMDiff_directionalDerivative hf hV).continuous
    (fun z u => FlowConstruction.hasDerivAt_comp_integralCurve hf (hF z) u)
    hboundary x (hmove ▸ hy) (show f (F 0 x) = c by rw [F.map_zero_apply]; exact hx)
  simpa only [htime, F.map_zero_apply] using hmove

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
