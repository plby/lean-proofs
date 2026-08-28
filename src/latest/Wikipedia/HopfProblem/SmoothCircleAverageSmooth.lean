import Wikipedia.HopfProblem.SmoothCircleAverageBasic
import Wikipedia.HopfProblem.SmoothManifoldParameterIntegral

/-!
# Smoothness of the actual period-one average

The literal interval integral of the original smooth action is smooth in
the original manifold atlas. Invariance and relative-value preservation
are proved separately from the action laws in `SmoothCircleAverageBasic`.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothCircleAverage

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Averaging the given smooth map along the given smooth real action
preserves smoothness, without changing the source atlas. -/
theorem contMDiff_average (act : ℝ → M → M)
    (hact : ContMDiff ((𝓘(ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => act p.1 p.2))
    {g : M → F} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (average act g) := by
  have hswap : ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ))
      ((𝓘(ℝ)).prod 𝓘(ℝ, E)) ∞ (Prod.swap : M × ℝ → ℝ × M) :=
    contMDiff_snd.prodMk contMDiff_fst
  exact SmoothManifoldParameterIntegral.contMDiff_intervalIntegral
    ((hg.comp hact).comp hswap) 0 1

end Wikipedia.HopfProblem.SmoothCircleAverage
