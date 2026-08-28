import Wikipedia.HopfProblem.HolomorphicAutomorphismCompactAtlas
import Wikipedia.HopfProblem.HolomorphicAutomorphismCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Holomorphicity of genuine automorphism expressions

When an automorphism sends the actual closed outer chart patch into the
same chart source, its literal native coordinate expression is
holomorphic throughout the open outer coordinate ball.
-/

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The original chart, automorphism, and inverse chart compose
holomorphically wherever the actual outer chart condition holds. -/
theorem expression_holomorphic (A : CompactAtlas E M) (i : A.Index)
    (f : HolomorphicAutomorphism 𝓘(ℂ, E) M)
    (hf : f ∈ Coordinates.goodMaps (A.chart i)
      (Metric.closedBall (A.centerCoord i) (2 * A.radius (A.center i)))) :
    ContDiffOn ℂ ω (Coordinates.expression (A.chart i) f)
      (A.outerCoordinates i : Set E) := by
  have hc : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.chart i) (A.chart i).source :=
    contMDiffOn_chart
  have hi : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.chart i).symm
      (A.outerCoordinates i : Set E) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (x := A.center i)).mono
      (A.outerCoordinates_subset_target i)
  exact (hc.comp (f.holomorphic.comp_contMDiffOn hi)
    (fun z hz => hf ⟨z, Metric.ball_subset_closedBall hz, rfl⟩)).contDiffOn

/-- Each point of the outer coordinate ball has an analytic germ of the
same actual coordinate expression. -/
theorem expression_analyticAt (A : CompactAtlas E M) (i : A.Index)
    (f : HolomorphicAutomorphism 𝓘(ℂ, E) M)
    (hf : f ∈ Coordinates.goodMaps (A.chart i)
      (Metric.closedBall (A.centerCoord i) (2 * A.radius (A.center i))))
    {z : E} (hz : z ∈ A.outerCoordinates i) :
    AnalyticAt ℂ (Coordinates.expression (A.chart i) f) z :=
  ((expression_holomorphic A i f hf).contDiffAt
    ((A.outerCoordinates i).isOpen.mem_nhds hz)).analyticAt

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
