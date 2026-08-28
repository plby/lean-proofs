import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

/-- The standard six-sphere with its native topology and stereographic atlas. -/
abbrev SixSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

/-- Every closed smooth homotopy six-sphere is homeomorphic to the standard sphere. -/
theorem homeomorphic_sixSphere_of_homotopySixSphere
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) : Nonempty (M ≃ₜ SixSphere) := by
  sorry

/-- The original smooth atlas of a closed homotopy six-sphere is standard. -/
theorem diffeomorphic_sixSphere_of_homotopySixSphere
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) :
    Nonempty (M ≃ₘ⟮𝓘(ℝ, E), 𝓡 6⟯ SixSphere) := by
  sorry

end Wikipedia.SmoothSixDPoincare
