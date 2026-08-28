import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped ContDiff Manifold

namespace NoExoticSixSphere

/-- The standard sphere with its stereographic smooth atlas. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Every smooth six-sphere has the standard smooth structure. The supplied
atlas on `M` is independent of the homeomorphism. -/
theorem no_exotic_six_sphere (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : Nonempty (M ≃ₜ Sphere 6)) : Nonempty (M ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  sorry

end NoExoticSixSphere
