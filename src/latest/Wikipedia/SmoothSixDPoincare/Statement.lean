import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv

/-!
# The exact six-dimensional specialization of Smale's Theorem A

The target is a homeomorphism, not a diffeomorphism. The manifold has its
original topology and a smooth atlas modeled on a six-dimensional real vector
space. No disk decomposition or recognition principle is an assumption.

`Assertion` records the target proposition only. Its unconditional proof is
`smale_theorem_a` in `Wikipedia/SmoothSixDPoincare/TheoremA.lean`.

Source: S. Smale, *Generalized Poincaré's conjecture in dimensions greater
than four*, Annals of Mathematics 74 (1961), Theorem A.
-/

open scoped ContDiff Manifold
open ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

/-- The standard six-sphere with its native Euclidean subspace topology. -/
abbrev SixSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

/-- The exact target proposition; this definition does not assert its truth. -/
def Assertion : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M],
    Module.finrank ℝ E = 6 → (M ≃ₕ SixSphere) → Nonempty (M ≃ₜ SixSphere)

end Wikipedia.SmoothSixDPoincare
