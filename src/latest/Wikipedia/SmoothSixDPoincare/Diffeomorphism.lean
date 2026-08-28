import Wikipedia.SmoothSixDPoincare.TheoremA
import Wikipedia.NoExoticSixSphere.SmoothModelRigidity

/-! # Smooth six-dimensional Poincaré recognition -/

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

/-- Every closed smooth homotopy six-sphere is diffeomorphic to the standard
six-sphere for its originally supplied smooth atlas. -/
theorem diffeomorphic_sixSphere_of_homotopySixSphere
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) :
    Nonempty (M ≃ₘ⟮𝓘(ℝ, E), 𝓡 6⟯ SixSphere) := by
  obtain ⟨h⟩ := homeomorphic_sixSphere_of_homotopySixSphere E M hdim hM
  exact NoExoticSixSphere.diffeomorphic_of_homeomorphic E M hdim h

end Wikipedia.SmoothSixDPoincare
