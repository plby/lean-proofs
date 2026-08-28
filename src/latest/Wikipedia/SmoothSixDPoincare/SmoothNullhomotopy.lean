import Wikipedia.SmoothSixDPoincare.SmoothHomotopyCollars
import Wikipedia.SmoothSixDPoincare.LowDimensionalNullhomotopy

/-!
# Smooth low-dimensional nullhomotopies in the original homotopy six-sphere

The actual homotopy equivalence first supplies a continuous nullhomotopy.
Endpoint flattening and relative smoothing turn it into a genuinely smooth
cylinder map, equal to the original map on a whole bottom collar and constant
on a whole top collar. No sphere homeomorphism or disk embedding is assumed.
-/

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E G H X M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [CompactSpace X]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold 𝓘(ℝ, G) ∞ M]

/-- Smooth maps of dimension below six contract by a smooth homotopy with fixed endpoint collars. -/
theorem exists_smooth_nullhomotopy_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E < 6) (f : C(X, M)) (hf : ContMDiff I 𝓘(ℝ, G) ∞ f) :
    ∃ c : M, ∃ H : f.Homotopy (ContinuousMap.const X c),
      ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, G) ∞ H ∧
      (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x) ∧
      (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) := by
  obtain ⟨c, ⟨H⟩⟩ := manifoldMap_nullhomotopic_of_homotopySixSphere (I := I) e hdim f
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hf contMDiff_const H
  exact ⟨c, H', hH', hlo, hhi⟩

end Wikipedia.SmoothSixDPoincare
