import Wikipedia.NoExoticSixSphere.SardManifoldSource

/-!
# Almost every vector-valued regular value

This retains the null exceptional set from the proved manifold-source Sard
theorem. Unlike density alone, it permits countably many regularity
requirements to be imposed on the same perturbation parameter.
-/

open scoped Manifold ContDiff
open Set MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

variable {B F : Type} {H M : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SecondCountableTopology M] [MeasurableSpace F] [BorelSpace F]

theorem ae_regularValues (μ : Measure F) [IsAddHaarMeasure μ]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    ∀ᵐ b ∂μ, ∀ x, f x = b → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  rw [ae_iff]
  apply measure_mono_null _ (measure_manifoldCriticalValues_eq_zero μ isOpen_univ
    hf.contMDiffOn)
  intro b hb
  simp only [mem_ofPred_eq, not_forall] at hb
  obtain ⟨x, hx, hcrit⟩ := hb
  exact ⟨x, ⟨mem_univ x, hcrit⟩, hx⟩

end NoExoticSixSphere.Sard
