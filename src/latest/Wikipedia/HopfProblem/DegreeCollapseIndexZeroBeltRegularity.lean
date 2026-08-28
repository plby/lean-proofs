import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery
import Wikipedia.SmoothSixDPoincare.NativeTransversalityStability

/-!
# Automatic native transversality of the belt sphere at an index-zero point

For index zero the original belt sphere has the entire regular-level
dimension. Its proved injective native derivative is therefore surjective.
Consequently every sheet is transverse to it at every crossing; no
transversality hypothesis is needed for a zero/one cancellation criterion.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

open Classical in
theorem index_zero_belt_derivative_surjective (d : MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hzero : Module.finrank ℝ d.chart.NegativeCoordinates = 0) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Surjective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E := by
    exact mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  have hi : Injective A := d.belt_derivative_injective hf n v
  have hdim : Module.finrank ℝ (RegularLevel.Model E) = n := by
    have hsplit := d.chart.finrank_negative_add_positive
    have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
    simp only [RegularLevel.Model, finrank_euclideanSpace, Fintype.card_fin]
    omega
  have hrank : Module.finrank ℝ A.range = Module.finrank ℝ (RegularLevel.Model E) := by
    rw [LinearMap.finrank_range_of_inj hi, hdim, finrank_euclideanSpace_fin]
  have hrange : A.range = ⊤ := Submodule.eq_top_of_finrank_eq hrank
  exact LinearMap.range_eq_top.mp hrange

open Classical in
theorem nativeAt_index_zero_belt {D H X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace H] (I : ModelWithCorners ℝ D H)
    [TopologicalSpace X] [ChartedSpace H X]
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hzero : Module.finrank ℝ d.chart.NegativeCoordinates = 0) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ g : X → d.UpperLevel, ∀ x v,
      NativeTransversality.At I (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g d.surgery.beltSphere x v := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro g x v _ w
  obtain ⟨z, hz⟩ := index_zero_belt_derivative_surjective d hf hzero n v w
  let A : D →L[ℝ] RegularLevel.Model E := by
    exact mfderiv I 𝓘(ℝ, RegularLevel.Model E) g x
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E := by
    exact mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  refine ⟨(0, z), ?_⟩
  change A 0 + B z = w
  rw [map_zero, zero_add]
  exact hz

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
