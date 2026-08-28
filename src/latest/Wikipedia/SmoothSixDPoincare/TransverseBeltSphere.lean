import Wikipedia.SmoothSixDPoincare.MorseSignedCancellationStep

/-!
# The native sphere properties retained during Morse-belt cancellation

This predicate packages the actual smoothness, injectivity, immersion, and
transversality conclusions already constructed for the attaching sphere.
Its intersection set is finite by the proved native transversality theorem.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

/-- The actual native geometric properties needed by every signed cancellation step. -/
def IsTransverseBeltSphere (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) : Prop :=
  letI := RegularLevel.chartedSpace hf D.upper_regular
  letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧ Injective g ∧
    (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x)) ∧
    ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
      g D.surgery.beltSphere x y

/-- Finiteness is a consequence of the native sphere properties, not an extra invariant. -/
theorem finite_points_of_isTransverseBeltSphere [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    {g : C(Hemisphere.Sphere 2, D.UpperLevel)}
    (hg : D.IsTransverseBeltSphere hf hdim hindex g) : (D.beltIntersectionPoints 2 g).Finite := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hs, hinj, _, ht⟩ := hg
  exact D.finite_beltIntersectionPoints hf 3 2 hindex g hs hinj ht

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
