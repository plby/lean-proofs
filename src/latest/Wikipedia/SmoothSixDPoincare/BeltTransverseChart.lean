import Wikipedia.SmoothSixDPoincare.BeltLocalCoordinates
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-! # Constructing a belt-sphere chart in the actual next-handle transverse model -/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p q : M} (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)

open Classical in
theorem exists_belt_transverse_chart (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = m + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, d'.chart.PositiveCoordinates) (𝓡 n)
      d'.chart.PositiveCoordinates (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞,
      (0 : d'.chart.PositiveCoordinates) ∈ χ.source ∧ χ 0 = v := by
  have h₁ := d.chart.finrank_negative_add_positive
  have h₂ := d'.chart.finrank_negative_add_positive
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
  have hneg : Module.finrank ℝ d'.chart.NegativeCoordinates = m + 1 := Fact.out
  have hdim' : Module.finrank ℝ d'.chart.PositiveCoordinates = n := by omega
  let L : d'.chart.PositiveCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim'.trans finrank_euclideanSpace_fin.symm)
  let c := NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) v
  refine ⟨L.toDiffeomorph.toPartialDiffeomorph.trans c, ⟨mem_univ _, ?_⟩, ?_⟩
  · change L 0 ∈ c.source
    rw [map_zero]
    exact NativeParametrization.zero_mem_centered_source v
  · change c (L 0) = v
    rw [map_zero]
    exact NativeParametrization.centered_zero v

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
