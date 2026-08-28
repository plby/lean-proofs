import Wikipedia.HopfProblem.DegreeCollapseNativeFieldChartGerms

/-!
# Keeping an endpoint field chart after a remote compact field change

An actual field-germ equality at the endpoint gives a constructed open
restriction on which the changed field has the same model. An arbitrary
prescribed open coordinate neighborhood is retained as well, so the
resulting closed model ball can control a non-isometric block change.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing

variable {D E M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_controlled_field_germ_chart
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (W : D → D)
    (V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y)
    {c : D} (hc : c ∈ Φ.source) (hfield : ∀ᶠ y in 𝓝 (Φ c), V' y = V y)
    {O : Set D} (hO : IsOpen O) (hcO : c ∈ O) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (r : ℝ),
      0 < r ∧ closedBall c r ⊆ Ψ.source ∧ Ψ.source ⊆ Φ.source ∩ O ∧
      Ψ.target ⊆ Φ.target ∧ (∀ z, Ψ z = Φ z) ∧
      ∀ y ∈ Ψ.target, V' y = FlowConstruction.partialChartField Ψ.symm W y := by
  obtain ⟨U, hUsub, hU, hcenter⟩ := mem_nhds_iff.mp hfield
  let R := PartialChart.restrictTarget Φ hU
  let Ψ := PartialChart.restrictSource R hO
  have hcΨ : c ∈ Ψ.source := by
    change (c ∈ Φ.source ∧ Φ c ∈ U) ∧ c ∈ O
    exact ⟨⟨hc, hcenter⟩, hcO⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Ψ.open_source.mem_nhds hcΨ)
  refine ⟨Ψ, r, hr, hball, fun z hz => ⟨hz.1.1, hz.2⟩,
    fun y hy => hy.1.1, fun _ => rfl, ?_⟩
  intro y hy
  exact (hUsub hy.1.2).trans (hmodel y hy.1.1)

end Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing
