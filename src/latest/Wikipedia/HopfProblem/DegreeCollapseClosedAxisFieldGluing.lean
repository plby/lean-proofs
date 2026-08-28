import Wikipedia.HopfProblem.DegreeCollapseThreeFieldChartGluing
import Wikipedia.HopfProblem.DegreeCollapseClosedAxisInjectivity

/-!
# A full native field chart from matching endpoint and regular charts

The middle chart supplies the actual injective regular axis. Its two
distinct excluded endpoints give closed-axis injectivity. Matching full
germs at two interior cuts then construct one genuine native chart
containing the closed axis and preserving the exact model field.
No ambient tubular chart or separately supplied embedded axis is assumed.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing

variable {Z E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

theorem exists_closed_axis_native_field_chart
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (W : (ℝ × Z) → ℝ × Z) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l < a) (hab : a < b) (hbr : b < r)
    (hsource₀ : ∀ s ∈ Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Ioo l r, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ)
    (haxis₀ : ∀ s ∈ Ioc l a, Φ₀ (s, 0) = Φₘ (s, 0))
    (haxis₁ : ∀ s ∈ Ico b r, Φ₁ (s, 0) = Φₘ (s, 0))
    (hleft : Φ₀ (l, 0) ∉ Φₘ.target) (hright : Φ₁ (r, 0) ∉ Φₘ.target)
    (hne : Φ₀ (l, 0) ≠ Φ₁ (r, 0)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
      (∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) ∧
      Φ (l, 0) = Φ₀ (l, 0) ∧ Φ (r, 0) = Φ₁ (r, 0) ∧
      (∀ s ∈ Ioo l r, Φ (s, 0) = Φₘ (s, 0)) ∧
      ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
      ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let γ : ℝ → M := fun s => threeChartMap Φ₀ Φₘ Φ₁ a b (s, 0)
  have hγ₀ (s : ℝ) (hs : s ≤ a) : γ s = Φ₀ (s, 0) :=
    (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hs).eq_of_nhds
  have hγ₁ (s : ℝ) (hs : b ≤ s) : γ s = Φ₁ (s, 0) :=
    (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hs).eq_of_nhds
  have hγₘ (s : ℝ) (hs : s ∈ Ioo a b) : γ s = Φₘ (s, 0) :=
    (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ hs.1 hs.2).eq_of_nhds
  have hregular (s : ℝ) (hs : s ∈ Ioo l r) : γ s = Φₘ (s, 0) := by
    by_cases hsa : s ≤ a
    · exact (hγ₀ s hsa).trans (haxis₀ s ⟨hs.1, hsa⟩)
    by_cases hbs : b ≤ s
    · exact (hγ₁ s hbs).trans (haxis₁ s ⟨hbs, hs.2⟩)
    exact hγₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩
  have hinj : InjOn γ (Icc l r) :=
    injective_closed_axis_of_regular_chart Φₘ γ hsourceₘ hregular
      (by rw [hγ₀ l hla.le]; exact hleft)
      (by rw [hγ₁ r hbr.le]; exact hright)
      (by rw [hγ₀ l hla.le, hγ₁ r hbr.le]; exact hne)
  obtain ⟨Φ, hsource, haxis, hfield, hg₀, hg₁⟩ :=
    exists_glued_three_native_field_charts Φ₀ Φₘ Φ₁ W V hfield₀ hfieldₘ hfield₁
      hla.le hab hbr.le hsource₀
      (fun s hs => hsourceₘ s ⟨hla.trans hs.1, hs.2.trans hbr⟩)
      hsource₁ hgerm₀ hgerm₁ γ hinj
      (fun s hs => (hγ₀ s hs.2).symm)
      (fun s hs => (hγₘ s hs).symm)
      (fun s hs => (hγ₁ s hs.1).symm)
  have hlr : l ≤ r := (hla.trans (hab.trans hbr)).le
  refine ⟨Φ, hsource, hfield,
    (haxis l ⟨le_rfl, hlr⟩).trans (hγ₀ l hla.le),
    (haxis r ⟨hlr, le_rfl⟩).trans (hγ₁ r hbr.le), ?_, hg₀, hg₁⟩
  exact fun s hs => (haxis s ⟨hs.1.le, hs.2.le⟩).trans (hregular s hs)

end Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing
