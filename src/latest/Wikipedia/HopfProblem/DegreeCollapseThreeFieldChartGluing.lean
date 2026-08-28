import Wikipedia.HopfProblem.DegreeCollapseNativeFieldChartGerms
import Wikipedia.HopfProblem.DegreeCollapseThreeChartMap

/-!
# One native field chart containing the full compact axis

Three actual charts of the same model field, with matching full germs
at the two switching points, glue along their common embedded axis.
Compact injectivity gives one genuine chart carrying the original native
field throughout its target and retaining both full endpoint germs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing

variable {Z E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

theorem exists_glued_three_native_field_charts
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (W : (ℝ × Z) → ℝ × Z) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hsource₀ : ∀ s ∈ Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Ioo a b, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ)
    (γ : ℝ → M) (hinj : InjOn γ (Icc l r))
    (haxis₀ : ∀ s ∈ Icc l a, Φ₀ (s, 0) = γ s)
    (haxisₘ : ∀ s ∈ Ioo a b, Φₘ (s, 0) = γ s)
    (haxis₁ : ∀ s ∈ Icc b r, Φ₁ (s, 0) = γ s) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
      (∀ s ∈ Icc l r, Φ (s, 0) = γ s) ∧
      (∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) ∧
      ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
      ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let f := threeChartMap Φ₀ Φₘ Φ₁ a b
  have haxis (s : ℝ) (hs : s ∈ Icc l r) : f (s, 0) = γ s := by
    by_cases hsa : s ≤ a
    · exact (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa).eq_of_nhds.trans
        (haxis₀ s ⟨hs.1, hsa⟩)
    · by_cases hbs : b ≤ s
      · exact (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs).eq_of_nhds.trans
          (haxis₁ s ⟨hbs, hs.2⟩)
      · exact (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa)
          (lt_of_not_ge hbs)).eq_of_nhds.trans
          (haxisₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩)
  have hfinj : InjOn f (Icc l r ×ˢ {(0 : Z)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [haxis s hs, haxis t ht] at heq
    exact congrArg (fun s : ℝ => (s, (0 : Z))) (hinj hs ht heq)
  have hlocal : ∀ p ∈ Icc l r ×ˢ {(0 : Z)},
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
        p ∈ Ψ.source ∧ f =ᶠ[𝓝 p] Ψ ∧
        ∀ y ∈ Ψ.target, V y = FlowConstruction.partialChartField Ψ.symm W y := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsa : s ≤ a
    · exact ⟨Φ₀, hsource₀ s ⟨hs.1, hsa⟩,
        threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa, hfield₀⟩
    · by_cases hbs : b ≤ s
      · exact ⟨Φ₁, hsource₁ s ⟨hbs, hs.2⟩,
          threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs, hfield₁⟩
      · exact ⟨Φₘ, hsourceₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩,
          threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa) (lt_of_not_ge hbs), hfieldₘ⟩
  obtain ⟨Φ, hsource, hmap, hfield⟩ := exists_native_field_chart_near_compact f W V
    (isCompact_Icc.prod isCompact_singleton) hfinj hlocal
  refine ⟨Φ, hsource, fun s hs => (hmap (s, 0)).trans (haxis s hs), hfield, ?_, ?_⟩
  · filter_upwards [threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hla] with p hp
    exact (hmap p).trans hp
  · filter_upwards [threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbr] with p hp
    exact (hmap p).trans hp

end Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing
