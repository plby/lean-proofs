import Wikipedia.SmoothSixDPoincare.VariableChartPerturbation
import Wikipedia.SmoothSixDPoincare.ControlledRelativeHomotopy

/-!
# Charts contained in a target set preserve it throughout their perturbations

No compactness of the controlled source region is needed. A valid chart
perturbation either stays in the chart source or leaves the point unchanged.
This applies to the entire constant-parameter or variable-parameter homotopy.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E G F H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ)

theorem perturb_mem_of_source_subset {a : F} (ha : Valid c f β a)
    {O : Set N} (hsource : c.source ⊆ O) {x : X} (hx : f x ∈ O) :
    perturb c f β a x ∈ O := by
  by_cases hxc : f x ∈ c.source
  · exact hsource (perturb_mem_source c f β ha hxc)
  · simpa only [perturb, if_neg hxc] using hx

variable {f β}

theorem homotopicRelWithin_of_source_subset
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {ε : ℝ} (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a)
    {a : F} (ha : ‖a‖ < ε) {D : Set X} {O : Set N}
    (hsource : c.source ⊆ O) (hmaps : MapsTo f D O) :
    HomotopicRelWithin (⟨f, hf.continuous⟩ : C(X, N))
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0} D O := by
  refine ⟨homotopyRel c hf hβ hsupport hvalid ha, ?_⟩
  intro t x hx
  exact perturb_mem_of_source_subset c f β
    (hvalid _ (norm_interval_smul_lt ha t)) hsource (hmaps hx)

theorem variableHomotopicRelWithin_of_source_subset
    (hf : Continuous f) (hβ : Continuous β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : X → F} (ha : Continuous a) {ε : ℝ}
    (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C D : Set X} {O : Set N}
    (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0)
    (hsource : c.source ⊆ O) (hmaps : MapsTo f D O) :
    HomotopicRelWithin (⟨f, hf⟩ : C(X, N))
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩ C D O := by
  refine ⟨variableHomotopyRel c hf hβ hsupport ha hvalid hbound hfixed, ?_⟩
  intro t x hx
  exact perturb_mem_of_source_subset c f β
    (hvalid _ (norm_interval_smul_lt (hbound x) t)) hsource (hmaps hx)

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
