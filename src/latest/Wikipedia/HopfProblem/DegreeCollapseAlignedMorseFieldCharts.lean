import Wikipedia.HopfProblem.DegreeCollapseSelectedMorseAxes
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Native endpoint field charts with prescribed linear axis alignment

A constructed linear Morse-field conjugacy may be used as the endpoint
coordinates before the rational scalar change. Restricting the actual
native chart to a supplied field-agreement germ retains its critical point
and gives the exact original global field throughout the chart target.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

open ManifoldMorse

open Classical in
/-- The actual native cubic endpoint chart keeps an arbitrary proved linear
axis alignment, with the full forward coordinate map specified. -/
theorem exists_cubic_field_endpoint_with_alignment (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (σ : Fin m → ℝ) {e : ℝ} (he : e ^ 2 = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) = x ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, c.descentField y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  let P := L.toDiffeomorph.toPartialDiffeomorph
  let Q := P.trans c.splitChart.symm
  have h0 : (0 : Model m) ∈ Q.source := by
    change (0 : Model m) ∈ univ ∧ L 0 ∈ c.splitChart.target
    rw [map_zero, ← c.splitChart_center]
    exact ⟨mem_univ _, c.splitChart.map_source' c.splitChart_mem_source⟩
  have hQzero : Q 0 = x := by
    change c.splitChart.symm (L 0) = x
    rw [map_zero, ← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hmodel : ∀ y ∈ Q.target, c.descentField y =
      FlowConstruction.partialChartField Q.symm (endpointLinearField σ (1 / 2) e) y := by
    intro y hy
    have hpush (p : Model m) (_ : p ∈ P.source) :
        fderiv ℝ P p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (P p) := by
      change fderiv ℝ L p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)
      rw [L.fderiv]
      exact hL p
    exact (partialChartField_of_model_conjugacy P c.splitChart.symm
      (endpointLinearField σ (1 / 2) e) MorseHandle.descent hpush hy).symm
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_native_cubic_field_endpoint σ (by norm_num : 0 < (1 / 2 : ℝ)) he Q h0
      c.descentField hmodel
  refine ⟨Φ, ?_, ?_, fun y hy => (hsub hy).1, hf, hmap⟩
  · simpa only [mul_one_div] using hp
  · simpa only [mul_one_div, hQzero] using hc

open Classical in
/-- The constructed aligned endpoint chart represents the original field,
using only its already supplied Morse field germ at the actual critical point. -/
theorem exists_original_field_endpoint_with_alignment (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (σ : Fin m → ℝ) {e : ℝ} (he : e ^ 2 = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) = x ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_cubic_field_endpoint_with_alignment c σ he L hL
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp heq
  let Ψ := PartialChart.restrictTarget Φ hU
  have hpΨ : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hp, hc.symm ▸ hxU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, hmap⟩
  intro y hy
  exact (hUsub hy.2).trans (hf y hy.1)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
