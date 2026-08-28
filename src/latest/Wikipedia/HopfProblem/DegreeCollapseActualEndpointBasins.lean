import Wikipedia.HopfProblem.DegreeCollapseActualConnectionEndpoints
import Wikipedia.HopfProblem.DegreeCollapseEndpointBasinRestriction

/-!
# Actual connection endpoint charts with exact basin coordinates

The endpoint charts, alignment, domain restriction, and both directions
of the relevant basin equivalence are constructed from the original
descending native Morse flow and its actual nonstationary endpoint limit.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M}

open ManifoldMorse

open Classical in
theorem exists_actual_incoming_cubic_basin (c : SignedMorseChart (E := E) f p)
    (hf : Continuous f) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {x : M} (hxp : x ≠ p) (hlim : Tendsto (fun t => F t x) atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (1 / 2, 0) = p ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ z ∈ Φ.source, Tendsto (fun t => F t (Φ z)) atTop (𝓝 p) ↔
        ∀ i, σ i = -1 → z.2 i = 0) ∧
      ∀ᶠ t in atTop, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  let σ := fun i : Fin m => c.weights (ρ (some i))
  obtain ⟨Φ, hc, hcenter, _, hfield, htail, L, hL, hcoord⟩ :=
    exists_actual_incoming_cubic_endpoint c ρ he hV F hF hxp hlim heq
  obtain ⟨Ψ, hsub, hmap, hΨc, hΨcenter, htarget, hΨfield, hbasin⟩ :=
    exists_cubic_endpoint_basin_restriction c hf σ (fun i => c.signs _) L hL
      hV F hF hmono heq Φ hc hcenter hfield hcoord
  refine ⟨Ψ, hΨc, hΨcenter, htarget, hΨfield, ?_, ?_⟩
  · exact fun z hz => (hbasin z hz).1 rfl
  · exact endpoint_axis_tail_of_restriction Φ Ψ hsub hmap hΨc hΨcenter F x hlim htail

open Classical in
theorem exists_actual_outgoing_cubic_basin (c : SignedMorseChart (E := E) f p)
    (hf : Continuous f) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = -1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {x : M} (hxp : x ≠ p) (hlim : Tendsto (fun t => F t x) atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (-(1 / 2 : ℝ), 0) = p ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ z ∈ Φ.source, Tendsto (fun t => F t (Φ z)) atBot (𝓝 p) ↔
        ∀ i, σ i = 1 → z.2 i = 0) ∧
      ∀ᶠ t in atBot, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  let σ := fun i : Fin m => c.weights (ρ (some i))
  obtain ⟨Φ, hc, hcenter, _, hfield, htail, L, hL, hcoord⟩ :=
    exists_actual_outgoing_cubic_endpoint c ρ he hV F hF hxp hlim heq
  have hc' : ((-1 : ℝ) / 2, (0 : Fin m → ℝ)) ∈ Φ.source := by
    convert! hc using 1 <;> norm_num
  have hcenter' : Φ ((-1 : ℝ) / 2, 0) = p := by
    convert! hcenter using 1 <;> norm_num
  obtain ⟨Ψ, hsub, hmap, hΨc, hΨcenter, htarget, hΨfield, hbasin⟩ :=
    exists_cubic_endpoint_basin_restriction c hf σ (fun i => c.signs _) L hL
      hV F hF hmono heq Φ hc' hcenter' hfield hcoord
  have hΨc' : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Ψ.source := by
    convert! hΨc using 1 <;> norm_num
  have hΨcenter' : Ψ (-(1 / 2 : ℝ), 0) = p := by
    convert! hΨcenter using 1 <;> norm_num
  refine ⟨Ψ, hΨc', hΨcenter', htarget, hΨfield, ?_, ?_⟩
  · exact fun z hz => (hbasin z hz).2 rfl
  · exact endpoint_axis_tail_of_restriction Φ Ψ hsub hmap hΨc' hΨcenter' F x hlim htail

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
