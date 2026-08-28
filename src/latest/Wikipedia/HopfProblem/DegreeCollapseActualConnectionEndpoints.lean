import Wikipedia.HopfProblem.DegreeCollapseConnectionTailOnAxis
import Wikipedia.SmoothSixDPoincare.DescendingFlow

/-!
# Cubic endpoint field charts for actual native connecting orbits

Starting from the original complete flow, a nonstationary endpoint limit,
and its actual Morse field germ, construct the endpoint chart and align it
with the entire far orbit tail. The linear alignment and the chart domain
are constructed, not included as extra geometric premises.
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
theorem morse_coordinates_nonzero_on_nonstationary_orbit
    (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hxp : x ≠ p) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {t : ℝ} (ht : F t x ∈ c.splitChart.source) : c.splitChart (F t x) ≠ 0 := by
  have heqp : V p = c.descentField p :=
    mem_of_mem_nhds (x := p) (s := {y : M | V y = c.descentField y}) heq
  have hVp : V p = 0 := heqp.trans c.descentField_center
  have hfixed := FlowConstruction.flow_fixed_of_zero hV F hF hVp
  intro hz
  have hpoint : F t x = p := c.splitChart.toOpenPartialHomeomorph.injOn ht
    c.splitChart_mem_source (hz.trans c.splitChart_center.symm)
  have hh := congrArg (F (-t)) hpoint
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hfixed] at hh
  exact hxp hh

open Classical in
/-- A positive selected Morse coordinate constructs the actual incoming
cubic endpoint chart, whose regular axis contains the entire far orbit tail. -/
theorem exists_actual_incoming_cubic_endpoint (c : SignedMorseChart (E := E) f p)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hxp : x ≠ p) (hlim : Tendsto (fun t => F t x) atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (1 / 2, 0) = p ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ᶠ t in atTop, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
      ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
        (∀ z, L (endpointLinearField σ (1 / 2) 1 z) = MorseHandle.descent (L z)) ∧
        ∀ z ∈ Φ.source,
          c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) 1 z) := by
  let σ := fun i : Fin m => c.weights (ρ (some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_incoming_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).2
  have hbase : c.splitChart (F T x) = (0, v) := Prod.ext (hzero T le_rfl) rfl
  have hv : v ≠ 0 := by
    intro hv
    exact morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq
      (hsource T le_rfl) (hbase.trans (Prod.ext rfl hv))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_incoming_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) 1 q) = MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ := exists_controlled_morse_field_endpoint c σ
    (by norm_num : (1 : ℝ) ^ 2 = 1) L hL' V heq
  refine ⟨Φ, hc, hval, hsub, hfield, ?_, L, hL', ?_⟩
  · exact incoming_tail_on_cubic_axis c Φ L hc hval hcoord F x hlim hr hLray hbase
      (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

open Classical in
/-- A negative selected Morse coordinate constructs the actual outgoing
cubic endpoint chart, whose regular axis contains the entire far orbit tail. -/
theorem exists_actual_outgoing_cubic_endpoint (c : SignedMorseChart (E := E) f p)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = -1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hxp : x ≠ p) (hlim : Tendsto (fun t => F t x) atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (-(1 / 2 : ℝ), 0) = p ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ᶠ t in atBot, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
      ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
        (∀ z, L (endpointLinearField σ (1 / 2) (-1) z) = MorseHandle.descent (L z)) ∧
        ∀ z ∈ Φ.source,
          c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) (-1) z) := by
  let σ := fun i : Fin m => c.weights (ρ (some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_outgoing_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).1
  have hbase : c.splitChart (F T x) = (v, 0) := Prod.ext rfl (hzero T le_rfl)
  have hv : v ≠ 0 := by
    intro hv
    exact morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq
      (hsource T le_rfl) (hbase.trans (Prod.ext hv rfl))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_outgoing_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) (-1) q) = MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ := exists_controlled_morse_field_endpoint c σ
    (by norm_num : (-1 : ℝ) ^ 2 = 1) L hL' V heq
  have hc' : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source := by
    convert! hc using 1 <;> norm_num
  have hval' : Φ (-(1 / 2 : ℝ), 0) = p := by
    convert! hval using 1 <;> norm_num
  refine ⟨Φ, hc', hval', hsub, hfield, ?_, L, hL', ?_⟩
  · exact outgoing_tail_on_cubic_axis c Φ L hc' hval' hcoord F x hlim hr hLray hbase
      (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
