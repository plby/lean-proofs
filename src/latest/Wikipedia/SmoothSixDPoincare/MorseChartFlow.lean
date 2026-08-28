import Wikipedia.SmoothSixDPoincare.MorseModelEntry
import Wikipedia.SmoothSixDPoincare.MorseDescentField
import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Topology.Connected.Clopen

/-!
# Agreement of the native flow with the exact Morse model

Native integral-curve uniqueness identifies the global flow locally with
the explicit coordinate flow whenever the fields agree near the starting
point, and on a whole connected time set while the model trajectory stays
in the field-agreement region. Agreement is proved, rather than assumed
for the flows.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The native flow has the explicit Morse-coordinate formula near time zero. -/
theorem eventually_flow_eq_descentModel
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hx : x ∈ c.splitChart.source)
    (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      F t x = c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  let α : ℝ → c.NegativeCoordinates × c.PositiveCoordinates :=
    fun t => MorseHandle.descentFlow t (c.splitChart x)
  let γ : ℝ → M := e.symm ∘ α
  have hα : Continuous α := MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : α 0 = e x := MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), α t ∈ e.target :=
    hα.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hγ₀ : γ 0 = x := by
    change e.symm (α 0) = x
    rw [hα₀, e.left_inv hx]
  have hγc : ContinuousAt γ 0 :=
    (e.continuousAt_symm (hα₀ ▸ e.map_source hx)).comp hα.continuousAt
  have hγt : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by simpa only [ContinuousAt, hγ₀] using hγc
  have hγ : IsMIntegralCurveAt γ V 0 := by
    filter_upwards [htarget, hγt.eventually heq] with t ht heqt
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t)))
    rw [heqt]
    exact FlowConstruction.hasMFDerivAt_lift_partialChartCurve c.splitChart MorseHandle.descent
      (MorseHandle.hasDerivAt_descentFlow (c.splitChart x) t) ht
  have h₀ : F 0 x = γ 0 := (F.map_zero_apply x).trans hγ₀.symm
  exact isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    (hV.contMDiffAt) ((hcurve x).isMIntegralCurveAt 0) hγ h₀

open Classical in
/-- Model agreement persists on a connected time set, provided the entire
model trajectory stays in the chart and in the region where the fields agree. -/
theorem flow_eqOn_descentModel [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hx : x ∈ c.splitChart.source)
    {S : Set ℝ} (hS : IsPreconnected S) (hzero : 0 ∈ S)
    (htarget : ∀ t ∈ S, MorseHandle.descentFlow t (c.splitChart x) ∈ c.splitChart.target)
    (heq : ∀ t ∈ S, ∀ᶠ y in
      𝓝 (c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x))),
        V y = c.descentField y) :
    EqOn (fun t => F t x)
      (fun t => c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x))) S := by
  let α : ℝ → c.NegativeCoordinates × c.PositiveCoordinates :=
    fun t => MorseHandle.descentFlow t (c.splitChart x)
  let γ : ℝ → M := c.splitChart.symm ∘ α
  have hα : Continuous α := MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hγ : ∀ t ∈ S, IsMIntegralCurveAt γ V t := by
    intro t ht
    have hlocal : ∀ᶠ s in 𝓝 t, α s ∈ c.splitChart.target :=
      hα.continuousAt.preimage_mem_nhds (c.splitChart.open_target.mem_nhds (htarget t ht))
    have hc : ContinuousAt c.splitChart.toOpenPartialHomeomorph.symm (α t) :=
      c.splitChart.toOpenPartialHomeomorph.continuousAt_symm (htarget t ht)
    have hγc : ContinuousAt γ t := hc.comp (f := α) hα.continuousAt
    filter_upwards [hlocal, hγc.eventually (heq t ht)] with s hs heqs
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s)))
    rw [heqs]
    exact FlowConstruction.hasMFDerivAt_lift_partialChartCurve c.splitChart MorseHandle.descent
      (MorseHandle.hasDerivAt_descentFlow (c.splitChart x) s) hs
  have hγc : Continuous (fun t : S => γ t.val) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hγ t.val t.property).continuousAt).comp continuousAt_subtype_val
  let U : Set S := {t | F t.val x = γ t.val}
  have hclosed : IsClosed U :=
    isClosed_eq (F.continuous continuous_subtype_val continuous_const) hγc
  have hopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      hV.contMDiffAt ((hcurve x).isMIntegralCurveAt t.val) (hγ t.val t.property) ht
    exact continuousAt_subtype_val.eventually hlocal
  have hγzero : γ 0 = x := by
    change c.splitChart.symm (MorseHandle.descentFlow 0 (c.splitChart x)) = x
    rw [MorseHandle.descentFlow.map_zero_apply]
    exact c.splitChart.left_inv' hx
  have hnonempty : U.Nonempty :=
    ⟨⟨0, hzero⟩, (F.map_zero_apply x).trans hγzero.symm⟩
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have huniv : U = univ := (show IsClopen U from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro t ht
  have hmem : (⟨t, ht⟩ : S) ∈ U := huniv ▸ mem_univ _
  exact hmem

open Classical in
/-- The endpoint formula includes either sign of time and both endpoints of
the closed trajectory interval. -/
theorem flow_eq_descentModel_of_mem_uIcc [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {x : M} (hx : x ∈ c.splitChart.source) {t : ℝ}
    (htarget : ∀ s ∈ uIcc 0 t,
      MorseHandle.descentFlow s (c.splitChart x) ∈ c.splitChart.target)
    (heq : ∀ s ∈ uIcc 0 t, ∀ᶠ y in
      𝓝 (c.splitChart.symm (MorseHandle.descentFlow s (c.splitChart x))),
        V y = c.descentField y) :
    F t x = c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)) :=
  c.flow_eqOn_descentModel hV F hcurve hx isPreconnected_uIcc left_mem_uIcc
    htarget heq right_mem_uIcc

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
