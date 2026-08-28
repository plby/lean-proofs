import Wikipedia.SmoothSixDPoincare.MorseChartFlow
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Exact Morse coordinates along an actual native trajectory

Local native uniqueness and connectedness give the model formula on any
connected time set on which the actual trajectory lies in the Morse chart.
No prior assertion that the explicit model trajectory stays in the chart
is needed. Transporting backwards by the model flow is locally constant.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- Local flow identities determine the trajectory on every connected time set. -/
theorem flow_formula_of_local_shifts {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (γ : ℝ → X) {S : Set ℝ} (hS : IsPreconnected S)
    (hlocal : ∀ t ∈ S, ∀ᶠ s in 𝓝 t, γ s = F (s - t) (γ t))
    {t₀ t : ℝ} (h₀ : t₀ ∈ S) (ht : t ∈ S) : γ t = F (t - t₀) (γ t₀) := by
  let β : S → X := fun u => F (-u.1) (γ u.1)
  have hc : IsLocallyConstant β := by
    apply (IsLocallyConstant.iff_eventually_eq β).mpr
    intro u
    filter_upwards [continuousAt_subtype_val.eventually (hlocal u.1 u.2)] with v hv
    change F (-v.1) (γ v.1) = F (-u.1) (γ u.1)
    rw [hv, ← F.map_add]
    congr 1
    ring
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hb : β ⟨t, ht⟩ = β ⟨t₀, h₀⟩ :=
    hc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _)
  have hh := congrArg (F t) hb
  change F t (F (-t) (γ t)) = F t (F (-t₀) (γ t₀)) at hh
  simpa only [← F.map_add, add_neg_cancel, F.map_zero_apply, ← sub_eq_add_neg] using hh

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

open ManifoldMorse

open Classical in
/-- The actual Morse-coordinate trajectory has the local linear flow identity. -/
theorem eventually_morse_coordinate_flow (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (x : M) (t : ℝ) (ht : F t x ∈ c.splitChart.source)
    (heq : ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) :
    ∀ᶠ s in 𝓝 t, c.splitChart (F s x) =
      MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  have hlocal : ∀ᶠ u in 𝓝 (0 : ℝ), F u (F t x) =
      c.splitChart.symm (MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    c.eventually_flow_eq_descentModel hV F hF ht heq
  have htime : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t
  have hmodel : Continuous (fun u : ℝ =>
      MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have htarget : ∀ᶠ u in 𝓝 (0 : ℝ),
      MorseHandle.descentFlow u (c.splitChart (F t x)) ∈ c.splitChart.target := by
    have hnhds : ∀ᶠ y in 𝓝 (c.splitChart (F t x)), y ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (c.splitChart.map_source' ht)
    have hm0 : Tendsto (fun u : ℝ => MorseHandle.descentFlow u (c.splitChart (F t x)))
        (𝓝 0) (𝓝 (c.splitChart (F t x))) := by
      simpa only [Flow.map_zero_apply] using hmodel.tendsto 0
    exact hm0.eventually hnhds
  filter_upwards [htime.eventually hlocal, htime.eventually htarget] with s hs hst
  rw [← F.map_add, sub_add_cancel] at hs
  have hh := congrArg c.splitChart hs
  exact hh.trans (c.splitChart.right_inv' hst)

open Classical in
/-- Connectedness gives the exact model formula using actual-trajectory
domain control, rather than assuming a model trajectory remains in the chart. -/
theorem morse_coordinates_of_actual_trajectory (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (x : M) {S : Set ℝ} (hS : IsPreconnected S)
    (htarget : ∀ t ∈ S, F t x ∈ c.splitChart.source)
    (heq : ∀ t ∈ S, ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y)
    {t₀ t : ℝ} (h₀ : t₀ ∈ S) (ht : t ∈ S) :
    c.splitChart (F t x) = MorseHandle.descentFlow (t - t₀) (c.splitChart (F t₀ x)) :=
  flow_formula_of_local_shifts MorseHandle.descentFlow (fun s => c.splitChart (F s x)) hS
    (fun s hs => eventually_morse_coordinate_flow c hV F hF x s (htarget s hs) (heq s hs)) h₀ ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
