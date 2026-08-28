import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryWindows
import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairBands
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Surviving critical germs, signed charts, and excellent-function data

Exact pair removal leaves each remaining critical point outside the pair
band, so its complete function germ and value survive. Distinct critical
values and signed Morse charts are retained, and a new compatible finite
surgery system with a complete flow can be constructed for the new function.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}

theorem surviving_critical_germs_of_pair_band {p q : M} {l u : ℝ}
    (hpair : ∀ z ∈ criticalPoints E f, f z ∈ Icc l u → z = p ∨ z = q)
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hexterior : ∀ z, f z ∉ Ioo l u → g =ᶠ[𝓝 z] f) :
    ∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f := by
  intro z hz
  obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
  apply hexterior z
  intro hband
  exact (hpair z hzf ⟨hband.1.le, hband.2.le⟩).elim hzp hzq

theorem distinct_critical_values_of_surviving_germs
    (hinj : InjOn f (criticalPoints E f)) (hsub : criticalPoints E g ⊆ criticalPoints E f)
    (hgerms : ∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) :
    InjOn g (criticalPoints E g) := by
  intro x hx y hy hxy
  apply hinj (hsub hx) (hsub hy)
  rw [← (hgerms x hx).self_of_nhds, ← (hgerms y hy).self_of_nhds]
  exact hxy

theorem exists_signed_morse_chart_of_germ {p : M}
    (c : SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : SignedMorseChart (E := E) g p,
      d.weights = c.weights ∧ d.chart.source ⊆ c.chart.source ∧
      (∀ x, d.chart x = c.chart x) ∧ ∀ z, d.chart.symm z = c.chart.symm z := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let P := PartialChart.restrictSource c.chart hU
  let d : SignedMorseChart (E := E) g p := {
    weights := c.weights
    signs := c.signs
    chart := P
    mem_source := ⟨c.mem_source, hpU⟩
    center := c.center
    equation := by
      intro x hx
      have hxs : x ∈ c.chart.source ∩ U := hx
      have hxeq : g x = f x := hUsub hxs.2
      change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
      rw [hxeq, hgerm.self_of_nhds]
      exact c.equation x hxs.1
    inverse_equation := by
      intro z hz
      have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
      have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
      change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
      rw [hzeq, hgerm.self_of_nhds]
      exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl, inter_subset_left, fun _ => rfl, fun _ => rfl⟩

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem adapted_surgeries_after_pair_removal (S : SurgeryWindows E f)
    (p q : criticalPoints E f)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : IsMorse E g)
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔
      z ∈ criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val)
    (hexterior : ∀ z, f z ∉ Ioo (S.lower p) (S.upper q) → g =ᶠ[𝓝 z] f) :
    (∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) ∧
      InjOn g (criticalPoints E g) ∧ Nonempty (AdaptedSurgeryWindows E g) := by
  have hkeep := surviving_critical_germs_of_pair_band
    (surgery_pair_band_isolation S p q hconsecutive) hcrit hexterior
  have hinj := distinct_critical_values_of_surviving_germs S.distinct
    (fun z hz => ((hcrit z).mp hz).1) hkeep
  exact ⟨hkeep, hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
