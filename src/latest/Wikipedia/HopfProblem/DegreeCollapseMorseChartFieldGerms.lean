import Wikipedia.HopfProblem.DegreeCollapseMorseConstantShift
import Wikipedia.HopfProblem.DegreeCollapseSurvivingMorseGerms
import Wikipedia.SmoothSixDPoincare.MorseDescentField

/-!
# Critical constant-shift germs retain the original native model field

Restricting a signed Morse chart changes only its source and target sets;
its actual coordinate function and weights stay unchanged. Its pulled-back
linear model field is therefore exactly unchanged. This allows critical-value
rearrangements to retain the same adapted field and complete flow.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}

theorem exists_signed_morse_chart_of_germ_preserving_field
    (c : SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let d : SignedMorseChart (E := E) g p := {
    weights := c.weights
    signs := c.signs
    chart := PartialChart.restrictSource c.chart hU
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
  exact ⟨d, rfl⟩

theorem exists_signed_morse_chart_of_shift_germ_preserving_field
    (c : SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    ∃ d : SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨d, hd⟩ := exists_signed_morse_chart_of_germ_preserving_field
    (shiftedSignedMorseChart c k) hgerm
  exact ⟨d, hd⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
