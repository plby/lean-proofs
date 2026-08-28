import Wikipedia.SmoothSixDPoincare.MorseCriticalAttachment
import Wikipedia.SmoothSixDPoincare.IsolatedMorseBand
import Wikipedia.SmoothSixDPoincare.ExcellentMorseFunction

/-!
# Constructing the homotopy attachment from a smooth Morse function

For a critical point with a unique critical value, this theorem constructs
the Morse chart, handle radius, exact-field neighborhood, descending flow,
and homotopy equivalence with the actual boundary-attachment quotient.
None of those constructions is an input hypothesis.

The uniqueness of the chosen critical value remains an explicit Morse
function hypothesis. Handle cancellation and sphere recognition remain
separate obligations.
-/

noncomputable section

open Set Metric Manifold Filter ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct the genuine handle-attachment quotient accounting for the homotopy change across
a uniquely valued Morse critical point, directly from the original smooth Morse function. -/
theorem exists_morse_attachment {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      Nonempty (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₕ
          {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨ρ, hρ, W, hW, _, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock (finite_criticalPoints hf hm) hunique V heq
  have hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    have hxW : c.attachingHandleMap ρ hρ hblock z ∈ W :=
      (hblockW (MorseHandle.modelMap_mem_product hρ z)).2
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact heqW y hy
  obtain ⟨e, _⟩ := c.exists_attachingUnionHomotopyEquiv hf hV hzero hdesc F hcurve
    ρ hρ hblock hagreement hband
  exact ⟨ρ, hρ, c, hblock,
    ⟨(c.attachingHandleUnionHomeomorph hf.continuous ρ hρ hblock).toHomotopyEquiv.trans e⟩⟩

variable (E M) in
open Classical in
/-- Construct a global Morse function with finite distinct critical values and a genuine
homotopy-attachment description at every critical point, from smoothness and compactness alone. -/
theorem exists_morse_function_with_attachments :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      (criticalPoints E f).Finite ∧ InjOn f (criticalPoints E f) ∧
      ∀ p ∈ criticalPoints E f, ∃ (ρ : ℝ) (hρ : 0 < ρ),
        ∃ c : SignedMorseChart (E := E) f p,
        ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
        Nonempty (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
          {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₕ
            {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨f, hf, hm, hfinite, hinj⟩ := exists_morse_function_with_distinct_critical_values E M
  refine ⟨f, hf, hm, hfinite, hinj, ?_⟩
  intro p hp
  exact exists_morse_attachment hf hm hp (fun x hx heq => hinj hx hp heq)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
