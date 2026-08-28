import Wikipedia.HopfProblem.DegreeCollapseMorseSectionNeighborhood
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseLevelExit

/-!
# Actual exits near the full original core sections

Given any open neighborhood of the original belt sphere, every point
sufficiently near the critical point outside the pure negative plane has
an actual backward level crossing in that neighborhood. The dual statement
holds for the attaching sphere and forward crossings. No orbit or label
near the critical point is replaced by a model-only surrogate.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

open Classical in
theorem morse_coordinate_neighborhood (c : SignedMorseChart (E := E) f p)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source ∧
      ‖(c.splitChart x).1‖ < a ∧ ‖(c.splitChart x).2‖ < b := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hn : ‖(c.splitChart p).1‖ < a := by
    simpa only [c.splitChart_center, Prod.fst_zero, norm_zero] using ha
  have hp : ‖(c.splitChart p).2‖ < b := by
    simpa only [c.splitChart_center, Prod.snd_zero, norm_zero] using hb
  have hs : ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hna : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).1‖ < a := hc.fst.norm (eventually_lt_nhds hn)
  have hpb : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).2‖ < b := hc.snd.norm (eventually_lt_nhds hp)
  exact hs.and (hna.and hpb)

variable [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

open Classical in
theorem eventually_backward_exit_in_belt_neighborhood (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {U : Set M} (hU : IsOpen U)
    (hcore : ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).2 ≠ 0 →
      ∃ T : ℝ, T < 0 ∧ f (F T x) = f p + r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_upper_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c (lt_min hr hδ) hr] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_backward_morse_level_exit c hV F hF hr hblock hfield hx.1
      (hx.2.1.trans_le (min_le_left _ _)) hx.2.2 hne
  have hq : MorseHandle.quadratic (c.splitChart (F T x)) = r ^ 2 := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = r ^ 2
    linarith
  have hh := hsection (c.splitChart (F T x)) hbox hq
    (hsmall.trans_lt (hx.2.1.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x :=
    c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

open Classical in
theorem eventually_forward_exit_in_attaching_neighborhood (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {U : Set M} (hU : IsOpen U)
    (hcore : ∀ v : PuncturedHandle.UnitSphere c.NegativeCoordinates,
      (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).1 ≠ 0 →
      ∃ T : ℝ, 0 < T ∧ f (F T x) = f p - r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_lower_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c hr (lt_min hr hδ)] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_forward_morse_level_exit c hV F hF hr hblock hfield hx.1
      hx.2.1 (hx.2.2.trans_le (min_le_left _ _)) hne
  have hq : MorseHandle.quadratic (c.splitChart (F T x)) = -(r ^ 2) := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = -(r ^ 2)
    linarith
  have hh := hsection (c.splitChart (F T x)) hbox hq
    (hsmall.trans_lt (hx.2.2.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x :=
    c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
