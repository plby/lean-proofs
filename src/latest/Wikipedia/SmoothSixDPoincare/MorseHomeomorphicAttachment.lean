import Wikipedia.SmoothSixDPoincare.MorseModelBoundaryOrbits
import Wikipedia.SmoothSixDPoincare.IsolatedMorseBand
import Wikipedia.SmoothSixDPoincare.ExcellentMorseFunction

/-!
# Constructing homeomorphic attachments for an excellent Morse function

The adapted field, local block, complete flow, and collar are constructed
from the original function. The conclusion describes the actual topology
of the whole upper sublevel by a boundary-attachment quotient.

This is not yet smooth handle cancellation or the unconditional sphere theorem.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct an arbitrarily small actual attachment, retaining the isolated
critical window and exact model-orbit formulas throughout its controlled block. -/
theorem exists_morse_boundary_attachment_with_model_orbits_lt {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ < ε ∧ ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        {x : M // f x ≤ f p + ρ ^ 2},
        (∀ x, f (e x) = f p + ρ ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
            range (c.attachingHandleMap ρ hρ hblock))) ∧
          (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
          (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
          (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
          (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) ∧
          c.FollowsModelBoundaryOrbits ρ hρ hblock e ∧
          ∀ x ∈ criticalPoints E f,
            f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨ρ, hρ, hρε, W, hW, _, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt (finite_criticalPoints hf hm) hunique V heq hε
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
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hcurve
    ρ hρ hblock hagreement hband
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hregular (b : ℝ) (hb : b ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p)
      (x : M) (hx : f x = b) : x ∉ criticalPoints E f := by
    intro hcrit
    have hxp := hband x hcrit (hx ▸ hb)
    exact hne (hx.symm.trans (congrArg f hxp))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t →
      f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hstrict := FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp))
      F hcurve hzero hdesc (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hstrict
  refine ⟨ρ, hρ, hρε, c, hblock, e, hfront, hfixed,
    FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono hbottom,
    hlower, hupper, ?_, hband⟩
  apply c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hcurve ρ hρ hblock
    (e := e) (horbit := horbit)
  intro z hz
  filter_upwards [hW.mem_nhds (hblockW hz).2] with y hy
  exact heqW y hy

open Classical in
/-- Construct the actual attachment, retaining exact model-orbit formulas
throughout the controlled Morse block. -/
theorem exists_morse_boundary_attachment_with_model_orbits {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        {x : M // f x ≤ f p + ρ ^ 2},
        (∀ x, f (e x) = f p + ρ ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
            range (c.attachingHandleMap ρ hρ hblock))) ∧
          (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
          (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
          (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
          (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) ∧
          c.FollowsModelBoundaryOrbits ρ hρ hblock e := by
  obtain ⟨ρ, hρ, _, c, hblock, e, hfront, hfixed, hlevel, hlower, hupper, horbits, _⟩ :=
    exists_morse_boundary_attachment_with_model_orbits_lt hf hm hp hunique zero_lt_one
  exact ⟨ρ, hρ, c, hblock, e, hfront, hfixed, hlevel, hlower, hupper, horbits⟩

open Classical in
/-- Construct the homeomorphic handle attachment at a uniquely valued Morse critical point. -/
theorem exists_morse_boundary_attachment_with_regular_levels_and_fixed {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        {x : M // f x ≤ f p + ρ ^ 2},
        (∀ x, f (e x) = f p + ρ ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
            range (c.attachingHandleMap ρ hρ hblock))) ∧
          (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
          (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
          (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
          (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) := by
  obtain ⟨ρ, hρ, c, hblock, e, hfront, hfixed, hlevel, hlower, hupper, -⟩ :=
    exists_morse_boundary_attachment_with_model_orbits hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, e, hfront, hfixed, hlevel, hlower, hupper⟩

open Classical in
/-- Retain actual regularity of both endpoint levels in the constructed Morse attachment. -/
theorem exists_morse_boundary_attachment_with_regular_levels {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        {x : M // f x ≤ f p + ρ ^ 2},
        (∀ x, f (e x) = f p + ρ ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
            range (c.attachingHandleMap ρ hρ hblock))) ∧
          (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
          (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
          (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) := by
  obtain ⟨ρ, hρ, c, hblock, e, he, -, hlevel, hlower, hupper⟩ :=
    exists_morse_boundary_attachment_with_regular_levels_and_fixed hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, e, he, hlevel, hlower, hupper⟩

open Classical in
/-- Construct the attachment together with the actual lower sublevel frontier identity. -/
theorem exists_morse_boundary_attachment_with_lower_frontier {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        {x : M // f x ≤ f p + ρ ^ 2},
        (∀ x, f (e x) = f p + ρ ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
            range (c.attachingHandleMap ρ hρ hblock))) ∧
          frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2} := by
  obtain ⟨ρ, hρ, c, hblock, e, he, hlevel, -, -⟩ :=
    exists_morse_boundary_attachment_with_regular_levels hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, e, he, hlevel⟩

open Classical in
/-- Construct the homeomorphic handle attachment at a uniquely valued Morse critical point. -/
theorem exists_morse_boundary_attachment {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        {x : M // f x ≤ f p + ρ ^ 2},
        ∀ x, f (e x) = f p + ρ ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
            range (c.attachingHandleMap ρ hρ hblock)) := by
  obtain ⟨ρ, hρ, c, hblock, e, hfront, -⟩ :=
    exists_morse_boundary_attachment_with_lower_frontier hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, e, hfront⟩

open Classical in
/-- Construct the homeomorphic handle attachment at a uniquely valued Morse critical point. -/
theorem exists_morse_homeomorphic_attachment {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      Nonempty (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₜ
          {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨ρ, hρ, c, hblock, e, -⟩ := exists_morse_boundary_attachment hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock,
    ⟨(c.attachingHandleUnionHomeomorph hf.continuous ρ hρ hblock).trans e⟩⟩

variable (E M) in
open Classical in
/-- Construct a smooth Morse function with distinct critical values and homeomorphic attachments. -/
theorem exists_morse_function_with_homeomorphic_attachments :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      (criticalPoints E f).Finite ∧ InjOn f (criticalPoints E f) ∧
      ∀ p ∈ criticalPoints E f, ∃ (ρ : ℝ) (hρ : 0 < ρ),
        ∃ c : SignedMorseChart (E := E) f p,
        ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
        Nonempty (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
          {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₜ
            {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨f, hf, hm, hfinite, hinj⟩ := exists_morse_function_with_distinct_critical_values E M
  refine ⟨f, hf, hm, hfinite, hinj, ?_⟩
  intro p hp
  exact exists_morse_homeomorphic_attachment hf hm hp (fun x hx heq => hinj hx hp heq)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
