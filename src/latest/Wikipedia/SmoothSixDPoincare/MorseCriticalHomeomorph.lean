import Wikipedia.SmoothSixDPoincare.MorseCriticalAttachment
import Wikipedia.SmoothSixDPoincare.SublevelAttachmentHomeomorph
import Wikipedia.SmoothSixDPoincare.FlowSublevelFrontier

/-!
# Homeomorphic handle attachment across a Morse critical point

Strict absorption of the genuine curved handle and regularity of the
upper level give an actual homeomorphism, strengthening the previously
constructed homotopy equivalence. No smooth cancellation is asserted.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The actual attachment homeomorphism, including the backward-flow formula
on its whole frontier. -/
theorem exists_attachingUnionHomeomorph_with_level_and_orbits
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband : ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2},
      (∀ x, f (e x) = f p + ρ ^ 2 ↔
        x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
          range (c.attachingHandleMap ρ hρ hblock))) ∧
      (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
      (∀ x, x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
          range (c.attachingHandleMap ρ hρ hblock)) →
        ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) := by
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hboundary (b : ℝ) (hb : b ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p)
      (x : M) (hx : f x = b) (t : ℝ) (ht : 0 < t) : f (F t x) < f x := by
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp := hband x hcrit (hx ▸ hb)
      exact hne (hx.symm.trans (congrArg f hxp))
    simpa only [F.map_zero_apply] using
      FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x :=
    hboundary _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have htop : ∀ x, f x = f p + ρ ^ 2 → ∀ t : ℝ, 0 < t →
      f (F t x) < f p + ρ ^ 2 := by
    intro x hx t ht
    rw [← hx]
    exact hboundary _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩
      (by nlinarith [sq_pos_of_pos hρ]) x hx t ht
  have hhome := FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits
    hf hV hdesc F hcurve hmono
    ((isClosed_le hf.continuous continuous_const).union
      (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
    subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock)
    (a := f p - ρ ^ 2)
    (fun x hcrit hx => by
      have hxp := hband x hcrit hx
      subst x
      exact interior_mono subset_union_right
        (c.mem_interior_range_attachingHandleMap ρ hρ hblock))
    (c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement)
    (c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock
      hagreement hbottom) htop
  obtain ⟨e, hfront, hfixed, horbit⟩ := hhome
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro x
    have hx := hfront (e.symm x)
    rw [e.apply_symm_apply,
      FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop] at hx
    exact hx.symm
  · intro x hx
    let y : {x : M // f x ≤ f p + ρ ^ 2} := ⟨x.val, hx.le⟩
    have hy : y.val ∈ frontier {z : M | f z ≤ f p + ρ ^ 2} := by
      rw [FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
      exact hx
    have heq : e y = x := Subtype.ext (hfixed y x.property hy)
    have hh := congrArg e.symm heq
    rw [e.symm_apply_apply] at hh
    exact congrArg (fun z : {z : M // f z ≤ f p + ρ ^ 2} => z.val) hh.symm
  · intro x hx t ht hlevel
    apply horbit x hx t ht
    rw [FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
    exact hlevel

open Classical in
/-- The whole upper sublevel is homeomorphic to the actual lower sublevel with its handle. -/
theorem exists_attachingUnionHomeomorph_with_level_and_fixed
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband : ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2},
      (∀ x, f (e x) = f p + ρ ^ 2 ↔
        x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
          range (c.attachingHandleMap ρ hρ hblock))) ∧
      (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) := by
  obtain ⟨e, hlevel, hfixed, -⟩ := c.exists_attachingUnionHomeomorph_with_level_and_orbits
    hf hV hzero hdesc F hcurve ρ hρ hblock hagreement hband
  exact ⟨e, hlevel, hfixed⟩

open Classical in
/-- The actual attachment homeomorphism with its precise level/frontier correspondence. -/
theorem exists_attachingUnionHomeomorph_with_level
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband : ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2},
      ∀ x, f (e x) = f p + ρ ^ 2 ↔
        x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
          range (c.attachingHandleMap ρ hρ hblock)) := by
  obtain ⟨e, he, -⟩ := c.exists_attachingUnionHomeomorph_with_level_and_fixed
    hf hV hzero hdesc F hcurve ρ hρ hblock hagreement hband
  exact ⟨e, he⟩

open Classical in
/-- The whole upper sublevel is homeomorphic to the actual lower sublevel with its handle. -/
theorem nonempty_attachingUnionHomeomorph
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband : ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    Nonempty (↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨e, -⟩ := c.exists_attachingUnionHomeomorph_with_level hf hV hzero hdesc F hcurve
    ρ hρ hblock hagreement hband
  exact ⟨e⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
