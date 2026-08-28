import Wikipedia.SmoothSixDPoincare.AbsorbingFlowCollar
import Wikipedia.SmoothSixDPoincare.MorseCriticalHomeomorph

/-!
# The actual flow collar for a controlled native Morse attachment

The signed Morse block, field agreement, and isolated critical band imply
all hypotheses of the absorbing collar construction. The result retains
the collar itself, so its whole-sublevel homeomorphism and original smooth
exterior maps can be used together.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

theorem nonempty_attachingFlowCollar
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband : ∀ x ∈ criticalPoints E f,
      f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    Nonempty (FlowConstruction.FlowCollarData F
      ({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock))
      {x | f x ≤ f p + ρ ^ 2}) := by
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hboundary (b : ℝ) (hb : b ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p)
      (x : M) (hx : f x = b) (t : ℝ) (ht : 0 < t) : f (F t x) < f x := by
    have hreg : x ∉ criticalPoints E f := by
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
  exact FlowConstruction.nonempty_absorbingSublevelFlowCollar hf hV hdesc F hcurve hmono
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

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
