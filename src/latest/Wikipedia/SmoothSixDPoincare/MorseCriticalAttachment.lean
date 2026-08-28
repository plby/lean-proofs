import Wikipedia.SmoothSixDPoincare.HandleFlowTrapping
import Wikipedia.SmoothSixDPoincare.SublevelAttachmentDeformation
import Wikipedia.SmoothSixDPoincare.MorseHandleAttachment

/-!
# Homotopy attachment across a single Morse critical point

The actual lower sublevel union the embedded handle includes into the
upper sublevel by a homotopy equivalence. The derivative and flow hypotheses
are supplied by the earlier adapted-field construction; the band must
contain no other critical point, and the field must agree with the Morse
field near the entire handle.

This is a homotopy attachment theorem, not a smooth handle-cancellation
theorem or a proof of the sphere-recognition target.
-/

noncomputable section

open Set Metric Manifold Filter ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The constructed handle accounts for the homotopy change across its isolated critical band. -/
theorem exists_attachingUnionHomotopyEquiv
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
    ∃ e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₕ
      {x : M // f x ≤ f p + ρ ^ 2}, ∀ x, (e x).1 = x.1 := by
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x := by
    intro x hx t ht
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp : x = p := hband x hcrit ⟨hx.ge, by rw [hx]; linarith [sq_nonneg ρ]⟩
      rw [hxp] at hx
      nlinarith [sq_pos_of_pos hρ]
    simpa only [F.map_zero_apply] using
      FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  apply FlowConstruction.exists_absorbingSublevelHomotopyEquiv hf hV hdesc F hcurve hmono
    ((isClosed_le hf.continuous continuous_const).union
      (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
    subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock)
    (a := f p - ρ ^ 2)
  · intro x hcrit hx
    have hxp := hband x hcrit hx
    subst x
    exact interior_mono subset_union_right (c.mem_interior_range_attachingHandleMap ρ hρ hblock)
  · exact c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
  · exact c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock
      hagreement hbottom

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
