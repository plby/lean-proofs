import Wikipedia.SmoothSixDPoincare.MorseFlowCollar
import Wikipedia.SmoothSixDPoincare.SmoothSublevelCollarExterior

/-!
# A constructed Morse flow collar with both original exteriors smooth

Regularity of the two endpoint levels follows from the isolated critical
band. The descending native field supplies the actual frontier identities
and transversality. The resulting chosen collar retains one whole-sublevel
homeomorphism, with smooth lower and upper exterior maps in the original
regular-level atlases.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem frontier_sublevel_eq_of_regular_level {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {b : ℝ} (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    frontier {x | f x ≤ b} = {x | f x = b} := by
  apply frontier_sublevel_eq_of_strict_flow hf.continuous F
    (antitone_flow_height hf F hcurve hzero hdesc)
  intro x hx t ht
  have h := strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc (hreg x hx) ht
  simpa only [F.map_zero_apply, hx] using h

end Wikipedia.SmoothSixDPoincare.FlowConstruction

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

theorem exists_attachingFlowCollar_with_smooth_exteriors
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
    letI : CompactSpace ↥({x : M | f x ≤ f p + ρ ^ 2}) :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    ∃ (hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f)
      (hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f)
      (d : FlowConstruction.FlowCollarData F
        ({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock))
        {x | f x ≤ f p + ρ ^ 2}),
      (letI := RegularLevel.chartedSpace hf hlower;
        ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ d.lowerExteriorMap
          {x | x.val ∉ range (c.attachingHandleMap ρ hρ hblock)}) ∧
      (letI := RegularLevel.chartedSpace hf hupper;
        ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ d.upperExteriorMap
          {x | d.upperExteriorMap x ∉ range (c.attachingHandleMap ρ hρ hblock)}) := by
  let _ : CompactSpace ↥({x : M | f x ≤ f p + ρ ^ 2}) :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  have hregular (b : ℝ) (hb : b ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p)
      (x : M) (hx : f x = b) : x ∉ criticalPoints E f := by
    intro hcrit
    have hxp := hband x hcrit (hx ▸ hb)
    exact hne (hx.symm.trans (congrArg f hxp))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  obtain ⟨d⟩ := c.nonempty_attachingFlowCollar hf hV hzero hdesc F hcurve
    ρ hρ hblock hagreement hband
  have hfronta := FlowConstruction.frontier_sublevel_eq_of_regular_level
    hf hV hzero hdesc F hcurve hlower
  have hfrontb := FlowConstruction.frontier_sublevel_eq_of_regular_level
    hf hV hzero hdesc F hcurve hupper
  have hK := (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range
  refine ⟨hlower, hupper, d, ?_, ?_⟩
  · exact d.contMDiffOn_lowerExteriorMap hV hcurve hf hK hlower hfronta hfrontb
      (fun x hx => (hdesc x (hupper x hx)).ne)
  · exact d.contMDiffOn_upperExteriorMap hV hcurve hf hK hupper hfrontb
      (fun x hx => (hdesc x (hlower x hx)).ne)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
