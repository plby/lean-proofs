import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryWindows

/-!
# Native surgery data retaining a prescribed field and signed chart

Shrink the original signed chart inside the supplied field germ, construct
the actual attachment using that same flow, and retain model-field germs
on the whole closed surgery block. No fresh descent field is substituted.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem exists_morseSurgeryData_of_field_germ_lt
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hfinite : (criticalPoints E f).Finite)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p : M} (c : SignedMorseChart (E := E) f p)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : MorseSurgeryData E f p, d.radius < ε ∧ d.chart = c ∧
      (∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p) ∧
      ∀ z, z ∈ closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
        closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) →
        ∀ᶠ x in 𝓝 (d.chart.splitChart.symm z), V x = d.chart.descentField x := by
  obtain ⟨ρ, hρ, hρε, W, hW, -, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt hfinite hunique V heq hε
  have hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hmodel : ∀ z, z ∈ closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) →
      ∀ᶠ x in 𝓝 (c.splitChart.symm z), V x = c.descentField x := by
    intro z hz
    filter_upwards [hW.mem_nhds (hblockW hz).2] with x hx
    exact heqW x hx
  have hagreement : ∀ x ∈ range (c.attachingHandleMap ρ hρ hblock),
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    exact hmodel _ (MorseHandle.modelMap_mem_product hρ z)
  obtain ⟨e, hfront, hfixed, horbit⟩ := c.exists_attachingUnionHomeomorph_with_level_and_orbits
    hf hV hzero hdesc F hF ρ hρ hblock hagreement hband
  have hregular (b : ℝ) (hb : b ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p)
      (x : M) (hx : f x = b) : x ∉ criticalPoints E f := by
    intro hcrit
    exact hne (hx.symm.trans (congrArg f (hband x hcrit (hx ▸ hb))))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t →
      f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hh := FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp))
      F hF hzero hdesc (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hh
  have hlevel := FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F
    (FlowConstruction.antitone_flow_height hf F hF hzero hdesc) hbottom
  have horbits := c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hF
    ρ hρ hblock (e := e) (horbit := horbit) hmodel
  exact ⟨{
    radius := ρ
    radius_pos := hρ
    chart := c
    block := hblock
    attachmentHomeomorph := e
    attachment_frontier := hfront
    attachment_fixed := hfixed
    attachment_model_orbits := horbits
    surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e hfront
    oldExterior_eq := fun _ => rfl
    newExterior_eq := fun _ => rfl
    oldPiece_eq := fun _ => rfl
    newPiece_eq := fun _ => rfl
    belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e hfront hfixed
    lower_regular := hlower
    upper_regular := hupper }, hρε, rfl, hband, hmodel⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
