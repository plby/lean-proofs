import Wikipedia.SmoothSixDPoincare.MorseSurgeryOfCollar
import Wikipedia.SmoothSixDPoincare.SmoothMorseFlowCollar

/-!
# Constructing native Morse surgery records with smooth original exteriors

The adapted field, controlled block, collar, and whole-sublevel realization
are all constructed from the original smooth Morse function. Radius control,
critical isolation, model boundary orbits, and both smooth exterior maps are
retained in the same surgery record.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_morseSurgeryData_smoothExterior_lt {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : MorseSurgeryData E f p, d.radius < ε ∧
      (∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p) ∧
      d.HasSmoothExterior hf := by
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
  let _ : CompactSpace ↥({x : M | f x ≤ f p + ρ ^ 2}) :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  obtain ⟨hlower, hupper, R, hforward, hbackward⟩ :=
    c.exists_attachingFlowCollar_with_smooth_exteriors hf hV hzero hdesc F hcurve
      ρ hρ hblock hagreement hband
  have hfronta := FlowConstruction.frontier_sublevel_eq_of_regular_level
    hf hV hzero hdesc F hcurve hlower
  have hfrontb := FlowConstruction.frontier_sublevel_eq_of_regular_level
    hf hV hzero hdesc F hcurve hupper
  have hmodel : c.FollowsModelBoundaryOrbits ρ hρ hblock R.sublevelRealization := by
    apply c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hcurve ρ hρ hblock
      (e := R.sublevelRealization) (horbit := R.sublevelRealization_orbit hfrontb)
    intro z hz
    filter_upwards [hW.mem_nhds (hblockW hz).2] with y hy
    exact heqW y hy
  refine ⟨c.surgeryDataOfCollar ρ hρ hblock R hfronta hfrontb hlower hupper hmodel hf.continuous,
    hρε, hband, ?_⟩
  exact c.surgeryDataOfCollar_hasSmoothExterior ρ hρ hblock R hfronta hfrontb
    hlower hupper hmodel hf hforward hbackward

theorem exists_morseSurgeryData_smoothExterior {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ d : MorseSurgeryData E f p, d.HasSmoothExterior hf := by
  obtain ⟨d, _, _, hd⟩ := exists_morseSurgeryData_smoothExterior_lt hf hm hp hunique zero_lt_one
  exact ⟨d, hd⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
