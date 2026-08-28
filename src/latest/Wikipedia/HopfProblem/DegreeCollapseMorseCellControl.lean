import Wikipedia.HopfProblem.DegreeCollapseMorseCells

/-!
# Arbitrarily small, isolated native Morse cell attachments

Retaining both the radius bound and the actual critical-band isolation
condition lets a finite collection of cells be put into disjoint bands.
The full flow and relative core deformation are constructed, not assumed.
-/

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCells

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- The core-cell attachment can be chosen within any positive radius bound,
with no other critical point in the whole closed band. -/
theorem exists_morse_cell_attachment_lt {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p)
    {R : ℝ} (hR : 0 < R) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ < R ∧ ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      (∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) ∧
      Module.finrank ℝ c.NegativeCoordinates ≤ Module.finrank ℝ E ∧
      Nonempty (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {u : MorseHandle.UnitDisk c.NegativeCoordinates | ‖(u : c.NegativeCoordinates)‖ = 1}
        (coreCellMap c ρ hρ hblock) ≃ₕ {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨r, hr, W, hW, _, heqW, hblockr⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρmin, hband⟩ :=
    exists_isolating_radius (finite_criticalPoints hf hm) p hunique (lt_min hr hR)
  have hρr : ρ < r := hρmin.trans_le (min_le_left r R)
  have hρR : ρ < R := hρmin.trans_le (min_le_right r R)
  have hblockW : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
    intro z hz
    apply hblockr
    have hrad : 2 * ρ ≤ 2 * r := by linarith
    exact ⟨closedBall_subset_closedBall hrad hz.1, closedBall_subset_closedBall hrad hz.2⟩
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
  refine ⟨ρ, hρ, hρR, c, hblock, hband, core_dimension_le c, ?_⟩
  exact ⟨(cellHandleHomotopyEquiv c ρ hρ hblock hf.continuous).trans
    ((c.attachingHandleUnionHomeomorph hf.continuous ρ hρ hblock).toHomotopyEquiv.trans e)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCells
