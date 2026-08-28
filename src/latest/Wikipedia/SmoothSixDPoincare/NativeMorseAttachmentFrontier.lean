import Wikipedia.SmoothSixDPoincare.ManifoldHandleNeighborhood
import Wikipedia.SmoothSixDPoincare.MorseAttachmentFrontier

/-! # The exact attachment frontier in the original native Morse chart -/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
theorem mem_interior_attachingUnion_iff_model (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ interior ({z | f z ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ↔
      c.splitChart y ∈ interior (MorseHandle.attachmentRegion ρ) := by
  constructor
  · intro hi
    apply mem_interior_iff_mem_nhds.mpr
    have ht : c.splitChart y ∈ c.splitChart.target := c.splitChart.map_source' hy
    have hc : ContinuousAt c.splitChart.symm (c.splitChart y) :=
      c.splitChart.toOpenPartialHomeomorph.symm.continuousAt ht
    have hleft : c.splitChart.symm (c.splitChart y) = y := c.splitChart.left_inv' hy
    have hnear : c.splitChart.symm ⁻¹'
        interior ({z | f z ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ∈
        𝓝 (c.splitChart y) := hc.preimage_mem_nhds (by
      rw [hleft]
      exact isOpen_interior.mem_nhds hi)
    apply mem_of_superset (inter_mem (c.splitChart.open_target.mem_nhds ht) hnear)
    intro z hz
    have hmem := (c.mem_attachingUnion_iff_model ρ hρ hblock
      (c.splitChart.map_target' hz.1)).mp (interior_subset hz.2)
    rwa [c.splitChart.right_inv' hz.1] at hmem
  · exact c.mem_interior_attachingUnion_of_model ρ hρ hblock hy

variable [T2Space M]

open Classical in
theorem mem_frontier_attachingUnion_iff_model (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ frontier ({z | f z ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ↔
      c.splitChart y ∈ frontier (MorseHandle.attachmentRegion ρ) := by
  have hA : IsClosed ({z | f z ≤ f p - ρ ^ 2} ∪
      range (c.attachingHandleMap ρ hρ hblock)) :=
    (isClosed_le hf continuous_const).union
      (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range
  rw [frontier, frontier, hA.closure_eq, (MorseHandle.isClosed_attachmentRegion hρ).closure_eq]
  exact and_congr (c.mem_attachingUnion_iff_model ρ hρ hblock hy)
    (not_congr (c.mem_interior_attachingUnion_iff_model ρ hρ hblock hy))

open Classical in
/-- The exact two native frontier pieces, expressed using original height and chart norm. -/
theorem mem_frontier_attachingUnion_iff (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ frontier ({z | f z ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ↔
      (f y = f p - ρ ^ 2 ∧ ρ ≤ ‖(c.splitChart y).2‖) ∨
        (‖(c.splitChart y).2‖ = ρ ∧ f p - ρ ^ 2 ≤ f y) := by
  rw [c.mem_frontier_attachingUnion_iff_model hf ρ hρ hblock hy,
    MorseHandle.mem_frontier_attachmentRegion_iff hρ]
  have heq : f y = f p + MorseHandle.quadratic (c.splitChart y) := by
    rw [c.splitChart_equation hy]
    unfold MorseHandle.quadratic
    ring
  constructor
  · rintro (⟨hq, hv⟩ | ⟨hv, hq⟩)
    · exact Or.inl ⟨by linarith, hv⟩
    · exact Or.inr ⟨hv, by linarith⟩
  · rintro (⟨hq, hv⟩ | ⟨hv, hq⟩)
    · exact Or.inl ⟨by linarith, hv⟩
    · exact Or.inr ⟨hv, by linarith⟩

open Classical in
/-- Exactly the positive disk boundary of the actual handle lies on the attachment frontier. -/
theorem attachingHandleMap_mem_frontier_iff (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : MorseHandle.UnitDisk c.NegativeCoordinates × MorseHandle.UnitDisk c.PositiveCoordinates) :
    c.attachingHandleMap ρ hρ hblock z ∈
        frontier ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ↔
      ‖(z.2 : c.PositiveCoordinates)‖ = 1 := by
  have ht := hblock (MorseHandle.modelMap_mem_product hρ z)
  have hy : c.attachingHandleMap ρ hρ hblock z ∈ c.splitChart.source :=
    c.splitChart.map_target' ht
  rw [c.mem_frontier_attachingUnion_iff_model hf ρ hρ hblock hy]
  have heq : c.splitChart (c.attachingHandleMap ρ hρ hblock z) = MorseHandle.modelMap ρ z :=
    c.splitChart.right_inv' ht
  rw [heq, MorseHandle.modelMap_mem_frontier_attachmentRegion_iff hρ]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
