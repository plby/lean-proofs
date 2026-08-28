import Wikipedia.SmoothSixDPoincare.ManifoldMorseHandle
import Wikipedia.SmoothSixDPoincare.MorseModelFlow

/-!
# The embedded handle is a neighborhood of its critical center

The curved handle contains an ambient coordinate neighborhood. Transport
through the genuine Morse chart proves the corresponding neighborhood
statement in the original manifold topology, in every Morse index.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The actual embedded handle contains a neighborhood of its critical point. -/
theorem range_attachingHandleMap_mem_nhds (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    range (c.attachingHandleMap ρ hρ hblock) ∈ 𝓝 p := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hnhds := e.symm.image_mem_nhds hzero
    (MorseHandle.range_modelMap_mem_nhds_zero (N := c.NegativeCoordinates)
      (P := c.PositiveCoordinates) hρ)
  rw [hinv] at hnhds
  apply mem_of_superset hnhds
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact ⟨z, rfl⟩

open Classical in
/-- In particular, the critical point lies in the interior of the handle's image. -/
theorem mem_interior_range_attachingHandleMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    p ∈ interior (range (c.attachingHandleMap ρ hρ hblock)) :=
  mem_interior_iff_mem_nhds.mpr (c.range_attachingHandleMap_mem_nhds ρ hρ hblock)

open Classical in
/-- Membership in the embedded handle is exactly membership in its coordinate model. -/
theorem mem_range_attachingHandleMap_iff (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ range (c.attachingHandleMap ρ hρ hblock) ↔
      c.splitChart y ∈ range (MorseHandle.modelMap ρ) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    exact (c.splitChart.toOpenPartialHomeomorph.right_inv
      (hblock (MorseHandle.modelMap_mem_product hρ z))).symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change c.splitChart.symm (MorseHandle.modelMap ρ z) = y
    rw [hz]
    exact c.splitChart.toOpenPartialHomeomorph.left_inv hy

open Classical in
/-- The handle image in the original manifold is described by two coordinate inequalities. -/
theorem mem_range_attachingHandleMap_iff_inequalities (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ range (c.attachingHandleMap ρ hρ hblock) ↔
      ‖(c.splitChart y).2‖ ≤ ρ ∧ f p - ρ ^ 2 ≤ f y := by
  rw [c.mem_range_attachingHandleMap_iff ρ hρ hblock hy, MorseHandle.mem_range_modelMap_iff hρ]
  apply and_congr_right
  intro _
  rw [c.splitChart_equation hy]
  constructor <;> intro h <;> linarith

open Classical in
/-- The lower sublevel with its handle adjoined has exactly the model description in the chart. -/
theorem mem_attachingUnion_iff_model (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ {z | f z ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock) ↔
      c.splitChart y ∈ {z | MorseHandle.quadratic z ≤ -(ρ ^ 2)} ∪
        range (MorseHandle.modelMap ρ) := by
  change (f y ≤ f p - ρ ^ 2 ∨ y ∈ range (c.attachingHandleMap ρ hρ hblock)) ↔
    (MorseHandle.quadratic (c.splitChart y) ≤ -(ρ ^ 2) ∨
      c.splitChart y ∈ range (MorseHandle.modelMap ρ))
  rw [c.mem_range_attachingHandleMap_iff ρ hρ hblock hy]
  apply or_congr_left
  rw [c.splitChart_equation hy]
  unfold MorseHandle.quadratic
  constructor <;> intro h <;> linarith

open Classical in
/-- Interior membership in the model attachment transfers to the original manifold topology. -/
theorem mem_interior_attachingUnion_of_model (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source)
    (hi : c.splitChart y ∈ interior ({z | MorseHandle.quadratic z ≤ -(ρ ^ 2)} ∪
      range (MorseHandle.modelMap ρ))) :
    y ∈ interior ({z | f z ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hp := (c.splitChart.toOpenPartialHomeomorph.continuousAt hy).preimage_mem_nhds
    (mem_interior_iff_mem_nhds.mp hi)
  apply mem_of_superset (inter_mem (c.splitChart.open_source.mem_nhds hy) hp)
  intro z hz
  exact (c.mem_attachingUnion_iff_model ρ hρ hblock hz.1).mpr hz.2

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
