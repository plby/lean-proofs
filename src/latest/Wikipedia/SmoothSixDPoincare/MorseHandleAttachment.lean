import Wikipedia.SmoothSixDPoincare.ManifoldMorseHandle
import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!
# The local handle attached to the actual lower sublevel

This identifies the union of the lower sublevel and the constructed handle
with its genuine boundary-attachment quotient. The union lies in the upper
sublevel; no equivalence with the whole upper sublevel is claimed here.
-/

noncomputable section

open Set Metric Manifold Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} (c : SignedMorseChart (E := E) f x)

open Classical in
/-- The whole negative boundary face maps to exactly the bottom level. -/
theorem attachingHandleMap_boundary_height (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : MorseHandle.UnitDisk c.NegativeCoordinates × MorseHandle.UnitDisk c.PositiveCoordinates)
    (hz : ‖(z.1 : c.NegativeCoordinates)‖ = 1) :
    f (c.attachingHandleMap ρ hρ hblock z) = f x - ρ ^ 2 := by
  rw [c.attachingHandleMap_quadratic, MorseHandle.modelMap_height hρ z, hz]
  ring

open Classical in
/-- The attaching map from the genuine sphere times disk into the lower level set. -/
def attachingBoundaryMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    C(sphere (0 : c.NegativeCoordinates) 1 × MorseHandle.UnitDisk c.PositiveCoordinates,
      {y : M // f y = f x - ρ ^ 2}) where
  toFun z :=
    ⟨c.attachingHandleMap ρ hρ hblock (⟨z.1, sphere_subset_closedBall z.1.2⟩, z.2),
      c.attachingHandleMap_boundary_height ρ hρ hblock _ (by
        simpa only [mem_sphere, dist_zero_right] using z.1.2)⟩
  continuous_toFun := ((c.attachingHandleMap ρ hρ hblock).continuous.comp
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
      continuous_snd)).subtype_mk _

open Classical in
/-- Attaching the constructed handle to the lower sublevel gives exactly their actual union. -/
def attachingHandleUnionHomeomorph [T2Space M] [CompactSpace M] (hf : Continuous f)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    ClosedAttachment.Space {y : M | f y ≤ f x - ρ ^ 2}
      {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₜ
        ↥({y : M | f y ≤ f x - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) :=
  ClosedAttachment.unionHomeomorph _ _ _ (isClosed_le hf continuous_const).isCompact
    (c.attachingHandleMap_injective ρ hρ hblock)
    (fun z => c.attachingHandleMap_lower_iff ρ hρ hblock z)

open Classical in
/-- The lower sublevel with its embedded handle is a genuine subspace of the upper sublevel. -/
theorem attachingHandleUnion_subset_upper (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    {y : M | f y ≤ f x - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock) ⊆
      {y : M | f y ≤ f x + ρ ^ 2} := by
  rintro y (hy | ⟨z, rfl⟩)
  · change f y ≤ f x + ρ ^ 2
    change f y ≤ f x - ρ ^ 2 at hy
    nlinarith [sq_nonneg ρ]
  · exact c.attachingHandleMap_upper ρ hρ hblock z

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
