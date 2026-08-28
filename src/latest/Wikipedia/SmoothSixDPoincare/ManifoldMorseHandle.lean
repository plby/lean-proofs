import Wikipedia.SmoothSixDPoincare.ManifoldSplitMorseChart
import Wikipedia.SmoothSixDPoincare.MorseHandleModel

/-!
# A genuine embedded local handle at each Morse critical point

The explicit curved product of Euclidean disks is inserted into the actual
manifold Morse chart. Its lower-sublevel overlap is exactly its negative
boundary face. Proving that this handle accounts for the whole change in
the global sublevel still requires a separate attachment theorem.
-/

noncomputable section

open Set Metric Manifold Topology
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} (c : SignedMorseChart (E := E) f x)

open Classical in
/-- Insert the curved handle into the actual Morse chart. -/
def attachingHandleMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    C(MorseHandle.UnitDisk c.NegativeCoordinates ×
      MorseHandle.UnitDisk c.PositiveCoordinates, M) where
  toFun z := c.splitChart.symm (MorseHandle.modelMap ρ z)
  continuous_toFun := c.splitChart.toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
    (MorseHandle.continuous_modelMap ρ) (fun z => hblock (MorseHandle.modelMap_mem_product hρ z))

open Classical in
theorem attachingHandleMap_injective (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    Function.Injective (c.attachingHandleMap ρ hρ hblock) := by
  intro z w h
  apply MorseHandle.modelMap_injective hρ
  exact c.splitChart.toOpenPartialHomeomorph.symm.injOn
    (hblock (MorseHandle.modelMap_mem_product hρ z))
    (hblock (MorseHandle.modelMap_mem_product hρ w)) h

open Classical in
theorem attachingHandleMap_isClosedEmbedding [T2Space M] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    IsClosedEmbedding (c.attachingHandleMap ρ hρ hblock) :=
  (c.attachingHandleMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.attachingHandleMap_injective ρ hρ hblock)

open Classical in
/-- The center of the handle is the original critical point. -/
theorem attachingHandleMap_zero (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    c.attachingHandleMap ρ hρ hblock (⟨0, by simp⟩, ⟨0, by simp⟩) = x := by
  change c.splitChart.symm (MorseHandle.modelMap ρ (⟨0, by simp⟩, ⟨0, by simp⟩)) = x
  simp only [MorseHandle.modelMap, smul_zero]
  rw [show ((0 : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) = c.splitChart x
    from c.splitChart_center.symm]
  exact c.splitChart.toOpenPartialHomeomorph.left_inv c.splitChart_mem_source

open Classical in
theorem attachingHandleMap_quadratic (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : MorseHandle.UnitDisk c.NegativeCoordinates × MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) =
      f x + (-‖(MorseHandle.modelMap ρ z).1‖ ^ 2 + ‖(MorseHandle.modelMap ρ z).2‖ ^ 2) := by
  change f (c.splitChart.symm (MorseHandle.modelMap ρ z)) = _
  rw [c.splitChart_inverse_equation (hblock (MorseHandle.modelMap_mem_product hρ z))]
  ring

open Classical in
/-- The only overlap with the lower sublevel is the negative boundary of the handle. -/
theorem attachingHandleMap_lower_iff (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : MorseHandle.UnitDisk c.NegativeCoordinates × MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) ≤ f x - ρ ^ 2 ↔ ‖(z.1 : c.NegativeCoordinates)‖ = 1 := by
  rw [c.attachingHandleMap_quadratic, sub_eq_add_neg, add_le_add_iff_left]
  exact MorseHandle.modelMap_lower_iff hρ z

open Classical in
/-- The whole embedded local handle lies in the upper sublevel. -/
theorem attachingHandleMap_upper (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : MorseHandle.UnitDisk c.NegativeCoordinates × MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) ≤ f x + ρ ^ 2 := by
  rw [c.attachingHandleMap_quadratic]
  exact add_le_add le_rfl (MorseHandle.modelMap_upper hρ z)

open Classical in
/-- Every genuine Morse chart contains an embedded attaching handle with the exact boundary overlap.
This is a local construction, not yet a description of the whole upper sublevel. -/
theorem exists_attachingHandle [T2Space M] :
    ∃ ρ > (0 : ℝ),
      ∃ h : C(MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates, M),
        IsClosedEmbedding h ∧ h (⟨0, by simp⟩, ⟨0, by simp⟩) = x ∧
          ∀ z, f (h z) ≤ f x + ρ ^ 2 ∧
            (f (h z) ≤ f x - ρ ^ 2 ↔ ‖(z.1 : c.NegativeCoordinates)‖ = 1) := by
  obtain ⟨R, hR, hblock⟩ := c.exists_closed_productBlock
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have htwo : 2 * ρ = R := by dsimp [ρ]; ring
  have hblock' : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target := by
    rw [htwo]
    exact hblock
  exact ⟨ρ, hρ, c.attachingHandleMap ρ hρ hblock',
    c.attachingHandleMap_isClosedEmbedding ρ hρ hblock', c.attachingHandleMap_zero ρ hρ hblock',
    fun z => ⟨c.attachingHandleMap_upper ρ hρ hblock' z,
      c.attachingHandleMap_lower_iff ρ hρ hblock' z⟩⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
