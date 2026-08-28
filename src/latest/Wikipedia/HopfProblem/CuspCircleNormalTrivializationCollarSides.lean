import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarActual
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarStandardSides

/-!
# Inside, boundary, and outside of the actual compact disk in collar coordinates

The radial collar parameter has the expected sign in the literal original
threefold: negative means interior, zero means the true frontier, and
positive means outside the compact disk image. No complement model is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace

theorem radialScale_le_half_iff (t : ℝ) : radialScale t ≤ (1 / 2 : ℝ) ↔ t ≤ 0 := by
  dsimp [radialScale]
  constructor <;> intro h <;> linarith

theorem radialScale_lt_half_iff (t : ℝ) : radialScale t < (1 / 2 : ℝ) ↔ t < 0 := by
  dsimp [radialScale]
  constructor <;> intro h <;> linarith

theorem radialScale_eq_half_iff (t : ℝ) : radialScale t = (1 / 2 : ℝ) ↔ t = 0 := by
  dsimp [radialScale]
  constructor <;> intro h <;> linarith

theorem half_lt_radialScale_iff (t : ℝ) : (1 / 2 : ℝ) < radialScale t ↔ 0 < t := by
  dsimp [radialScale]
  constructor <;> intro h <;> linarith

/-- The nonpositive half-collar is exactly the actual closed disk image. -/
theorem actualMap_mem_closedDiskNeighborhood_iff (p : Domain) :
    actualMap p ∈ closedDiskNeighborhood ↔ (p.2 : ℝ) ≤ 0 := by
  change (standardNeighborhoodDiffeomorph (standardProductMap p) : Threefold.Space) ∈
    closedDiskNeighborhood ↔ _
  rw [standardNeighborhoodDiffeomorph_mem_closedDiskNeighborhood_iff,
    norm_standardProductMap_snd, radialScale_le_half_iff]

/-- The negative half-collar is exactly the actual ambient interior. -/
theorem actualMap_mem_interior_closedDiskNeighborhood_iff (p : Domain) :
    actualMap p ∈ interior closedDiskNeighborhood ↔ (p.2 : ℝ) < 0 := by
  change (standardNeighborhoodDiffeomorph (standardProductMap p) : Threefold.Space) ∈
    interior closedDiskNeighborhood ↔ _
  rw [standardNeighborhoodDiffeomorph_mem_interior_closedDiskNeighborhood_iff,
    norm_standardProductMap_snd, radialScale_lt_half_iff]

/-- The zero parameter is exactly the genuine frontier in the original threefold. -/
theorem actualMap_mem_frontier_closedDiskNeighborhood_iff (p : Domain) :
    actualMap p ∈ frontier closedDiskNeighborhood ↔ (p.2 : ℝ) = 0 := by
  change (standardNeighborhoodDiffeomorph (standardProductMap p) : Threefold.Space) ∈
    frontier closedDiskNeighborhood ↔ _
  rw [standardNeighborhoodDiffeomorph_mem_frontier_closedDiskNeighborhood_iff,
    norm_standardProductMap_snd, radialScale_eq_half_iff]

/-- The positive half-collar is exactly outside the actual compact disk image. -/
theorem actualMap_not_mem_closedDiskNeighborhood_iff (p : Domain) :
    actualMap p ∉ closedDiskNeighborhood ↔ 0 < (p.2 : ℝ) := by
  rw [actualMap_mem_closedDiskNeighborhood_iff, not_le]

/-- The inverse collar's signed parameter detects the actual frontier. -/
theorem actualCollarDiffeomorph_inverse_parameter_zero_iff (x : actualCollarNeighborhood) :
    ((actualCollarDiffeomorph.symm x).2 : ℝ) = 0 ↔
      (x : Threefold.Space) ∈ frontier closedDiskNeighborhood := by
  rw [← actualMap_mem_frontier_closedDiskNeighborhood_iff]
  change (actualCollarDiffeomorph (actualCollarDiffeomorph.symm x) : Threefold.Space) ∈
    frontier closedDiskNeighborhood ↔ _
  rw [actualCollarDiffeomorph.apply_symm_apply]

/-- The inverse collar's negative parameter detects the actual ambient interior. -/
theorem actualCollarDiffeomorph_inverse_parameter_neg_iff (x : actualCollarNeighborhood) :
    ((actualCollarDiffeomorph.symm x).2 : ℝ) < 0 ↔
      (x : Threefold.Space) ∈ interior closedDiskNeighborhood := by
  rw [← actualMap_mem_interior_closedDiskNeighborhood_iff]
  change (actualCollarDiffeomorph (actualCollarDiffeomorph.symm x) : Threefold.Space) ∈
    interior closedDiskNeighborhood ↔ _
  rw [actualCollarDiffeomorph.apply_symm_apply]

/-- The inverse collar's positive parameter detects the actual exterior of the compact image. -/
theorem actualCollarDiffeomorph_inverse_parameter_pos_iff (x : actualCollarNeighborhood) :
    0 < ((actualCollarDiffeomorph.symm x).2 : ℝ) ↔
      (x : Threefold.Space) ∉ closedDiskNeighborhood := by
  rw [← actualMap_not_mem_closedDiskNeighborhood_iff]
  change (actualCollarDiffeomorph (actualCollarDiffeomorph.symm x) : Threefold.Space) ∉
    closedDiskNeighborhood ↔ _
  rw [actualCollarDiffeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar
