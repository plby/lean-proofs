import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardNeighborhood
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryFrontier

/-!
# The actual closed-neighborhood sides in standard radial coordinates

The original closed disk neighborhood, its ambient interior, and its ambient
frontier pull back to the closed, open, and exact half-unit radius conditions
in the genuine standard-product chart of the original threefold.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace

/-- The physical normal radius is the positive scale times the standard Euclidean norm. -/
theorem standardUnitToNormal_radiusSq (p : StandardOpenNormalProduct) :
    radiusSq (standardUnitToNormalDiffeomorph p).val.2 =
      (injectiveRadius * ‖(p.2 : RealFour.Space)‖) ^ 2 := by
  rw [standardUnitToNormalDiffeomorph_coe]
  change radiusSq
    (RealFour.coordinateEquiv.symm (injectiveRadius • (p.2 : RealFour.Space))) = _
  rw [RealFour.coordinateEquiv_symm_radiusSq, norm_smul,
    Real.norm_of_nonneg injectiveRadius_pos.le]

/-- The actual closed disk image is exactly the standard closed half-unit disk. -/
theorem standardNeighborhoodDiffeomorph_mem_closedDiskNeighborhood_iff
    (p : StandardOpenNormalProduct) :
    (standardNeighborhoodDiffeomorph p : Threefold.Space) ∈ closedDiskNeighborhood ↔
      ‖(p.2 : RealFour.Space)‖ ≤ (1 / 2 : ℝ) := by
  rw [standardNeighborhoodDiffeomorph_coe, roundProductMap_mem_closedDiskNeighborhood_iff,
    standardUnitToNormal_radiusSq,
    sq_le_sq₀ (mul_nonneg injectiveRadius_pos.le (norm_nonneg _)) closedRadius_pos.le]
  simpa only [closedRadius, mul_one_div] using
    (mul_le_mul_iff_right₀ injectiveRadius_pos :
      injectiveRadius * ‖(p.2 : RealFour.Space)‖ ≤ injectiveRadius * (1 / 2 : ℝ) ↔
        ‖(p.2 : RealFour.Space)‖ ≤ (1 / 2 : ℝ))

/-- The ambient interior in the actual threefold is the strict half-unit radius condition. -/
theorem standardNeighborhoodDiffeomorph_mem_interior_closedDiskNeighborhood_iff
    (p : StandardOpenNormalProduct) :
    (standardNeighborhoodDiffeomorph p : Threefold.Space) ∈ interior closedDiskNeighborhood ↔
      ‖(p.2 : RealFour.Space)‖ < (1 / 2 : ℝ) := by
  rw [standardNeighborhoodDiffeomorph_coe,
    roundProductMap_mem_interior_closedDiskNeighborhood_iff, standardUnitToNormal_radiusSq,
    sq_lt_sq₀ (mul_nonneg injectiveRadius_pos.le (norm_nonneg _)) closedRadius_pos.le]
  simpa only [closedRadius, mul_one_div] using
    (mul_lt_mul_iff_right₀ injectiveRadius_pos :
      injectiveRadius * ‖(p.2 : RealFour.Space)‖ < injectiveRadius * (1 / 2 : ℝ) ↔
        ‖(p.2 : RealFour.Space)‖ < (1 / 2 : ℝ))

/-- The literal ambient frontier is the standard half-unit radius level. -/
theorem standardNeighborhoodDiffeomorph_mem_frontier_closedDiskNeighborhood_iff
    (p : StandardOpenNormalProduct) :
    (standardNeighborhoodDiffeomorph p : Threefold.Space) ∈ frontier closedDiskNeighborhood ↔
      ‖(p.2 : RealFour.Space)‖ = (1 / 2 : ℝ) := by
  rw [standardNeighborhoodDiffeomorph_coe,
    roundProductMap_mem_frontier_closedDiskNeighborhood_iff, standardUnitToNormal_radiusSq,
    sq_eq_sq₀ (mul_nonneg injectiveRadius_pos.le (norm_nonneg _)) closedRadius_pos.le]
  constructor
  · intro h
    apply mul_left_cancel₀ injectiveRadius_pos.ne'
    simpa only [closedRadius, mul_one_div] using h
  · intro h
    simpa only [closedRadius, mul_one_div] using congrArg (injectiveRadius * ·) h

/-- The actual exterior, within the native open chart, is the greater-than-half radius side. -/
theorem standardNeighborhoodDiffeomorph_not_mem_closedDiskNeighborhood_iff
    (p : StandardOpenNormalProduct) :
    (standardNeighborhoodDiffeomorph p : Threefold.Space) ∉ closedDiskNeighborhood ↔
      (1 / 2 : ℝ) < ‖(p.2 : RealFour.Space)‖ := by
  rw [standardNeighborhoodDiffeomorph_mem_closedDiskNeighborhood_iff, not_le]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar
