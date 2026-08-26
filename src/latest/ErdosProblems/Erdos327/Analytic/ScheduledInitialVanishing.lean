import ErdosProblems.Erdos327.Analytic.SourceSmallBlocks
import ErdosProblems.Erdos327.Analytic.MixedSmallBlocks

/-!
# Exact disappearance of fixed scheduled prefixes

For a fixed number of dyadic indices, increasing the roughness cutoff
eventually puts every corresponding source or mixed box below the
roughness support.  Thus the refined scheduled prefix is literally zero,
uniformly in `N` and in all regularity parameters.
-/

namespace Erdos327.Analytic

open Filter Finset

noncomputable section

theorem dyadicScale_mono {i j : ℕ} (hij : i ≤ j) :
    dyadicScale i ≤ dyadicScale j := by
  unfold dyadicScale
  exact Nat.pow_le_pow_right (by norm_num) hij

theorem sourceRefinedScheduledBlockBound_eq_zero_of_le
    {L N i j : ℕ} {A K : ℝ}
    (hij : i ≤ j) (hfar : 8 * dyadicScale j < L) :
    sourceRefinedScheduledBlockBound L N A K i = 0 := by
  rw [sourceRefinedScheduledBlockBound, if_pos]
  exact (Nat.mul_le_mul_left 8 (dyadicScale_mono hij)).trans_lt hfar

theorem mixedRefinedScheduledBlockBound_eq_zero_of_le
    {L N i j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hij : i ≤ j) (hfar : 16 * dyadicScale j < L) :
    mixedRefinedScheduledBlockBound
        L N Ab Kb Ao Ko qb qo i = 0 := by
  rw [mixedRefinedScheduledBlockBound, if_pos]
  exact (Nat.mul_le_mul_left 16 (dyadicScale_mono hij)).trans_lt hfar

/-- A fixed source prefix vanishes once its largest reference scale is
below `L/8`. -/
theorem sum_sourceRefinedScheduledBlockBound_range_eq_zero
    {L N J : ℕ} {A K : ℝ}
    (hfar : 8 * dyadicScale J < L) :
    (∑ j ∈ range J,
      sourceRefinedScheduledBlockBound L N A K j) = 0 := by
  apply sum_eq_zero
  intro j hj
  exact sourceRefinedScheduledBlockBound_eq_zero_of_le
    (Nat.le_of_lt (mem_range.mp hj)) hfar

/-- A fixed mixed prefix vanishes once its largest reference scale is
below `L/16`. -/
theorem sum_mixedRefinedScheduledBlockBound_range_eq_zero
    {L N J : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hfar : 16 * dyadicScale J < L) :
    (∑ j ∈ range J,
      mixedRefinedScheduledBlockBound
        L N Ab Kb Ao Ko qb qo j) = 0 := by
  apply sum_eq_zero
  intro j hj
  exact mixedRefinedScheduledBlockBound_eq_zero_of_le
    (Nat.le_of_lt (mem_range.mp hj)) hfar

/-- Uniform eventual form of the fixed source-prefix disappearance. -/
theorem eventually_sourceRefinedScheduled_prefix_eq_zero
    (N J : ℕ) (A K : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      (∑ j ∈ range J,
        sourceRefinedScheduledBlockBound L N A K j) = 0 := by
  filter_upwards
    [eventually_gt_atTop (8 * dyadicScale J)] with L hL
  exact sum_sourceRefinedScheduledBlockBound_range_eq_zero hL

/-- Uniform eventual form of the fixed mixed-prefix disappearance. -/
theorem eventually_mixedRefinedScheduled_prefix_eq_zero
    (N J : ℕ) (Ab Kb Ao Ko qb qo : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      (∑ j ∈ range J,
        mixedRefinedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j) = 0 := by
  filter_upwards
    [eventually_gt_atTop (16 * dyadicScale J)] with L hL
  exact sum_mixedRefinedScheduledBlockBound_range_eq_zero hL

end

end Erdos327.Analytic
