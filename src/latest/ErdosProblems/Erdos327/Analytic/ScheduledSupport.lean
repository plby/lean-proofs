import ErdosProblems.Erdos327.Analytic.ScheduledResidualBounds

/-!
# Exact support of the scheduled dyadic sums

The coordinate identities force the residual variable to lie below a
quotient of `N` by the square of the dyadic scale.  This file records that
the scheduled upper bounds themselves vanish when that quotient is zero.
-/

namespace Erdos327.Analytic

noncomputable section

/-- A source scheduled summand vanishes once its residual quotient is zero. -/
theorem sourceScheduledBlockBound_eq_zero_of_residual_eq_zero
    {L N j : ℕ} {A K : ℝ}
    (hzero : 2 * N / dyadicScale j ^ 2 = 0) :
    sourceScheduledBlockBound L N A K j = 0 := by
  have hnot : ¬sourceScheduledGoodIndex L N j := by
    intro hj
    rcases hj with ⟨_hz, _hLX, hY⟩
    omega
  rw [sourceScheduledBlockBound, if_neg hnot]
  unfold sourceScheduledFallbackBlockBound
  rw [hzero, sourceDyadicResidualMoment_zero]
  ring

/-- The refined source summand has the same exact terminal support. -/
theorem sourceRefinedScheduledBlockBound_eq_zero_of_residual_eq_zero
    {L N j : ℕ} {A K : ℝ}
    (hzero : 2 * N / dyadicScale j ^ 2 = 0) :
    sourceRefinedScheduledBlockBound L N A K j = 0 := by
  unfold sourceRefinedScheduledBlockBound
  split_ifs
  · rfl
  · exact sourceScheduledBlockBound_eq_zero_of_residual_eq_zero hzero

/-- A convenient strict-square criterion for the terminal source range. -/
theorem sourceRefinedScheduledBlockBound_eq_zero_of_two_mul_lt_sq
    {L N j : ℕ} {A K : ℝ}
    (hterminal : 2 * N < dyadicScale j ^ 2) :
    sourceRefinedScheduledBlockBound L N A K j = 0 := by
  apply sourceRefinedScheduledBlockBound_eq_zero_of_residual_eq_zero
  exact Nat.div_eq_of_lt hterminal

/-- A mixed scheduled summand vanishes at residual quotient zero, once the
only potentially literal-cardinality block is known to be empty. -/
theorem mixedRefinedScheduledBlockBound_eq_zero_of_residual_eq_zero
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 17 ≤ L)
    (hzero : N / (dyadicScale j * dyadicScale j) = 0) :
    mixedRefinedScheduledBlockBound
      L N Ab Kb Ao Ko qb qo j = 0 := by
  unfold mixedRefinedScheduledBlockBound
  by_cases hfar : 16 * dyadicScale j < L
  · rw [if_pos hfar]
  · rw [if_neg hfar]
    have hnotGood : ¬mixedScheduledGoodIndex L N j := by
      intro hj
      rcases hj with ⟨_hz, _hLX, _hzX, hY⟩
      omega
    rw [mixedScheduledBlockBound, if_neg hnotGood]
    unfold mixedScheduledFallbackBlockBound
    by_cases havailable : mixedScheduledResidualAvailable L j
    · rw [if_pos havailable]
      unfold mixedScheduledExactResidualBlockBound
      rw [mixedExactResidualMoment_eq_zero_of_div_eq_zero hzero]
      ring
    · rw [if_neg havailable]
      unfold mixedScheduledExactCardBlockBound
      rw [mixedCoordinateBoxBlock_eq_empty_of_not_residualAvailable
        hL havailable]
      simp

/-- A convenient strict-square criterion for the terminal mixed range. -/
theorem mixedRefinedScheduledBlockBound_eq_zero_of_lt_sq
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 17 ≤ L)
    (hterminal : N < dyadicScale j * dyadicScale j) :
    mixedRefinedScheduledBlockBound
      L N Ab Kb Ao Ko qb qo j = 0 := by
  apply mixedRefinedScheduledBlockBound_eq_zero_of_residual_eq_zero hL
  exact Nat.div_eq_of_lt hterminal

end

end Erdos327.Analytic
