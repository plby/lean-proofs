import ErdosProblems.Erdos1148.ReturningCoverHeightBound

/-! # Short segments can be covered ordinarily at a controlled height cost -/

namespace Erdos1148.DukeArithmetic

theorem exp_le_ten_height_mul_exp_half {Y T : ℝ} (hY : 0 < Y)
    (hshort : ¬96 * Real.exp (-T) ≤ (Y ^ 2)⁻¹) :
    Real.exp T ≤ 10 * Y * Real.exp (T / 2) := by
  have hinv : 1 / Y ^ 2 < 96 / Real.exp T := by
    simpa only [one_div, Real.exp_neg, div_eq_mul_inv, one_mul] using lt_of_not_ge hshort
  have hexp : Real.exp T < 96 * Y ^ 2 := by
    simpa only [one_mul] using (div_lt_div_iff₀ (sq_pos_of_pos hY) (Real.exp_pos T)).mp hinv
  have hsquare : Real.exp (T / 2) ^ 2 = Real.exp T := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num <;> ring
  have hhalf : Real.exp (T / 2) ≤ 10 * Y := by
    nlinarith [Real.exp_pos (T / 2)]
  calc
    _ = Real.exp (T / 2) * Real.exp (T / 2) := by rw [← pow_two, hsquare]
    _ ≤ _ := mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le

end Erdos1148.DukeArithmetic
