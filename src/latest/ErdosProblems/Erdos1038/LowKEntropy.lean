import ErdosProblems.Erdos1038.LowKArithmetic

/-!
# Entropy calibration in the elementary range

This file proves the analytic inequality `t * log (a/t) ≤ a/e` from the
elementary tangent bound for `log`, combines it with the certified rational
constants in `LowKArithmetic.lean`, and packages the final implication
that the residual-radius sum is strictly larger than `1/3`.
-/

namespace Erdos1038

noncomputable section

theorem mul_log_div_le_div_exp_one {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t * Real.log (a / t) ≤ a / Real.exp 1 := by
  let y : ℝ := a / (t * Real.exp 1)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hlogy := Real.log_le_sub_one_of_pos hy
  have hfactor : a / t = y * Real.exp 1 := by
    dsimp [y]
    field_simp [ht.ne', he.ne']
  have hlogfactor : Real.log (a / t) = Real.log y + 1 := by
    rw [hfactor, Real.log_mul hy.ne' he.ne', Real.log_exp]
  have hmain : Real.log (a / t) ≤ a / (t * Real.exp 1) := by
    rw [hlogfactor]
    dsimp [y] at hlogy
    linarith
  calc
    t * Real.log (a / t) ≤ t * (a / (t * Real.exp 1)) :=
      mul_le_mul_of_nonneg_left hmain ht.le
    _ = a / Real.exp 1 := by field_simp [ht.ne', he.ne']

theorem entropy_term_lt_nine_div_hundred {ε t : ℝ}
    (hε : 0 < ε) (hεmax : ε < 1 / 25) (ht : 0 < t) :
    t * Real.log (6 * ε / t) < 9 / 100 := by
  have ha : 0 < 6 * ε := mul_pos (by norm_num) hε
  have hentropy := mul_log_div_le_div_exp_one ha ht
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have heLower := exp_one_gt_eight_div_three
  have hratio : (6 * ε) / Real.exp 1 < 9 / 100 := by
    rw [div_lt_iff₀ he]
    have hmul : (9 / 100 : ℝ) * (8 / 3) <
        (9 / 100 : ℝ) * Real.exp 1 :=
      mul_lt_mul_of_pos_left heLower (by norm_num)
    norm_num at hmul ⊢
    linarith
  exact hentropy.trans_lt hratio

theorem lowK_log_margin {k : ℝ} (hk : k ≤ 29 / 20) :
    9 / 100 < Real.log 3 - k * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : k * Real.log 2 ≤ (29 / 20 : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hk hlog2.le
  linarith [log_three_sub_29_div_20_mul_log_two_gt_nine_div_hundred]

theorem lowK_calibration_positive {k ε t : ℝ}
    (hk : k ≤ 29 / 20) (hε : 0 < ε) (hεmax : ε < 1 / 25)
    (ht : 0 ≤ t) :
    0 < Real.log 3 - k * Real.log 2 - t * Real.log (6 * ε / t) := by
  rcases ht.eq_or_lt with rfl | htpos
  · linarith [lowK_log_margin hk]
  · have hent := entropy_term_lt_nine_div_hundred hε hεmax htpos
    linarith [lowK_log_margin hk]

theorem radius_sum_gt_one_third_of_calibration
    {k ε t S : ℝ} (hQ : 0 < 1 - t) (hS : 0 < S)
    (hk : k ≤ 29 / 20) (hε : 0 < ε) (hεmax : ε < 1 / 25)
    (ht : 0 ≤ t)
    (hcal : Real.log 3 - k * Real.log 2 -
        t * Real.log (6 * ε / t) ≤ (1 - t) * Real.log (3 * S)) :
    1 / 3 < S := by
  have hpositive := lowK_calibration_positive hk hε hεmax ht
  have hlog : 0 < Real.log (3 * S) := by
    nlinarith
  have hone : 1 < 3 * S :=
    (Real.log_pos_iff (mul_nonneg (by norm_num) hS.le)).mp hlog
  linarith

/-- The endpoint window and a residual-radius sum above `1/3` together
give a total lower bound strictly above `2`. -/
theorem sqrt_two_add_twice_gt_two {S : ℝ} (hS : 1 / 3 < S) :
    2 < Real.sqrt 2 + 2 * S := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (4 / 3 : ℝ) < Real.sqrt 2 := by
    nlinarith
  linarith

end

end Erdos1038
