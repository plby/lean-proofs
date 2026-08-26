import Mathlib

/-!
# Exact arithmetic for the elementary (`1 ≤ k ≤ 29 / 20`) range

This file certifies the numerical inequalities used in the proof of the
``Small endpoint-to-residual ratio'' proposition.  The transcendental
inequalities are consequences of Mathlib's rigorous finite-series bounds;
all remaining comparisons are exact rational arithmetic.
-/

open scoped Nat
open Finset Set

namespace Erdos1038

noncomputable section

/-- The four-term positive Taylor polynomial at `3 / 8` is strictly below
`exp (3 / 8)`. -/
theorem exp_three_eighths_gt_1489_div_1024 :
    (1489 / 1024 : ℝ) < Real.exp (3 / 8 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 / 8 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- The exact rational comparison following the exponential estimate. -/
theorem twenty_nine_div_twenty_lt_1489_div_1024 :
    (29 / 20 : ℝ) < 1489 / 1024 := by
  norm_num

/-- The exponential comparison used to bound `log (29 / 20)`. -/
theorem twenty_nine_div_twenty_lt_exp_three_eighths :
    (29 / 20 : ℝ) < Real.exp (3 / 8 : ℝ) :=
  twenty_nine_div_twenty_lt_1489_div_1024.trans
    exp_three_eighths_gt_1489_div_1024

/-- The complete exponential/rational chain, in the orientation displayed
in the manuscript. -/
theorem exp_three_eighths_rational_chain :
    (29 / 20 : ℝ) < 1489 / 1024 ∧
      (1489 / 1024 : ℝ) < Real.exp (3 / 8 : ℝ) :=
  ⟨twenty_nine_div_twenty_lt_1489_div_1024,
    exp_three_eighths_gt_1489_div_1024⟩

/-- Consequently, `log (29 / 20) < 3 / 8`. -/
theorem log_twenty_nine_div_twenty_lt_three_eighths :
    Real.log (29 / 20 : ℝ) < 3 / 8 := by
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 29 / 20)).2
    twenty_nine_div_twenty_lt_exp_three_eighths

/-- The alternating cubic Taylor polynomial is a strict lower bound for
`exp (-z)` when `z > 0`.  This is the sign-sensitive Taylor estimate used
in the manuscript. -/
theorem exp_neg_gt_taylor_three {z : ℝ} (hz : 0 < z) :
    1 - z + z ^ 2 / 2 - z ^ 3 / 6 < Real.exp (-z) := by
  let f : ℝ → ℝ := fun x => Real.exp ((-1 : ℝ) * x)
  have hf : ContDiff ℝ ⊤ f := by
    fun_prop
  have hwithin (m : ℕ) :
      iteratedDerivWithin m f (Set.Icc 0 z) 0 = iteratedDeriv m f 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hz)
      (hf.contDiffAt.of_le le_top) (by exact ⟨le_rfl, hz.le⟩)
  have hiter (m : ℕ) (x : ℝ) :
      iteratedDeriv m f x = (-1 : ℝ) ^ m * Real.exp ((-1 : ℝ) * x) := by
    change iteratedDeriv m (fun s : ℝ => Real.exp ((-1 : ℝ) * s)) x = _
    rw [iteratedDeriv_exp_const_mul]
  have htaylor :
      taylorWithinEval f 3 (Set.Icc 0 z) 0 z =
        1 - z + z ^ 2 / 2 - z ^ 3 / 6 := by
    rw [taylor_within_apply]
    simp_rw [hwithin]
    simp_rw [hiter]
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  obtain ⟨c, hc, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := f) (x₀ := 0) (x := z) (n := 3) (ne_of_lt hz)
        (hf.contDiffOn.of_le (by simp))
  have hderiv : iteratedDeriv 4 f c = Real.exp (-c) := by
    rw [hiter]
    norm_num
  have hrem_pos :
      0 < iteratedDeriv 4 f c * (z - 0) ^ 4 / (4 ! : ℕ) := by
    rw [hderiv]
    have hzpow : 0 < (z - 0) ^ 4 := by simpa using! pow_pos hz 4
    exact div_pos (mul_pos (Real.exp_pos _) hzpow) (by norm_num)
  rw [Set.uIcc_of_le hz.le, htaylor] at hrem
  have : 0 < f z - (1 - z + z ^ 2 / 2 - z ^ 3 / 6) := by
    rw [hrem]
    exact hrem_pos
  simpa [f] using! sub_pos.mp this

/-- The Taylor lower bound at the exact value `z = 87 / 392`. -/
theorem exp_neg_87_div_392_gt_taylor_three :
    1 - (87 / 392 : ℝ) + (87 / 392 : ℝ) ^ 2 / 2 -
        (87 / 392 : ℝ) ^ 3 / 6 < Real.exp (-(87 / 392 : ℝ)) := by
  exact exp_neg_gt_taylor_three (by norm_num)

/-- The exponent `z` used in the endpoint calculation. -/
theorem eighty_seven_div_392_eq_29_div_49_mul_three_eighths :
    (87 / 392 : ℝ) = (29 / 49 : ℝ) * (3 / 8 : ℝ) := by
  norm_num

/-- The exact rational subtraction in the endpoint estimate. -/
theorem endpoint_taylor_rational_identity :
    (49 / 20 : ℝ) *
          (1 - 87 / 392 + (87 / 392) ^ 2 / 2 - (87 / 392) ^ 3 / 6) -
        49 / 25 =
      522631 / 245862400 := by
  norm_num

/-- Positivity of the exact rational remainder displayed in the proof. -/
theorem endpoint_taylor_exact_remainder_pos :
    (0 : ℝ) < 522631 / 245862400 := by
  norm_num

/-- In particular, the rational Taylor margin is positive. -/
theorem endpoint_taylor_rational_margin :
    0 < (49 / 20 : ℝ) *
          (1 - 87 / 392 + (87 / 392) ^ 2 / 2 - (87 / 392) ^ 3 / 6) -
        49 / 25 := by
  rw [endpoint_taylor_rational_identity]
  exact endpoint_taylor_exact_remainder_pos

/-- Combining the Taylor estimate and the exact subtraction gives the
strict exponential endpoint inequality. -/
theorem endpoint_exp_margin_gt_exact_remainder :
    (522631 / 245862400 : ℝ) <
      (49 / 20 : ℝ) * Real.exp (-(87 / 392 : ℝ)) - 49 / 25 := by
  have h := mul_lt_mul_of_pos_left exp_neg_87_div_392_gt_taylor_three
    (by norm_num : (0 : ℝ) < 49 / 20)
  rw [← endpoint_taylor_rational_identity]
  linarith

/-- The endpoint inequality in the form used to bound `epsilon_K`. -/
theorem forty_nine_div_twenty_mul_exp_neg_z_gt_49_div_25 :
    (49 / 25 : ℝ) <
      (49 / 20 : ℝ) * Real.exp (-(87 / 392 : ℝ)) := by
  linarith [endpoint_taylor_exact_remainder_pos,
    endpoint_exp_margin_gt_exact_remainder]

/-- Replacing `3/8` by the strict logarithm bound makes the exponent larger. -/
theorem exp_neg_29_div_49_mul_log_ratio_gt_exp_neg_z :
    Real.exp (-(87 / 392 : ℝ)) <
      Real.exp (-(29 / 49 : ℝ) * Real.log (29 / 20 : ℝ)) := by
  apply Real.exp_strictMono
  rw [eighty_seven_div_392_eq_29_div_49_mul_three_eighths]
  nlinarith [log_twenty_nine_div_twenty_lt_three_eighths]

/-- The exact `K = 29/20` endpoint power bound from the manuscript. -/
theorem lowK_endpoint_rpow_product_gt_49_div_25 :
    (49 / 25 : ℝ) <
      (49 / 20 : ℝ) * (29 / 20 : ℝ) ^ (-(29 / 49 : ℝ)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 29 / 20)]
  have h := mul_lt_mul_of_pos_left
    exp_neg_29_div_49_mul_log_ratio_gt_exp_neg_z
    (by norm_num : (0 : ℝ) < 49 / 20)
  have hbase := forty_nine_div_twenty_mul_exp_neg_z_gt_49_div_25
  rw [mul_comm (Real.log (29 / 20 : ℝ)) (-(29 / 49 : ℝ))]
  exact hbase.trans h

/-- Equivalently, the numerical endpoint deficit is below `1/25`. -/
theorem lowK_endpoint_deficit_lt_one_div_25 :
    2 - (49 / 20 : ℝ) * (29 / 20 : ℝ) ^ (-(29 / 49 : ℝ)) < 1 / 25 := by
  linarith [lowK_endpoint_rpow_product_gt_49_div_25]

/-- A rigorous lower bound for `log 3`, obtained from four terms of the
`log ((1+x)/(1-x))` series at `x = 1/2`. -/
theorem log_three_gt_263_div_240 :
    (263 / 240 : ℝ) < Real.log 3 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- A rigorous upper bound for `log 2`, obtained from five terms and the
explicit tail estimate for the `log ((1+x)/(1-x))` series at `x = 1/3`. -/
theorem log_two_lt_1123_div_1620 :
    Real.log 2 < (1123 / 1620 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- The exact lower margin left after inserting the two logarithm bounds. -/
theorem log_three_sub_29_div_20_mul_log_two_gt_1469_div_16200 :
    (1469 / 16200 : ℝ) <
      Real.log 3 - (29 / 20 : ℝ) * Real.log 2 := by
  nlinarith [log_three_gt_263_div_240, log_two_lt_1123_div_1620]

/-- The rational logarithmic margin is itself larger than `9/100`. -/
theorem nine_div_hundred_lt_1469_div_16200 :
    (9 / 100 : ℝ) < 1469 / 16200 := by
  norm_num

/-- The convenient rounded form of the logarithmic margin. -/
theorem log_three_sub_29_div_20_mul_log_two_gt_nine_div_hundred :
    (9 / 100 : ℝ) <
      Real.log 3 - (29 / 20 : ℝ) * Real.log 2 :=
  nine_div_hundred_lt_1469_div_16200.trans
    log_three_sub_29_div_20_mul_log_two_gt_1469_div_16200

/-- The elementary lower bound `e > 8/3`. -/
theorem exp_one_gt_eight_div_three :
    (8 / 3 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

end

end Erdos1038
