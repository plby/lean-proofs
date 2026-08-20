import ErdosProblems.Erdos746.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter
open scoped Topology

namespace Erdos746

/-! Limits for the explicit error terms in equations (10) and (12) of the
mathematical proof.  They are stated separately so that the probabilistic
estimates can use them without repeating analytic arguments. -/

/-- The square of `log n` is negligible compared with `n`. -/
lemma tendsto_log_sq_div_nat :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Real.rpow_one] using
    tendsto_log_pow_div_rpow_nat 2 (a := 1) one_pos

/-- The first Range-I ratio in its multiplicative, negative-power form:
`A (log n)^2 n^(-δ/2) → 0`. -/
lemma tendsto_mul_log_sq_mul_rpow_neg (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦
      A * Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-(δ / 2)))
      atTop (nhds 0) := by
  refine (tendsto_baseRatio_zero A hδ).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [baseRatio, div_eq_mul_inv]
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

/-- Abstract form of the geometric-series passage `a_n → 0` implies
`a_n/(1-a_n) → 0`. -/
lemma tendsto_geometric_ratio_zero {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (fun n ↦ a n / (1 - a n)) atTop (nhds 0) := by
  have hden : Tendsto (fun n : ℕ ↦ 1 - a n) atTop (nhds ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub ha
  have h := ha.div hden (show (1 : ℝ) - 0 ≠ 0 by norm_num)
  have hc : Tendsto (fun n ↦ a n / (1 - a n)) atTop
      (nhds (0 / ((1 : ℝ) - 0))) := by
    refine h.congr' ?_
    filter_upwards [] with n
    rfl
  simpa using hc

/-- The Range-II exponential term `n exp(-b n/log n)` vanishes. -/
lemma tendsto_range_two_error_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp (-b * (n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) :=
  tendsto_nat_mul_exp_neg_nat_div_log hb

/-- The linear exponential term `n exp(-d n)` from Range III vanishes. -/
lemma tendsto_linear_error_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp (-d * (n : ℝ))) atTop (nhds 0) :=
  tendsto_nat_mul_exp_neg_mul_nat hd

/-- The edge-count Chernoff term `exp(-d n log n)` in (10) vanishes. -/
lemma tendsto_chernoff_error_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦
      Real.exp (-d * (n : ℝ) * Real.log (n : ℝ)))
      atTop (nhds 0) :=
  tendsto_exp_neg_mul_nat_log hd

/-- The large-set union-bound error from (9):
`n exp(2 n log 2 - c n log n/16) → 0`. -/
lemma tendsto_large_set_error_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp
        (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16))
      atTop (nhds 0) := by
  have h := tendsto_nat_mul_exp_linear_sub_mul_nat_log
    (2 * Real.log 2) (c := c / 16) (by positivity)
  convert h using 1
  funext n
  congr 2
  ring

/-- The adaptive sprinkling error in (12):
`exp(n-1-d n log n) → 0`. -/
lemma tendsto_adaptive_error_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦
      Real.exp ((n : ℝ) - 1 - d * (n : ℝ) * Real.log (n : ℝ)))
      atTop (nhds 0) :=
  tendsto_exp_nat_sub_one_sub_mul_nat_log hd

/-- The full explicit base-exposure error displayed in equation (10). -/
noncomputable def baseFailureError (A δ c : ℝ) (n : ℕ) : ℝ :=
  geometricError A δ n +
    (n : ℝ) * Real.exp (-(c / 8) * (n : ℝ) / Real.log (n : ℝ)) +
    (n : ℝ) * Real.exp (-((7 / 10 : ℝ) - Real.log 2) * (n : ℝ)) +
    (n : ℝ) * Real.exp
      (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16) +
    Real.exp (-(δ ^ 2 / (4 * (1 + 4 * δ / 3))) *
      (n : ℝ) * Real.log (n : ℝ))

/-- Every summand of (10), and hence their displayed sum, tends to zero. -/
lemma tendsto_baseFailureError_zero (A : ℝ) {δ c : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (baseFailureError A δ c) atTop (nhds 0) := by
  have hgeom := tendsto_geometricError_zero A hδ
  have hrange2 := tendsto_range_two_error_zero (b := c / 8) (by positivity)
  have hlinear : 0 < (7 / 10 : ℝ) - Real.log 2 := by
    linarith [Real.log_two_lt_d9]
  have hrange3 := tendsto_linear_error_zero hlinear
  have hlarge := tendsto_large_set_error_zero hc
  have hchernoffCoeff :
      0 < δ ^ 2 / (4 * (1 + 4 * δ / 3)) := by positivity
  have hchernoff := tendsto_chernoff_error_zero hchernoffCoeff
  have hsum := (((hgeom.add hrange2).add hrange3).add hlarge).add hchernoff
  have hsum0 := hsum
  simp only [add_zero] at hsum0
  refine hsum0.congr' ?_
  filter_upwards [] with n
  rfl

/-- Equation (12) with its actual coefficient
`(1-exp(-1))ρ/48`. -/
lemma tendsto_sprinkling_error_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) - 1 -
      ((1 - Real.exp (-1)) * ρ / 48) *
        (n : ℝ) * Real.log (n : ℝ))) atTop (nhds 0) := by
  have hexp : Real.exp (-1) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
  have hcoeff : 0 < (1 - Real.exp (-1)) * ρ / 48 := by positivity
  exact tendsto_adaptive_error_zero hcoeff

end Erdos746
