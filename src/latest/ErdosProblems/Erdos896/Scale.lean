/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The logarithmic scale in Erdős Problem 896

This file isolates elementary analytic facts about the slowly varying
denominator

`(log x)^δ * (log (log x))^(3/2)`.

The module is deliberately independent of the main problem file, while its
public names live in `Erdos896`; the main file can import it without creating
an import cycle.
-/

open Filter Asymptotics

namespace Erdos896

/-- The Erdős--Tenenbaum--Ford exponent. -/
noncomputable def delta896 : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- The slowly varying denominator in the multiplication-table estimate,
on a real argument. -/
noncomputable def logDenom896R (x : ℝ) : ℝ :=
  (Real.log x) ^ delta896 *
    (Real.log (Real.log x)) ^ (3 / 2 : ℝ)

/-- The slowly varying denominator on natural arguments. -/
noncomputable def logDenom896 (N : ℕ) : ℝ :=
  logDenom896R N

/-- The full Ford scale on natural arguments. -/
noncomputable def scale896 (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 : ℕ) / logDenom896 N

theorem delta896_pos : 0 < delta896 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hloglog : Real.log (Real.log 2) < Real.log 2 - 1 :=
    Real.log_lt_sub_one_of_pos hlog2 (by
      linarith [Real.log_two_lt_d9])
  have hquot : (1 + Real.log (Real.log 2)) / Real.log 2 < 1 :=
    (div_lt_one hlog2).2 (by linarith)
  unfold delta896
  linarith

theorem delta896_lt_one : delta896 < 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : Real.exp (-1) < Real.log 2 :=
    Real.exp_neg_one_lt_half.trans (by
      linarith [Real.log_two_gt_d9])
  have hloglog : -1 < Real.log (Real.log 2) := by
    rw [← Real.exp_lt_exp]
    simpa [Real.exp_log hlog2] using hexp
  have hquot : 0 < (1 + Real.log (Real.log 2)) / Real.log 2 :=
    div_pos (by linarith) hlog2
  unfold delta896
  linarith

theorem delta896_nonneg : 0 ≤ delta896 := delta896_pos.le

theorem delta896_le_one : delta896 ≤ 1 := delta896_lt_one.le

/-- Positivity of the slowly varying denominator on its natural domain. -/
theorem logDenom896R_pos {x : ℝ} (hx : Real.exp 1 < x) :
    0 < logDenom896R x := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans hx
  have hlogx : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]
    simpa using hx
  exact mul_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans hlogx) _)
    (Real.rpow_pos_of_pos (Real.log_pos hlogx) _)

theorem logDenom896_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < logDenom896 N := by
  apply logDenom896R_pos
  exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hN)

theorem scale896_pos {N : ℕ} (hN : 3 ≤ N) : 0 < scale896 N := by
  exact div_pos (pow_pos (by positivity : (0 : ℝ) < N) _)
    (logDenom896_pos hN)

theorem eventually_logDenom896_pos :
    ∀ᶠ N : ℕ in atTop, 0 < logDenom896 N := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  exact logDenom896_pos hN

theorem eventually_scale896_pos :
    ∀ᶠ N : ℕ in atTop, 0 < scale896 N := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  exact scale896_pos hN

/-- The logarithmic denominator is monotone once both iterated logarithms
are nonnegative. -/
theorem logDenom896R_mono {x y : ℝ}
    (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    logDenom896R x ≤ logDenom896R y := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hx1 : 1 ≤ x :=
    (by linarith [Real.exp_one_gt_two] : (1 : ℝ) ≤ Real.exp 1).trans hx
  have hy1 : 1 ≤ y := hx1.trans hxy
  have hlogx1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 hx
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hx0)
      (Set.mem_Ioi.mpr hy0) hxy
  have hloglogxy : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (zero_lt_one.trans_le hlogx1))
      (Set.mem_Ioi.mpr (zero_lt_one.trans_le (hlogx1.trans hlogxy))) hlogxy
  unfold logDenom896R
  exact mul_le_mul
    (Real.rpow_le_rpow (Real.log_nonneg hx1) hlogxy delta896_nonneg)
    (Real.rpow_le_rpow (Real.log_nonneg hlogx1)
      hloglogxy (by norm_num : (0 : ℝ) ≤ 3 / 2))
    (Real.rpow_nonneg (Real.log_nonneg hlogx1) _)
    (Real.rpow_nonneg (Real.log_nonneg hy1) _)

theorem logDenom896_mono {m N : ℕ} (hm : 3 ≤ m) (hmN : m ≤ N) :
    logDenom896 m ≤ logDenom896 N := by
  apply logDenom896R_mono
  · exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hm)
  · exact_mod_cast hmN

theorem logDenom896_le_sq (N : ℕ) (hN : 3 ≤ N) :
    logDenom896 N ≤ logDenom896 (N ^ 2) := by
  apply logDenom896_mono hN
  nlinarith

private lemma exp_two_lt_nine : Real.exp 2 < 9 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]

/-- A concrete doubling bound for the slowly varying denominator.  The
constant `8` is deliberately crude; its role is to make the `Θ` statement
below completely explicit. -/
theorem logDenom896_sq_le (N : ℕ) (hN : 9 ≤ N) :
    logDenom896 (N ^ 2) ≤ 8 * logDenom896 N := by
  have hNpos : 0 < N := by omega
  have hNRpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hlogN2 : (2 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNRpos]
    exact exp_two_lt_nine.le.trans (by exact_mod_cast hN)
  have hlogNpos : 0 < Real.log N := (by norm_num : (0 : ℝ) < 2).trans_le hlogN2
  have hloglogNpos : 0 < Real.log (Real.log N) :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le hlogN2)
  have hlog2_le : Real.log 2 ≤ Real.log (Real.log N) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
      (Set.mem_Ioi.mpr hlogNpos) hlogN2
  have hlog_sq : Real.log ((N ^ 2 : ℕ) : ℝ) = 2 * Real.log N := by
    rw [pow_two, Nat.cast_mul, Real.log_mul hNRpos.ne' hNRpos.ne']
    ring
  have hloglog_sq :
      Real.log (Real.log ((N ^ 2 : ℕ) : ℝ)) =
        Real.log 2 + Real.log (Real.log N) := by
    rw [hlog_sq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogNpos.ne']
  have hloglog_sq_nonneg :
      0 ≤ Real.log (Real.log ((N ^ 2 : ℕ) : ℝ)) := by
    rw [hloglog_sq]
    exact add_nonneg (Real.log_nonneg (by norm_num)) hloglogNpos.le
  have htwo_delta : (2 : ℝ) ^ delta896 ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        delta896_le_one)
  have hfirst :
      (Real.log ((N ^ 2 : ℕ) : ℝ)) ^ delta896 ≤
        2 * (Real.log N) ^ delta896 := by
    rw [hlog_sq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlogNpos.le]
    exact mul_le_mul_of_nonneg_right htwo_delta
      (Real.rpow_nonneg hlogNpos.le _)
  have htwo_three_halves : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hloglog_sq_le :
      Real.log (Real.log ((N ^ 2 : ℕ) : ℝ)) ≤
        2 * Real.log (Real.log N) := by
    rw [hloglog_sq]
    linarith
  have hsecond :
      (Real.log (Real.log ((N ^ 2 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) ≤
        4 * (Real.log (Real.log N)) ^ (3 / 2 : ℝ) := by
    calc
      (Real.log (Real.log ((N ^ 2 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) ≤
          (2 * Real.log (Real.log N)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow
          hloglog_sq_nonneg hloglog_sq_le (by norm_num)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) *
          (Real.log (Real.log N)) ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hloglogNpos.le]
      _ ≤ 4 * (Real.log (Real.log N)) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right htwo_three_halves
          (Real.rpow_nonneg hloglogNpos.le _)
  unfold logDenom896 logDenom896R
  calc
    (Real.log ((N ^ 2 : ℕ) : ℝ)) ^ delta896 *
          (Real.log (Real.log ((N ^ 2 : ℕ) : ℝ))) ^ (3 / 2 : ℝ) ≤
        (2 * (Real.log N) ^ delta896) *
          (4 * (Real.log (Real.log N)) ^ (3 / 2 : ℝ)) :=
      mul_le_mul hfirst hsecond
        (Real.rpow_nonneg hloglog_sq_nonneg _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogNpos.le _))
    _ = 8 * ((Real.log N) ^ delta896 *
          (Real.log (Real.log N)) ^ (3 / 2 : ℝ)) := by ring

theorem logDenom896_sq_comparable (N : ℕ) (hN : 9 ≤ N) :
    logDenom896 N ≤ logDenom896 (N ^ 2) ∧
      logDenom896 (N ^ 2) ≤ 8 * logDenom896 N := by
  exact ⟨logDenom896_le_sq N (by omega), logDenom896_sq_le N hN⟩

/-- The slowly varying denominator changes by at most a constant factor
when its argument is squared. -/
theorem logDenom896_sq_isTheta :
    (fun N : ℕ ↦ logDenom896 (N ^ 2)) =Θ[atTop]
      (fun N : ℕ ↦ logDenom896 N) := by
  constructor
  · apply IsBigO.of_bound 8
    filter_upwards [eventually_ge_atTop 9] with N hN
    have hN3 : 3 ≤ N := by omega
    have hsq3 : 3 ≤ N ^ 2 := le_trans hN3 (by nlinarith)
    rw [Real.norm_of_nonneg (logDenom896_pos hsq3).le,
      Real.norm_of_nonneg (logDenom896_pos hN3).le]
    exact logDenom896_sq_le N hN
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hNNsq : N ≤ N ^ 2 := by nlinarith
    have hsq3 : 3 ≤ N ^ 2 := hN.trans hNNsq
    rw [Real.norm_of_nonneg (logDenom896_pos hN).le,
      Real.norm_of_nonneg (logDenom896_pos hsq3).le]
    exact logDenom896_le_sq N hN

end Erdos896
