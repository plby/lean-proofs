import ErdosProblems.Erdos1164.DiscCoverage
import ErdosProblems.Erdos1164.ReturnClock

/-! # The lower tail of the covered radius -/

open MeasureTheory
open scoped ENNReal

namespace Erdos1164

/-- A deterministic return budget sufficient for a union bound over a disc. -/
noncomputable def discReturnBudget (r : ℕ) : ℕ :=
  ⌈1000 * Real.log ((r + 2 : ℕ) : ℝ) ^ 2⌉₊

theorem discReturnBudget_pos (r : ℕ) : 1 ≤ discReturnBudget r := by
  apply Nat.one_le_ceil_iff.mpr
  have hlog : 0 < Real.log ((r + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < r + 2))
  positivity

theorem discReturnBudget_lower (r : ℕ) :
    1000 * Real.log ((r + 2 : ℕ) : ℝ) ^ 2 ≤ (discReturnBudget r : ℝ) :=
  Nat.le_ceil _

theorem discReturnBudget_upper (r : ℕ) :
    (discReturnBudget r : ℝ) ≤ 1000 * Real.log ((r + 2 : ℕ) : ℝ) ^ 2 + 1 :=
  (Nat.ceil_lt_add_one (by positivity)).le

theorem disc_budget_exponential_cost (r : ℕ) :
    ((2 * r + 1 : ℕ) : ℝ≥0∞) ^ 2 *
      ENNReal.ofReal (Real.exp (-(discReturnBudget r : ℝ) /
        (200 * Real.log ((r + 2 : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (4 / (((r + 2 : ℕ) : ℝ) ^ 3)) := by
  let x : ℝ := ((r + 2 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : 0 < Real.log x := Real.log_pos (by dsimp [x]; exact_mod_cast (by omega : 1 < r + 2))
  have hexp : Real.exp (-(discReturnBudget r : ℝ) / (200 * Real.log x)) ≤
      1 / x ^ 5 := by
    have hb := discReturnBudget_lower r
    have he : -(discReturnBudget r : ℝ) / (200 * Real.log x) ≤ -Real.log (x ^ 5) := by
      rw [Real.log_pow]
      apply (div_le_iff₀ (by positivity : 0 < 200 * Real.log x)).mpr
      dsimp only [x] at *
      norm_num only [Nat.cast_ofNat]
      nlinarith
    have h := Real.exp_le_exp.mpr he
    rw [Real.exp_neg, Real.exp_log (pow_pos hx 5)] at h
    simpa only [one_div] using h
  have hpoly : (((2 * r + 1 : ℕ) : ℝ) ^ 2) * (1 / x ^ 5) ≤ 4 / x ^ 3 := by
    have hcoord : ((2 * r + 1 : ℕ) : ℝ) ≤ 2 * x := by dsimp [x]; push_cast; linarith
    have hsq : (((2 * r + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * x ^ 2 := by nlinarith
    calc
      (((2 * r + 1 : ℕ) : ℝ) ^ 2) * (1 / x ^ 5) ≤ (4 * x ^ 2) * (1 / x ^ 5) := by gcongr
      _ = 4 / x ^ 3 := by field_simp
  calc
    ((2 * r + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal
        (Real.exp (-(discReturnBudget r : ℝ) / (200 * Real.log x))) ≤
      ((2 * r + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 / x ^ 5) := by
        gcongr
    _ = ENNReal.ofReal ((((2 * r + 1 : ℕ) : ℝ) ^ 2) * (1 / x ^ 5)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 / x ^ 3) := ENNReal.ofReal_le_ofReal hpoly

/-- An unconditional finite-time lower-radius estimate with explicit constants.
The sole size condition says the return budget is at most square-root time. -/
theorem radius_lower_tail (n r : ℕ) (hn : 2 ≤ n)
    (hbudget : (discReturnBudget r + 1) ^ 2 ≤ n) :
    walkLaw {s | coveredRadius s n < r} ≤
      ENNReal.ofReal (24 * (discReturnBudget r : ℝ) / Real.log (n : ℝ) +
        4 / (((r + 2 : ℕ) : ℝ) ^ 3)) := by
  have hk : 2 ≤ discReturnBudget r + 1 := by have := discReturnBudget_pos r; omega
  have hsplit := radius_lower_tail_split n r (discReturnBudget r + 1) hk
  simp only [Nat.add_sub_cancel] at hsplit
  have hclock := originVisits_lower_tail hn hbudget
  have hdisc := disc_budget_exponential_cost r
  apply hsplit.trans
  have hsum := add_le_add hclock hdisc
  apply hsum.trans_eq
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]

end Erdos1164
