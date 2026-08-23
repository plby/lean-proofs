/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary analytic estimates for Erdős Problem 240

These lemmas isolate the elementary real-analytic and dyadic-logarithm
estimates used after applying a lower bound for a linear form in logarithms.
-/

namespace Erdos240

/-- A gap smaller than the integer square root gives the logarithmic upper
bound used opposite the Baker--Wuestholz lower bound. -/
lemma log_ratio_lt_exp_neg_half_log_of_bad_gap {a b : ℕ}
    (ha : 0 < a) (hab : a < b) (hgap : b - a < Nat.sqrt a) :
    Real.log ((b : ℝ) / (a : ℝ)) <
      Real.exp (-Real.log (a : ℝ) / 2) := by
  have haR : (0 : ℝ) < a := by positivity
  have hbR : (0 : ℝ) < b := by
    exact_mod_cast (show 0 < b by omega)
  have hratioPos : (0 : ℝ) < (b : ℝ) / (a : ℝ) := div_pos hbR haR
  have hratioNe : (b : ℝ) / (a : ℝ) ≠ 1 := by
    intro h
    have hba : (b : ℝ) = (a : ℝ) := (div_eq_one_iff_eq haR.ne').mp h
    have hbaNat : b = a := by exact_mod_cast hba
    exact hab.ne' hbaNat
  have hlog : Real.log ((b : ℝ) / (a : ℝ)) <
      (b : ℝ) / (a : ℝ) - 1 :=
    Real.log_lt_sub_one_of_pos hratioPos hratioNe
  have hratioSub : (b : ℝ) / (a : ℝ) - 1 =
      ((b - a : ℕ) : ℝ) / (a : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hab)]
    field_simp
  have hgapR : ((b - a : ℕ) : ℝ) < Real.sqrt (a : ℝ) := by
    calc
      ((b - a : ℕ) : ℝ) < (Nat.sqrt a : ℝ) := by exact_mod_cast hgap
      _ ≤ Real.sqrt (a : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hdiv : ((b - a : ℕ) : ℝ) / (a : ℝ) <
      Real.sqrt (a : ℝ) / (a : ℝ) :=
    div_lt_div_of_pos_right hgapR haR
  have hsqrtPos : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.2 haR
  have hsqrtSq : Real.sqrt (a : ℝ) * Real.sqrt (a : ℝ) = (a : ℝ) := by
    nlinarith [Real.sq_sqrt haR.le]
  have hsqrtDiv : Real.sqrt (a : ℝ) / (a : ℝ) =
      (Real.sqrt (a : ℝ))⁻¹ := by
    apply (div_eq_iff haR.ne').2
    rw [inv_mul_eq_div]
    apply (eq_div_iff hsqrtPos.ne').2
    exact hsqrtSq
  have hexp : Real.exp (-Real.log (a : ℝ) / 2) =
      (Real.sqrt (a : ℝ))⁻¹ := by
    rw [show -Real.log (a : ℝ) / 2 = -Real.log (Real.sqrt (a : ℝ)) by
      rw [Real.log_sqrt haR.le]
      ring]
    rw [Real.exp_neg, Real.exp_log hsqrtPos]
  rw [hratioSub] at hlog
  rw [hexp, ← hsqrtDiv]
  exact hlog.trans hdiv

/-- An elementary logarithm bound with constants convenient for the
post-Baker bootstrap. -/
lemma log_five_mul_le_four_sqrt {y : ℝ} (hy : 1 ≤ y) :
    Real.log (5 * y) ≤ 4 * Real.sqrt y := by
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hsqrt : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hsqrtSq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hyPos.le
  have hfivePos : 0 < 5 * y := mul_pos (by norm_num) hyPos
  apply (Real.log_le_iff_le_exp hfivePos).2
  calc
    5 * y ≤ 1 + 4 * Real.sqrt y + (4 * Real.sqrt y) ^ 2 / 2 := by
      nlinarith [hsqrtSq]
    _ ≤ Real.exp (4 * Real.sqrt y) := by
      exact Real.quadratic_le_exp_of_nonneg (mul_nonneg (by norm_num) hsqrt)

/-- Solving the self-referential inequality produced by the symmetric
Baker--Wuestholz estimate. -/
lemma le_sixtyFour_mul_sq_of_half_lt_mul_log {x y K : ℝ}
    (hx : 0 ≤ x) (hy : 1 ≤ y) (hK : 0 ≤ K)
    (h : y / 2 < K * x * Real.log (5 * y)) :
    y ≤ 64 * K ^ 2 * x ^ 2 := by
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hsqrtPos : 0 < Real.sqrt y := Real.sqrt_pos.2 hyPos
  have hsqrtSq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hyPos.le
  have hKx : 0 ≤ K * x := mul_nonneg hK hx
  have hlog := log_five_mul_le_four_sqrt hy
  have hmain : y / 2 < K * x * (4 * Real.sqrt y) :=
    h.trans_le (mul_le_mul_of_nonneg_left hlog hKx)
  have hsqrtBound : Real.sqrt y < 8 * K * x := by
    rw [← hsqrtSq] at hmain
    nlinarith
  nlinarith [sq_nonneg (8 * K * x - Real.sqrt y)]

/-- A real logarithm is controlled by twice the dyadic natural logarithm.
The hypotheses `2 ≤ p ≤ n` already provide a sufficient threshold on `n`. -/
lemma real_log_le_two_natLog_two {p n : ℕ} (hp : 2 ≤ p) (hpn : p ≤ n) :
    Real.log (p : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hn : 2 ≤ n := hp.trans hpn
  have hnR : (0 : ℝ) < n := by positivity
  have hlogpn : Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log hpR (by exact_mod_cast hpn)
  have hpowNat : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by omega) n
  have hpowReal : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hpowNat
  have hlogn : Real.log (n : ℝ) <
      Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) := by
    exact (Real.log_lt_log_iff hnR (by positivity)).2 hpowReal
  have hlogn' : Real.log (n : ℝ) <
      ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
    simpa only [Real.log_pow] using hlogn
  have hdyadicOne : 1 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by omega) hn
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hdyadic : ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 ≤
      2 * (Nat.log 2 n : ℝ) := by
    have hcast : (((Nat.log 2 n + 1 : ℕ) : ℝ)) ≤
        2 * (Nat.log 2 n : ℝ) := by
      exact_mod_cast (show Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n by omega)
    calc
      ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          ((Nat.log 2 n + 1 : ℕ) : ℝ) * 1 := by
        gcongr
      _ ≤ 2 * (Nat.log 2 n : ℝ) := by simpa using hcast
  exact hlogpn.trans (hlogn'.le.trans hdyadic)

end Erdos240

#print axioms Erdos240.log_ratio_lt_exp_neg_half_log_of_bad_gap
#print axioms Erdos240.log_five_mul_le_four_sqrt
#print axioms Erdos240.le_sixtyFour_mul_sq_of_half_lt_mul_log
#print axioms Erdos240.real_log_le_two_natLog_two
