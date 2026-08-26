/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Integer square-root scales for trimming dyadic spatial intervals.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Decay
import Mathlib.Data.Nat.Sqrt

namespace Erdos521

open Filter
open scoped Topology

theorem nat_sqrt_cast_le (n : ℕ) : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
  have hsq : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ),
    (Nat.cast_nonneg (Nat.sqrt n) : (0 : ℝ) ≤ Nat.sqrt n)]

theorem real_sqrt_lt_nat_sqrt_add_one (n : ℕ) : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
  have hsq : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ),
    (Nat.cast_nonneg (Nat.sqrt n) : (0 : ℝ) ≤ Nat.sqrt n)]

theorem nat_sqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

theorem nat_sqrt_div_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ by positivity)) _ hpow
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (Nat.sqrt n : ℝ) / n ≤ Real.sqrt n / n := div_le_div_of_nonneg_right (nat_sqrt_cast_le n) hn₀.le
    _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (n : ℝ) ^ (1 / 2 : ℝ) / n = (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hn₀]; norm_num

theorem nat_sqrt_lower_half {n : ℕ} (hn : 4 ≤ n) : Real.sqrt n / 2 ≤ (Nat.sqrt n : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.sqrt n := by
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]
  linarith [real_sqrt_lt_nat_sqrt_add_one n]

theorem eventually_two_pow_neg_sqrt_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ Nat.sqrt n)⁻¹ ≤ (n : ℝ) ^ p := by
  have hc : 0 < Real.log 2 / 2 := by positivity
  filter_upwards [eventually_exp_neg_rpow_le_rpow hc (by norm_num : (0 : ℝ) < 1 / 2) p,
    eventually_ge_atTop 4] with n hn hn₄
  apply le_trans _ hn
  have heq : ((2 : ℝ) ^ Nat.sqrt n)⁻¹ = Real.exp (-(Nat.sqrt n : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (nat_sqrt_lower_half hn₄) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [Real.sqrt_eq_rpow] at h
  nlinarith

end Erdos521
