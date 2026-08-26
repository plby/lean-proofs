import ErdosProblems.Erdos327.External.Mertens

namespace Erdos327.Analytic

open Filter Real Asymptotics
open scoped Nat

/-- Mertens' second theorem in the bounded-error form used by the
cutoff Euler-product estimates. -/
theorem primeReciprocalSum_sub_logLog_isBigO :
    (fun N : ℕ =>
      (∑ p ∈ Nat.primesLE N, 1 / (p : ℝ)) - log (log N))
      =O[atTop] fun _ ↦ (1 : ℝ) :=
  Mertens.sum_prime_inv_sub_isBigO_nat

/-- Mertens' third theorem in the exact asymptotic form used throughout
the analytic part of the construction. -/
theorem primeProduct_asymp :
    (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p))
      ~[atTop] (fun N : ℕ ↦ exp (-eulerMascheroniConstant) / log N) :=
  Mertens.prod_prime_one_minus_inv_asymp_nat

/-- The explicit error estimate behind Mertens' third theorem. -/
theorem primeProduct_error_bound {N : ℕ} (hN : 2 ≤ N) :
    |Mertens.E₃ N| ≤
      (log 4 + 3) / log N + 1 / N :=
  by
    simpa using Mertens.E₃_bound (x := (N : ℝ)) (mod_cast hN)

/-- A fixed explicit error reserve for the lower form of Mertens' third
theorem. -/
noncomputable def mertensLowerError : ℝ :=
  (log 4 + 3) / log 2 + 1 / 2

/-- A fixed positive constant in the lower Mertens product estimate. -/
noncomputable def mertensLowerConstant : ℝ :=
  exp (-eulerMascheroniConstant) * exp (-mertensLowerError)

theorem mertensLowerConstant_pos :
    0 < mertensLowerConstant := by
  unfold mertensLowerConstant
  positivity

/-- Explicit lower bound `c / log N` for the prime product. -/
theorem mertensLowerConstant_div_log_le_primeProduct
    {N : ℕ} (hN : 2 ≤ N) :
    mertensLowerConstant / log N ≤
      ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogN : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hN))
  have hlogMono : log (2 : ℝ) ≤ log (N : ℝ) := by
    exact log_le_log (by norm_num) (by exact_mod_cast hN)
  have hinvLog :
      1 / log (N : ℝ) ≤ 1 / log (2 : ℝ) := by
    exact one_div_le_one_div_of_le hlog2 hlogMono
  have hinvN : 1 / (N : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
  have herror :
      (log 4 + 3) / log (N : ℝ) + 1 / (N : ℝ) ≤
        mertensLowerError := by
    unfold mertensLowerError
    have hcoef : 0 ≤ log 4 + 3 := by positivity
    have hterm :
        (log 4 + 3) / log (N : ℝ) ≤
          (log 4 + 3) / log (2 : ℝ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvLog hcoef
    exact add_le_add hterm hinvN
  have hEbound := primeProduct_error_bound hN
  have hE : -mertensLowerError ≤ Mertens.E₃ N := by
    rw [abs_le] at hEbound
    linarith
  rw [Mertens.prod_prime_one_minus_inv_eq_nat (lt_of_lt_of_le (by omega : 1 < 2) hN)]
  unfold mertensLowerConstant
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hE) (exp_nonneg _))
    hlogN.le

end Erdos327.Analytic
