import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ENNReal

namespace CofiniteDerivatives

/-- The logarithm of a natural number is eventually bounded by any positive multiple of its
square root. -/
theorem eventually_log_le_mul_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * Real.sqrt n := by
  have hlog_real : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ c * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlog_real,
    eventually_ge_atTop (1 : ℕ)] with n hn hnone
  rw [Real.sqrt_eq_rpow]
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnone)
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg hlog_nonneg, abs_of_nonneg hrpow_nonneg] at hn
  exact hn

/-- A stretched exponential with square-root exponent is summable on the natural numbers. -/
theorem summable_exp_neg_mul_sqrt {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * Real.sqrt n)) := by
  have hlog_nat : ∀ᶠ n : ℕ in atTop,
      2 * Real.log n ≤ c * Real.sqrt n := by
    filter_upwards [eventually_log_le_mul_sqrt (half_pos hc)] with n hn
    linarith
  have hle : ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * Real.sqrt n) ≤ (n : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [hlog_nat, eventually_ge_atTop (1 : ℕ)] with n hn hnone
    calc
      Real.exp (-c * Real.sqrt n)
          ≤ Real.exp (-2 * Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = (n : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hnone))]
        congr 1
        ring
  have hmajor : Summable (fun n : ℕ =>
      max (Real.exp (-c * Real.sqrt n)) ((n : ℝ) ^ (-2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).congr_atTop <|
      hle.mono fun _ hn => (max_eq_right hn).symm
  exact hmajor.of_nonneg_of_le (fun _ => Real.exp_nonneg _) fun _ => le_max_left _ _

/-- The corresponding nonnegative `ENNReal` series has finite total mass. -/
theorem ennreal_tsum_mul_exp_neg_mul_sqrt_ne_top {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    (∑' n : ℕ, ENNReal.ofReal (C * Real.exp (-c * Real.sqrt n))) ≠ ∞ := by
  have hsum : Summable (fun n : ℕ => C * Real.exp (-c * Real.sqrt n)) :=
    (summable_exp_neg_mul_sqrt hc).mul_left C
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg hC (Real.exp_nonneg _)) hsum]
  exact ENNReal.ofReal_ne_top

/-- For positive `a`, the square-root main term eventually absorbs the logarithmic and constant
losses in the threshold used for the tail estimate. -/
theorem eventually_half_mul_sqrt_le_threshold {a C0 : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      (a / 2) * Real.sqrt n ≤ a * Real.sqrt n - (2 + Real.log n / 2) - C0 := by
  have hlog : ∀ᶠ n : ℕ in atTop,
      Real.log n / 2 ≤ (a / 4) * Real.sqrt n := by
    filter_upwards [eventually_log_le_mul_sqrt (half_pos ha)] with n hn
    linarith
  have hsqrt : Tendsto (fun n : ℕ => (a / 4) * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  filter_upwards [hlog, hsqrt.eventually_ge_atTop (2 + C0)] with n hlogn hconstant
  linarith

/-- The shifted square-root/logarithm tail occurring in the application is summable; changing
finitely many initial terms is harmless. -/
theorem summable_exp_neg_sqrt_sub_log {a C0 : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ =>
      Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)) := by
  have hle : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8) ≤
        Real.exp (-(a / 16) * Real.sqrt n) := by
    filter_upwards [eventually_half_mul_sqrt_le_threshold (C0 := C0) ha] with n hn
    apply Real.exp_le_exp.mpr
    linarith
  have hmajor : Summable (fun n : ℕ =>
      max (Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8))
        (Real.exp (-(a / 16) * Real.sqrt n))) :=
    (summable_exp_neg_mul_sqrt (by positivity : 0 < a / 16)).congr_atTop <|
      hle.mono fun _ hn => (max_eq_right hn).symm
  exact hmajor.of_nonneg_of_le (fun _ => Real.exp_nonneg _) fun _ => le_max_left _ _

end CofiniteDerivatives
