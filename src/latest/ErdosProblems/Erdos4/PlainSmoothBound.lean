import ErdosProblems.Erdos4.SmoothParameters

/-!
# All smooth survivors on a fixed parameter ray

The zero-residue construction requires a bound for every smooth integer,
not only the older shifted-coprime exceptional set. The existing Rankin
Euler-product bound applies without that extra filter. Choosing one fixed
loss parameter gives a strong uniform estimate for arbitrary interval
endpoints in the required range.
-/

open scoped BigOperators

namespace Erdos4.PlainSmoothBound

open SmoothParameters

theorem exp_eight_decay (r : ℕ) :
    Real.exp (-8 * Real.log 2 * (2 : ℝ) ^ r) = ((core r : ℝ) ^ 8)⁻¹ := by
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have heq : -8 * Real.log 2 * (2 : ℝ) ^ r = -Real.log ((core r : ℝ) ^ 8) := by
    rw [Real.log_pow, log_core]
    norm_num
    ring
  rw [heq, Real.exp_neg, Real.exp_log (pow_pos hcore 8)]

theorem smooth_count_le_decay {B : ℝ} {a r U : ℕ} (hr : 1 ≤ r)
    (hB : B + 8 * Real.log 2 ≤ (2 : ℝ) ^ a * Real.log 2)
    (hEuler : Erdos469.smoothRankinEulerProduct (delta r) (smoothFrontier r) ≤
      Real.exp (B * (2 : ℝ) ^ r))
    (hU : primaryFrontier a r ≤ U) :
    ((Nat.smoothNumbersUpTo U (smoothFrontier r + 1)).card : ℝ) ≤
      (U : ℝ) / (core r : ℝ) ^ 8 := by
  have hUpos : 0 < U := (primaryFrontier_pos a r).trans_le hU
  have hbase : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hlog : Real.log (primaryFrontier a r : ℝ) ≤ Real.log (U : ℝ) :=
    Real.log_le_log hbase (by exact_mod_cast hU)
  have hsave := mul_le_mul_of_nonneg_left hlog (delta_pos r).le
  rw [delta_mul_log_primaryFrontier] at hsave
  have hBmul := mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ (2 : ℝ) ^ r)
  rw [pow_add] at hsave
  have hexponent : B * (2 : ℝ) ^ r - delta r * Real.log U ≤
      -8 * Real.log 2 * (2 : ℝ) ^ r := by nlinarith
  have hRankin := Erdos469.card_smoothNumbersUpTo_rankin_le (y := smoothFrontier r) hUpos (delta_pos r)
    ((delta_le_half r).trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  calc
    _ ≤ (U : ℝ) ^ (1 - delta r) * Erdos469.smoothRankinEulerProduct (delta r) (smoothFrontier r) := hRankin
    _ ≤ (U : ℝ) ^ (1 - delta r) * Real.exp (B * (2 : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left hEuler (Real.rpow_nonneg (Nat.cast_nonneg U) _)
    _ = (U : ℝ) * Real.exp (B * (2 : ℝ) ^ r - delta r * Real.log U) := by
      rw [rpow_one_sub_eq_mul_exp_neg hUpos, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (U : ℝ) * Real.exp (-8 * Real.log 2 * (2 : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (Nat.cast_nonneg U)
    _ = _ := by rw [exp_eight_decay, div_eq_mul_inv]

/-- The fixed loss parameter is chosen before the length multiplier and
all outer endpoints. This bounds the entire smooth set, without a
shifted-coprimality restriction. -/
theorem exists_uniform_plain_smooth_bound :
    ∃ a : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ M : ℝ, ∀ U : ℕ,
      primaryFrontier a r ≤ U →
      (U : ℝ) ≤ M * (primaryFrontier a r : ℝ) ^ 50 * (core r : ℝ) ^ 2 →
      ((Nat.smoothNumbersUpTo U (smoothFrontier r + 1)).card : ℝ) ≤
        M * (primaryFrontier a r : ℝ) ^ 50 / (core r : ℝ) ^ 6 := by
  obtain ⟨B, _hBpos, hEuler⟩ := exists_eulerExponentConstant
  obtain ⟨a, ha⟩ := exists_lossExponent (B + 4 * Real.log 2)
  have hB : B + 8 * Real.log 2 ≤ (2 : ℝ) ^ a * Real.log 2 := by linarith
  refine ⟨a, ?_⟩
  intro r hr M U hU hUupper
  have hc : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  calc
    _ ≤ (U : ℝ) / (core r : ℝ) ^ 8 := smooth_count_le_decay hr hB (hEuler r hr) hU
    _ ≤ (M * (primaryFrontier a r : ℝ) ^ 50 * (core r : ℝ) ^ 2) / (core r : ℝ) ^ 8 :=
      div_le_div_of_nonneg_right hUupper (by positivity)
    _ = _ := by field_simp

end Erdos4.PlainSmoothBound
