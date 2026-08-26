import ErdosProblems.Erdos421.ComparableWindowScales

/-! # A fixed exponent margin absorbs the change of product scale -/

namespace Erdos421

open Filter Topology

theorem eventually_comparable_factor_band {β φ : ℝ} (hβ : 0 < β) (hφ : φ < 1 / 5) :
    ∀ᶠ X : ℕ in atTop, ∀ T H : ℝ, X / 4 ≤ T → T ≤ 3 * X →
      (X : ℝ) ^ β ≤ H → H ≤ (X : ℝ) ^ φ →
      T ^ (β / 2) ≤ H ∧ H ≤ T ^ (1 / 5 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_constant_rpow_le ((3 : ℝ) ^ (β / 2)) (by linarith : β / 2 < β),
    eventually_constant_rpow_le ((4 : ℝ) ^ (1 / 5 : ℝ)) hφ] with X hX hlo hhi
  intro T H hXT hTX hHlo hHhi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hTp : 0 < T := (div_pos hXp (by norm_num : (0 : ℝ) < 4)).trans_le hXT
  constructor
  · calc
      _ ≤ (3 * (X : ℝ)) ^ (β / 2) := Real.rpow_le_rpow hTp.le hTX (by positivity)
      _ = (3 : ℝ) ^ (β / 2) * (X : ℝ) ^ (β / 2) := Real.mul_rpow (by norm_num) hXp.le
      _ ≤ (X : ℝ) ^ β := hlo
      _ ≤ H := hHlo
  · calc
      H ≤ (X : ℝ) ^ φ := hHhi
      _ ≤ ((X : ℝ) / 4) ^ (1 / 5 : ℝ) := by
        rw [Real.div_rpow hXp.le (by norm_num)]
        apply (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _)).mpr
        simpa only [mul_comm] using hhi
      _ ≤ T ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hXT (by norm_num)

theorem constant_short_window_below_log_scale {C d : ℝ} (hC : 0 < C) (hd : 0 < d) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop, C / (X : ℝ) ^ d ≤ (Real.log X) ^ (-B) := by
  filter_upwards [inverse_log_above_inverse_power hd (inv_pos.mpr hC) B,
    eventually_ge_atTop (2 : ℕ)] with X hsave hX
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hm := mul_le_mul_of_nonneg_left hsave hC.le
  rw [Real.rpow_neg hXp.le] at hm
  rw [Real.rpow_neg hL.le]
  simpa only [div_eq_mul_inv, ← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hm

end Erdos421
