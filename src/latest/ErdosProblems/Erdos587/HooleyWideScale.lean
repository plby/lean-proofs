import ErdosProblems.Erdos587.HooleyWideCutoff

/-! # Fixed ambient and frequency cutoffs in the power-separated branch -/

namespace Erdos587

lemma delta_wide_centered_scale_conditions {T : ℝ} (hT : 2 ≤ T) {q M : ℕ}
    (hq : (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ))
    (hMlo : T ^ (2499 / 10000 : ℝ) ≤ M) (hMhi : (M : ℝ) ≤ T) :
    let N := ⌊T ^ 2⌋₊
    let X := ⌊T ^ 8⌋₊
    M ≤ N ∧ 2 * (N : ℝ) * Real.sqrt T ≤ X ∧
      (q : ℝ) * (X : ℝ) ^ (1 / 100000 : ℝ) ≤ M * Real.sqrt T ∧ q ≤ X ∧ 2 ≤ X := by
  let N := ⌊T ^ 2⌋₊
  let X := ⌊T ^ 8⌋₊
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hNlo : T ≤ (N : ℝ) := by
    simpa only [pow_one] using (delta_floor_power_step_bounds hT 1).1
  have hNhi : (N : ℝ) ≤ T ^ 2 := Nat.floor_le (by positivity)
  have hXlo : T ^ 7 ≤ (X : ℝ) := (delta_floor_power_step_bounds hT 7).1
  have hXhi : (X : ℝ) ≤ T ^ 8 := Nat.floor_le (by positivity)
  have hT7 : T ≤ T ^ 7 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT1 (show 1 ≤ 7 by omega)
  have hTX : T ≤ (X : ℝ) := hT7.trans hXlo
  have hMN : M ≤ N := by exact_mod_cast hMhi.trans hNlo
  have hsqrt : Real.sqrt T ≤ T := (Real.sqrt_le_iff).mpr ⟨hTpos.le, by nlinarith⟩
  have hsize : 2 * (N : ℝ) * Real.sqrt T ≤ X := by
    calc
      _ ≤ 2 * T ^ 2 * T := by gcongr
      _ = 2 * T ^ 3 := by ring
      _ ≤ T ^ 4 := constant_mul_pow_le_pow hT1 hT (by omega)
      _ ≤ T ^ 7 := pow_le_pow_right₀ hT1 (by omega)
      _ ≤ X := hXlo
  have hpower : (q : ℝ) * (X : ℝ) ^ (1 / 100000 : ℝ) ≤ M * Real.sqrt T := by
    calc
      _ ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) * (T ^ 8) ^ (1 / 100000 : ℝ) := by
        gcongr
      _ = T ^ ((3 / 4 - 1 / 1000 : ℝ) + 8 * (1 / 100000 : ℝ)) := by
        rw [← Real.rpow_natCast_mul hTpos.le, ← Real.rpow_add hTpos]
        norm_num
      _ ≤ T ^ ((2499 / 10000 : ℝ) + 1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T ^ (2499 / 10000 : ℝ) * Real.sqrt T := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hTpos]
      _ ≤ M * Real.sqrt T := mul_le_mul_of_nonneg_right hMlo (Real.sqrt_nonneg _)
  have hqX : q ≤ X := by
    have hqT : (q : ℝ) ≤ T := by
      apply hq.trans
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hT1 (show (3 / 4 - 1 / 1000 : ℝ) ≤ 1 by norm_num)
    exact_mod_cast hqT.trans hTX
  have hX2 : 2 ≤ X := by exact_mod_cast hT.trans hTX
  exact ⟨hMN, hsize, hpower, hqX, hX2⟩

lemma delta_wide_ambient_loglog_bound {T : ℝ} (hT : 2 ≤ T) :
    max 1 (Real.log (Real.log ((⌊T ^ 8⌋₊ : ℕ) : ℝ))) ≤
      9 * max 1 (Real.log (Real.log T)) := by
  have hT1 : 1 < T := by linarith
  have hTpos : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hXlo := (delta_floor_power_step_bounds hT 7).1
  have hTpow : T ≤ T ^ 7 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT1.le (show 1 ≤ 7 by omega)
  have hX : (1 : ℝ) < (⌊T ^ 8⌋₊ : ℝ) := hT1.trans_le (hTpow.trans hXlo)
  have hlogs := Real.log_le_log (Real.log_pos hX)
    (Real.log_le_log (by linarith : (0 : ℝ) < ⌊T ^ 8⌋₊) (Nat.floor_le (by positivity)))
  rw [Real.log_pow, Nat.cast_ofNat, Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hlogT.ne'] at hlogs
  have hlog8 : Real.log (8 : ℝ) ≤ 8 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hF1 := le_max_left (1 : ℝ) (Real.log (Real.log T))
  have hFlog := le_max_right (1 : ℝ) (Real.log (Real.log T))
  apply max_le <;> linarith

lemma delta_wide_loglog_mean_cost {T : ℝ} (hT : 2 ≤ T) :
    (max 1 (Real.log (Real.log ((⌊T ^ 8⌋₊ : ℕ) : ℝ)))) ^ (7 / 2 : ℝ) ≤
      9 ^ 4 * (max 1 (Real.log (Real.log T))) ^ 4 := by
  have hF : 1 ≤ max 1 (Real.log (Real.log T)) := le_max_left _ _
  calc
    _ ≤ (9 * max 1 (Real.log (Real.log T))) ^ (7 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (delta_wide_ambient_loglog_bound hT) (by norm_num)
    _ ≤ (9 * max 1 (Real.log (Real.log T))) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = _ := by norm_num [mul_pow]

end Erdos587
