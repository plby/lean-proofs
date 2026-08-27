import ErdosProblems.Erdos587.HooleyCenteredWeighted
import ErdosProblems.Erdos587.WideScales

/-! # The log-log cutoff for the power-separated terminal branch -/

open Filter

namespace Erdos587

lemma delta_loglog_le_one_add_log {T : ℝ} (hT : 1 ≤ T) :
    max 1 (Real.log (Real.log T)) ≤ 1 + Real.log T := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  apply max_le
  · linarith
  · by_cases hp : 0 < Real.log T
    · have hh := Real.log_le_sub_one_of_pos hp
      linarith
    · have hz : Real.log T = 0 := le_antisymm (le_of_not_gt hp) hlog
      simp only [hz, Real.log_zero]
      norm_num

lemma delta_floor_power_step_bounds {x : ℝ} (hx : 2 ≤ x) (n : ℕ) :
    x ^ n ≤ (⌊x ^ (n + 1)⌋₊ : ℝ) ∧ (⌊x ^ (n + 1)⌋₊ : ℝ) ≤ x ^ (n + 1) := by
  have hx1 : 1 ≤ x := by linarith
  have h1 : 1 ≤ x ^ n := one_le_pow₀ hx1
  have h2 : 2 * x ^ n ≤ x ^ (n + 1) := constant_mul_pow_le_pow hx1 hx le_rfl
  have hf := Nat.lt_floor_add_one (x ^ (n + 1))
  exact ⟨by linarith, Nat.floor_le (by positivity)⟩

theorem eventually_delta_wide_cutoff_bounds (p : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      let s := T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ p
      let M := ⌊s⌋₊
      0 < M ∧ T ^ (2499 / 10000 : ℝ) ≤ M ∧ (M : ℝ) ≤ s ∧ s / 2 ≤ M ∧ (M : ℝ) ≤ T := by
  filter_upwards [eventually_wide_cutoff_bounds p, eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 2499 / 10000 by norm_num)).eventually_ge_atTop 2]
    with T hold hT hlarge
  let Λ := max 1 (Real.log (Real.log T))
  let s := T ^ (1 / 4 : ℝ) / Λ ^ p
  let M := ⌊s⌋₊
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ1
  have hratio : T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ p ≤ s := by
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) (by positivity)
    exact pow_le_pow_left₀ hΛpos.le (delta_loglog_le_one_add_log hT) p
  have hfloor : ⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ p⌋₊ ≤ M := Nat.floor_mono hratio
  have hlo : T ^ (2499 / 10000 : ℝ) ≤ M :=
    hold.2.1.trans (by exact_mod_cast hfloor)
  have hhi : (M : ℝ) ≤ s := Nat.floor_le (by dsimp [s]; positivity)
  have hs : 2 ≤ s := hlarge.trans (hlo.trans hhi)
  have hMT : (M : ℝ) ≤ T := by
    calc
      _ ≤ s := hhi
      _ ≤ T ^ (1 / 4 : ℝ) := div_le_self (by positivity) (one_le_pow₀ hΛ1)
      _ ≤ T := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hT (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  exact ⟨hold.1.trans_le hfloor, hlo, hhi, half_le_nat_floor hs, hMT⟩

theorem eventually_delta_wide_cutoff_error_budget (K : ℝ) (hK : 0 < K) :
    ∀ᶠ T : ℝ in atTop,
      let Λ := max 1 (Real.log (Real.log T))
      let M := ⌊T ^ (1 / 4 : ℝ) / Λ ^ 6⌋₊
      K * M * Λ ^ 5 < Real.sqrt (Real.sqrt T) := by
  filter_upwards [eventually_delta_wide_cutoff_bounds 6, eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (K + 1)]
    with T hcut hT hlog
  change K + 1 ≤ Real.log (Real.log T) at hlog
  let Λ := max 1 (Real.log (Real.log T))
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛ : 0 < Λ := zero_lt_one.trans_le hΛ1
  have hKΛ : K < Λ := by have := le_max_right (1 : ℝ) (Real.log (Real.log T)); linarith
  have hTpos : 0 < T := by linarith
  have hroot : T ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt T) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hTpos.le]
    norm_num
  calc
    _ ≤ K * (T ^ (1 / 4 : ℝ) / Λ ^ 6) * Λ ^ 5 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcut.2.2.1 hK.le
    _ = (K / Λ) * T ^ (1 / 4 : ℝ) := by
      rw [show Λ ^ 6 = Λ ^ 5 * Λ by ring]
      field_simp
    _ < 1 * T ^ (1 / 4 : ℝ) :=
      mul_lt_mul_of_pos_right ((div_lt_one hΛ).mpr hKΛ) (Real.rpow_pos_of_pos hTpos _)
    _ = _ := by rw [one_mul, hroot]

end Erdos587
