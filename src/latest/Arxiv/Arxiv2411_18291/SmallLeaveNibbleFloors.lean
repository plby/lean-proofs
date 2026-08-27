import Arxiv.Arxiv2411_18291.ScaledNibbleInitialMargins

/-! # The scaled tracking bounds hold for every k at least three when p is at most 1/15 -/

namespace Arxiv2411_18291

theorem scaled_nibble_small_leave_coefficient_bounds {k : ℕ} (hk : 3 ≤ k) :
    512 * k ≤ 5 * 15 ^ k ∧ 8 * k ^ 2 ≤ 5 * 15 ^ (k - 2) ∧ 52 ≤ 15 ^ (k - 1) :=
  scaled_nibble_coefficient_bounds_of_seed (by norm_num) (by norm_num) (by norm_num) hk

theorem scaled_nibble_small_leave_conditions {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1 / 15) :
    NibbleFloorConditions k (scaledNibbleError k p) (2 * p) ∧
      2 * p + (128 * (k : ℝ) + 1) * scaledNibbleError k p ≤ 3 * p ∧
      (p ^ k) ^ 3 ≤ 1 ∧
      (p ^ k) ^ 3 < (k : ℝ) * (16 * (k : ℝ) ^ 2 - 1) * (scaledNibbleError k p) ^ 3 ∧
      (p ^ k) ^ 3 < (16 * (k : ℝ) - 1) * (scaledNibbleError k p) ^ 2 := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff := scaled_nibble_small_leave_coefficient_bounds hk
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 2) := one_le_pow₀ (by norm_num)
  have hvar : (128 : ℝ) * (1 / 15) ^ 2 ≤ (k : ℝ) * 2 ^ (k - 2) := by
    have hh := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg k)
    norm_num at hh ⊢
    linarith only [hK, hh]
  obtain ⟨hF, hend⟩ := scaled_nibble_floor_of_coefficients (by norm_num : 0 < 15)
    hk hcoeff hvar hp0.le hp
  have hsmallC : (512 / 5 : ℝ) * k ≤ (15 : ℝ) ^ k := by
    have hh : 512 * (k : ℝ) ≤ 5 * (15 : ℝ) ^ k := by exact_mod_cast hcoeff.1
    linarith only [hh]
  have hsmall := nibble_coefficient_times_floor_pow_le_one_of_base
    (by norm_num : (0 : ℝ) < 15) hp0.le hp hsmallC
  obtain ⟨hb, hcount, hedge⟩ := scaled_nibble_initial_margins_of_small_power
    hk hp0 (hp.trans (by norm_num)) hsmall
  exact ⟨hF, hend, hb, hcount, hedge⟩

end Arxiv2411_18291
