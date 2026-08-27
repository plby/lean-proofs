import Arxiv.Arxiv2411_18291.ScaledInitialNibbleFloors

/-! # The original regularity error fits the smaller tracking intervals -/

namespace Arxiv2411_18291

theorem scaledNibbleError_pos {k : ℕ} (hk : 0 < k) {p : ℝ} (hp : 0 < p) :
    0 < scaledNibbleError k p := by unfold scaledNibbleError; positivity

theorem scaled_nibble_initial_margins_of_small_power {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1) (hsmall : (512 / 5 : ℝ) * k * p ^ k ≤ 1) :
    (p ^ k) ^ 3 ≤ 1 ∧
      (p ^ k) ^ 3 < (k : ℝ) * (16 * (k : ℝ) ^ 2 - 1) * (scaledNibbleError k p) ^ 3 ∧
      (p ^ k) ^ 3 < (16 * (k : ℝ) - 1) * (scaledNibbleError k p) ^ 2 := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hK]
  have hpk0 : 0 < p ^ k := pow_pos hp0 k
  have hcube := pow_le_one₀ (pow_nonneg hp0.le k)
    (pow_le_one₀ hp0.le (hp.trans (by norm_num)) : p ^ k ≤ 1) (n := 3)
  refine ⟨hcube, ?_, ?_⟩
  · have hc : (1 : ℝ) < (k : ℝ) * (16 * (k : ℝ) ^ 2 - 1) * (2 / (5 * k)) ^ 3 := by
      have heq : (k : ℝ) * (16 * (k : ℝ) ^ 2 - 1) * (2 / (5 * k)) ^ 3 =
          (128 * (k : ℝ) ^ 2 - 8) / (125 * (k : ℝ) ^ 2) := by
        field_simp
        ring
      rw [heq]
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith only [hK]
    simpa only [one_mul, scaledNibbleError, mul_pow, mul_assoc] using
      mul_lt_mul_of_pos_right hc (pow_pos hpk0 3)
  · have hh := hsmall
    have hkp : (k : ℝ) * p ^ k < 1 := by
      have hpos := mul_pos hk0 hpk0
      nlinarith only [hh, hpos]
    have hc : 1 / (k : ℝ) ≤ (16 * (k : ℝ) - 1) * (2 / (5 * k)) ^ 2 := by
      apply (div_le_iff₀ hk0).mpr
      calc
        _ ≤ (64 * (k : ℝ) - 4) / (25 * k) :=
          (le_div_iff₀ (by positivity)).mpr (by linarith only [hK])
        _ = _ := by field_simp; ring
    have hpk : p ^ k < 1 / (k : ℝ) :=
      (lt_div_iff₀ hk0).mpr (by simpa only [mul_comm] using hkp)
    calc
      (p ^ k) ^ 3 = p ^ k * (p ^ k) ^ 2 := by ring
      _ < ((16 * (k : ℝ) - 1) * (2 / (5 * k)) ^ 2) * (p ^ k) ^ 2 :=
        mul_lt_mul_of_pos_right (hpk.trans_le hc) (pow_pos hpk0 2)
      _ = _ := by unfold scaledNibbleError; ring

theorem scaled_nibble_initial_margins {k : ℕ} (hk : 6 ≤ k) {p : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1 / 3) :
    (p ^ k) ^ 3 ≤ 1 ∧
      (p ^ k) ^ 3 < (k : ℝ) * (16 * (k : ℝ) ^ 2 - 1) * (scaledNibbleError k p) ^ 3 ∧
      (p ^ k) ^ 3 < (16 * (k : ℝ) - 1) * (scaledNibbleError k p) ^ 2 := by
  have hsmallC : (512 / 5 : ℝ) * k ≤ (3 : ℝ) ^ k := by
    have hh : 512 * (k : ℝ) ≤ 5 * (3 : ℝ) ^ k := by
      exact_mod_cast (scaled_nibble_coefficient_bounds hk).1
    linarith only [hh]
  exact scaled_nibble_initial_margins_of_small_power (by omega) hp0
    (hp.trans (by norm_num)) (nibble_coefficient_times_floor_pow_le_one hp0.le hp hsmallC)

end Arxiv2411_18291
