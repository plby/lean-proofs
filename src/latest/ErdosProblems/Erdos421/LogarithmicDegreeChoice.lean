import ErdosProblems.Erdos421.ZetaPolynomialParameters

/-! # Rounding the sixteenth root of the logarithmic height -/

namespace Erdos421

theorem exists_logarithmic_degree {L : ℝ} (hL : 1 ≤ L) {K₀ : ℕ}
    (hK₀ : (K₀ : ℝ) ^ 16 ≤ L) :
    ∃ K : ℕ, K₀ ≤ K ∧ (K : ℝ) ^ 16 ≤ L ∧ L ≤ ((K : ℝ) + 1) ^ 16 ∧
      (K : ℝ) + 1 ≤ 2 * L ^ (1 / 16 : ℝ) := by
  let q : ℝ := L ^ (1 / 16 : ℝ)
  have hL0 : 0 ≤ L := by linarith
  have hq : 1 ≤ q := Real.one_le_rpow hL (by norm_num)
  have hq0 : 0 ≤ q := by linarith
  have hqpow : q ^ 16 = L := by
    simpa only [q, one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hL0 (by decide : 16 ≠ 0)
  let K : ℕ := ⌊q⌋₊
  have hKq : (K : ℝ) ≤ q := Nat.floor_le hq0
  have hqK : q ≤ (K : ℝ) + 1 := (Nat.lt_floor_add_one q).le
  have hroot : (K₀ : ℝ) ≤ q := by
    have h := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg K₀) 16) hK₀
      (by norm_num : (0 : ℝ) ≤ (16 : ℝ)⁻¹)
    have he : ((K₀ : ℝ) ^ 16) ^ ((16 : ℝ)⁻¹) = K₀ := by
      simpa only [Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast (Nat.cast_nonneg K₀) (by decide : 16 ≠ 0)
    rw [he] at h
    simpa only [q, one_div] using h
  refine ⟨K, Nat.le_floor hroot, ?_, ?_, ?_⟩
  · exact (pow_le_pow_left₀ (Nat.cast_nonneg K) hKq 16).trans_eq hqpow
  · exact hqpow ▸ pow_le_pow_left₀ hq0 hqK 16
  · change (K : ℝ) + 1 ≤ 2 * q
    linarith

theorem logarithmic_degree_width_lower {L : ℝ} (hL : 0 < L) {K : ℕ}
    (hK : (K : ℝ) + 1 ≤ 2 * L ^ (1 / 16 : ℝ)) :
    ((2 : ℝ) ^ 44)⁻¹ / L ^ (15 / 16 : ℝ) ≤
      1 / (393216000 * ((K : ℝ) + 1) ^ 15) := by
  have hx : 0 < (K : ℝ) + 1 := by positivity
  have hLp : 0 < L ^ (15 / 16 : ℝ) := Real.rpow_pos_of_pos hL _
  have hq : (L ^ (1 / 16 : ℝ)) ^ 15 = L ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    norm_num
  have hpow : ((K : ℝ) + 1) ^ 15 ≤ (32768 : ℝ) * L ^ (15 / 16 : ℝ) := by
    have h := pow_le_pow_left₀ hx.le hK 15
    rw [mul_pow, hq] at h
    norm_num only [show (2 : ℝ) ^ 15 = 32768 by norm_num] at h
    exact h
  have hden : 393216000 * ((K : ℝ) + 1) ^ 15 ≤ (2 : ℝ) ^ 44 * L ^ (15 / 16 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 393216000)
    norm_num only [show (2 : ℝ) ^ 44 = 17592186044416 by norm_num]
    nlinarith only [h, hLp]
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 < 393216000 * ((K : ℝ) + 1) ^ 15) hden
  simpa only [one_div, mul_inv, div_eq_mul_inv, one_mul] using h

end Erdos421
