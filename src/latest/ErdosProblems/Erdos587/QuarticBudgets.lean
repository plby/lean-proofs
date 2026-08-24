import Mathlib

/-! Algebraic fourth-power tests for the analytic size hypotheses. -/

namespace Erdos587

lemma quarter_weight_pow_four {T Λ : ℝ} (hT : 0 ≤ T) (B : ℕ) :
    (T ^ (1 / 4 : ℝ) * Λ ^ B) ^ 4 = T * Λ ^ (4 * B) := by
  have hroot : (T ^ (1 / 4 : ℝ)) ^ 4 = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT]
    norm_num
  rw [mul_pow, hroot, ← pow_mul, Nat.mul_comm B 4]

lemma three_quarter_weight_pow_four {T Λ : ℝ} (hT : 0 ≤ T) (B : ℕ) :
    (T ^ (3 / 4 : ℝ) * Λ ^ B) ^ 4 = T ^ 3 * Λ ^ (4 * B) := by
  have hroot : (T ^ (3 / 4 : ℝ)) ^ 4 = T ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT]
    norm_num
  rw [mul_pow, hroot, ← pow_mul, Nat.mul_comm B 4]

lemma quarter_weight_le_of_budget {T Λ F H L : ℝ} (B : ℕ)
    (hT : 0 ≤ T) (hΛ : 0 ≤ Λ) (hF : 0 < F) (hL : 0 ≤ L)
    (hbudget : F ^ 4 * T * Λ ^ (4 * B) ≤ H ^ 4)
    (hH : 0 ≤ H) (hside : H ≤ F * L) :
    T ^ (1 / 4 : ℝ) * Λ ^ B ≤ L := by
  apply (mul_le_mul_iff_right₀ hF).mp
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
  calc
    (F * (T ^ (1 / 4 : ℝ) * Λ ^ B)) ^ 4 = F ^ 4 * T * Λ ^ (4 * B) := by
      rw [mul_pow, quarter_weight_pow_four hT]
      ring
    _ ≤ H ^ 4 := hbudget
    _ ≤ (F * L) ^ 4 := pow_le_pow_left₀ hH hside 4

lemma three_quarter_weight_le_of_budget {T Λ D H L : ℝ} (B : ℕ)
    (hT : 0 ≤ T) (hΛ : 0 ≤ Λ) (hD : 0 < D) (hL : 0 ≤ L)
    (hbudget : D ^ 4 * T ^ 3 * Λ ^ (4 * B) ≤ H ^ 12)
    (hH : 0 ≤ H) (harea : H ^ 3 ≤ D * L) :
    T ^ (3 / 4 : ℝ) * Λ ^ B ≤ L := by
  apply (mul_le_mul_iff_right₀ hD).mp
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
  calc
    (D * (T ^ (3 / 4 : ℝ) * Λ ^ B)) ^ 4 = D ^ 4 * T ^ 3 * Λ ^ (4 * B) := by
      rw [mul_pow, three_quarter_weight_pow_four hT]
      ring
    _ ≤ H ^ 12 := hbudget
    _ = (H ^ 3) ^ 4 := by ring
    _ ≤ (D * L) ^ 4 := pow_le_pow_left₀ (by positivity) harea 4

end Erdos587
