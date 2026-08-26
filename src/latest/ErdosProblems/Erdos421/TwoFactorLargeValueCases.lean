import ErdosProblems.Erdos421.TwoFactorPowerIdentities

/-! # The four elementary cases of two-factor large-value interpolation -/

namespace Erdos421

theorem largeValue_remove_diagonal {R u M T : ℝ}
    (hmean : R * u ≤ M + T) (hhalasz : R * u ^ 3 ≤ M * u ^ 2 + M * T)
    (hlarge : 2 * M < R * u) : R * u ≤ 2 * T ∧ R * u ^ 3 ≤ 2 * M * T := by
  have hmul := mul_le_mul_of_nonneg_right hlarge.le (sq_nonneg u)
  constructor <;> nlinarith

theorem twoFactor_case_a {u w R M H : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hH : 0 ≤ H) {k : ℕ} (hk : 1 ≤ k)
    (huM : u ≤ M) (hleft : R * u ≤ 2 * M) (hright : R * w ^ k ≤ 2 * H ^ k) :
    (u * w * R) ^ (2 * k) ≤ (2 * M) ^ (2 * k) * H ^ k * w ^ k := by
  rw [twoFactor_power_identity_a u w R hk]
  have hpow := pow_le_pow_left₀ (mul_nonneg hR hu) hleft (2 * k - 1)
  have hp := mul_le_mul hpow hright (mul_nonneg hR (pow_nonneg hw _))
    (pow_nonneg (by positivity) _)
  have hp' := mul_le_mul hp huM hu (by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hp' (pow_nonneg hw k)
  apply hfinal.trans_eq
  have he : (2 * M) ^ (2 * k) = (2 * M) ^ (2 * k - 1) * (2 * M) := by
    conv_lhs => rw [show 2 * k = (2 * k - 1) + 1 by omega, pow_succ]
  rw [he]
  ring

theorem twoFactor_case_b {u w R M T : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hT : 0 ≤ T) {k : ℕ} (hk : 2 ≤ k)
    (hleft : R * u ≤ 2 * T) (hcubic : R * u ^ 3 ≤ 2 * M * T)
    (hright : R * w ^ k ≤ 2 * T) :
    (u * w * R) ^ (2 * k) ≤ (2 * T) ^ (2 * k) * M := by
  rw [twoFactor_power_identity_b u w R hk]
  have hpow := pow_le_pow_left₀ (mul_nonneg hR hu) hleft (2 * k - 3)
  have hp := mul_le_mul hpow hcubic (mul_nonneg hR (pow_nonneg hu _))
    (pow_nonneg (by positivity) _)
  have hfinal := mul_le_mul hp
    (pow_le_pow_left₀ (mul_nonneg hR (pow_nonneg hw k)) hright 2) (sq_nonneg _) (by positivity)
  apply hfinal.trans_eq
  have he : (2 * T) ^ (2 * k) = (2 * T) ^ (2 * k - 3) * (2 * T) ^ 3 := by
    conv_lhs => rw [show 2 * k = (2 * k - 3) + 3 by omega, pow_add]
  rw [he]
  ring

theorem twoFactor_case_c {u w R M H T : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hH : 0 ≤ H) (hT : 0 ≤ T) {k : ℕ} (hk : 1 ≤ k)
    (huM : u ≤ M) (hleft : R * u ≤ 2 * M)
    (hright : R * w ^ (3 * k) ≤ 2 * H ^ k * T) :
    (u * w * R) ^ (3 * k) ≤ (2 * M) ^ (3 * k) * H ^ k * T := by
  rw [twoFactor_power_identity_c u w R hk]
  have hpow := pow_le_pow_left₀ (mul_nonneg hR hu) hleft (3 * k - 1)
  have hp := mul_le_mul hpow hright (mul_nonneg hR (pow_nonneg hw _))
    (pow_nonneg (by positivity) _)
  have hfinal := mul_le_mul hp huM hu (by positivity)
  apply hfinal.trans_eq
  have he : (2 * M) ^ (3 * k) = (2 * M) ^ (3 * k - 1) * (2 * M) := by
    conv_lhs => rw [show 3 * k = (3 * k - 1) + 1 by omega, pow_succ]
  rw [he]
  ring

theorem twoFactor_case_d {u w R M H T : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hT : 0 ≤ T) {k : ℕ} (hk : 2 ≤ k)
    (hleft : R * u ≤ 2 * T) (hcubic : R * u ^ 3 ≤ 2 * M * T)
    (hright : R * w ^ k ≤ 2 * H ^ k) :
    (u * w * R) ^ (2 * k) ≤ 2 ^ (2 * k) * M * H ^ (2 * k) * T ^ (2 * k - 2) := by
  rw [twoFactor_power_identity_b u w R hk]
  have hpow := pow_le_pow_left₀ (mul_nonneg hR hu) hleft (2 * k - 3)
  have hp := mul_le_mul hpow hcubic (mul_nonneg hR (pow_nonneg hu _))
    (pow_nonneg (by positivity) _)
  have hfinal := mul_le_mul hp
    (pow_le_pow_left₀ (mul_nonneg hR (pow_nonneg hw k)) hright 2) (sq_nonneg _) (by positivity)
  apply hfinal.trans_eq
  have htwo : (2 : ℝ) ^ (2 * k) = 2 ^ (2 * k - 3) * 2 ^ 3 := by
    conv_lhs => rw [show 2 * k = (2 * k - 3) + 3 by omega, pow_add]
  have htime : T ^ (2 * k - 2) = T ^ (2 * k - 3) * T := by
    conv_lhs => rw [show 2 * k - 2 = (2 * k - 3) + 1 by omega, pow_succ]
  have hHpow : H ^ (2 * k) = (H ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
  rw [htwo, htime, hHpow, mul_pow]
  ring

theorem twoFactor_largeValue_four_cases {u w R M H T : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hR : 0 ≤ R) (hM : 0 ≤ M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    {k : ℕ} (hk : 2 ≤ k) (huM : u ≤ M)
    (hmeanM : R * u ≤ M + T) (hhalaszM : R * u ^ 3 ≤ M * u ^ 2 + M * T)
    (hmeanH : R * w ^ k ≤ H ^ k + T)
    (hhalaszH : R * w ^ (3 * k) ≤ H ^ k * w ^ (2 * k) + H ^ k * T) :
    (u * w * R) ^ (2 * k) ≤ (2 * M) ^ (2 * k) * H ^ k * w ^ k ∨
    (u * w * R) ^ (2 * k) ≤ (2 * T) ^ (2 * k) * M ∨
    (u * w * R) ^ (3 * k) ≤ (2 * M) ^ (3 * k) * H ^ k * T ∨
    (u * w * R) ^ (2 * k) ≤ 2 ^ (2 * k) * M * H ^ (2 * k) * T ^ (2 * k - 2) := by
  by_cases hleft : R * u ≤ 2 * M
  · by_cases hright : R * w ^ k ≤ 2 * H ^ k
    · exact Or.inl (twoFactor_case_a hu hw hR hM hH (by omega) huM hleft hright)
    · have hh3 : R * (w ^ k) ^ 3 ≤ H ^ k * (w ^ k) ^ 2 + H ^ k * T := by
        simpa only [← pow_mul, Nat.mul_comm k] using hhalaszH
      have hb := (largeValue_remove_diagonal hmeanH hh3
        (lt_of_not_ge hright)).2
      have hc : R * w ^ (3 * k) ≤ 2 * H ^ k * T := by
        simpa only [← pow_mul, Nat.mul_comm k] using hb
      exact Or.inr (Or.inr (Or.inl (twoFactor_case_c hu hw hR hM hH hT
        (by omega) huM hleft hc)))
  · have hb := largeValue_remove_diagonal hmeanM hhalaszM (lt_of_not_ge hleft)
    by_cases hright : R * w ^ k ≤ 2 * H ^ k
    · exact Or.inr (Or.inr (Or.inr (twoFactor_case_d hu hw hR hM hT hk hb.1 hb.2 hright)))
    · have hh : R * w ^ k ≤ 2 * T := by linarith
      exact Or.inr (Or.inl (twoFactor_case_b hu hw hR hM hT hk hb.1 hb.2 hh))

end Erdos421
