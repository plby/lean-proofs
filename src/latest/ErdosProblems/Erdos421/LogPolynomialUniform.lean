import ErdosProblems.Erdos421.LogConstantBounds
import ErdosProblems.Erdos421.DifferenceConstants

/-! # Uniform logarithmic cancellation with polynomial degree dependence -/

namespace Erdos421

noncomputable def polynomialLogarithmicExponent (K : ℕ) : ℝ :=
  (((65536 * (K + 1) ^ 3 : ℕ) : ℝ))⁻¹

noncomputable def polynomialLogarithmicConstant (K : ℕ) : ℝ :=
  (2 : ℝ) ^ (1728 * (K + 1) ^ 11)

theorem polynomialLogarithmicExponent_pos (K : ℕ) :
    0 < polynomialLogarithmicExponent K := by
  unfold polynomialLogarithmicExponent
  positivity

theorem polynomialLogarithmicConstant_pos (K : ℕ) :
    0 < polynomialLogarithmicConstant K := by
  unfold polynomialLogarithmicConstant
  positivity

theorem polynomialLogarithmicExponent_le_half (K : ℕ) :
    polynomialLogarithmicExponent K ≤ 1 / 2 := by
  unfold polynomialLogarithmicExponent
  have hden : (2 : ℝ) ≤ ((65536 * (K + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 65536 * (K + 1) ^ 3 by
      nlinarith [Nat.one_le_pow 3 (K + 1) (by omega)])
  simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hden

theorem exists_integer_power_band {A t : ℝ} {a b : ℕ} (hab : a ≤ b)
    (hlo : A ^ a ≤ t) (hhi : t ≤ A ^ (b + 1)) :
    ∃ k, a ≤ k ∧ k ≤ b ∧ A ^ k ≤ t ∧ t ≤ A ^ (k + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_rfl, le_rfl, hlo, hhi⟩
  | succ b hab ih =>
    by_cases ht : t ≤ A ^ (b + 1)
    · obtain ⟨k, hk, hkb, hl, hu⟩ := ih ht
      exact ⟨k, hk, by omega, hl, hu⟩
    · exact ⟨b + 1, by omega, le_rfl, (lt_of_not_ge ht).le, hhi⟩

theorem polynomialLogarithmicExponent_le_meanValue {k K : ℕ}
    (hk : 0 < k) (hkK : k ≤ K) :
    polynomialLogarithmicExponent K ≤ 1 / (4 * (((2 * K ^ 2 + 1) * k : ℕ) : ℝ)) := by
  have hp : (0 : ℝ) < 4 * (((2 * K ^ 2 + 1) * k : ℕ) : ℝ) := by positivity
  have hden : 4 * (((2 * K ^ 2 + 1) * k : ℕ) : ℝ) ≤
      ((65536 * (K + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 4 * ((2 * K ^ 2 + 1) * k) ≤ 65536 * (K + 1) ^ 3 from
      (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (2 * K ^ 2 + 1) hkK)).trans
        (by nlinarith))
  simpa only [polynomialLogarithmicExponent, one_div] using inv_anti₀ hp hden

theorem meanValue_log_condition_uniform {k K : ℕ} (hkK : k ≤ K) :
    2 * (k : ℝ) * Real.log k ≤ (2 * K ^ 2 : ℕ) := by
  calc
    _ ≤ 2 * (k : ℝ) * k :=
      mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg k)) (by positivity)
    _ ≤ 2 * (K : ℝ) * K := by gcongr
    _ = _ := by push_cast; ring

/-- The mean-value estimate is uniform across all the high-frequency bands.
Both the saving and the logarithm of the constant depend polynomially on `K`. -/
theorem logarithmicSum_high_frequency_polynomial_bound {M N K : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hK : 12 ≤ K) {t : ℝ}
    (hlo : (M : ℝ) ^ 11 ≤ |t|) (hhi : |t| ≤ (M : ℝ) ^ K) :
    ‖logarithmicSum M N t‖ ≤ polynomialLogarithmicConstant K *
      (M : ℝ) ^ (1 - polynomialLogarithmicExponent K) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨j, hj, hjK, hl, hu⟩ := exists_integer_power_band (by omega : 11 ≤ K - 1)
    hlo (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ K)] using hhi)
  have hk : 12 ≤ j + 1 := by omega
  have hkK : j + 1 ≤ K := by omega
  have hb := logarithmicSum_meanValue_power_saving hk hM hN (2 * K ^ 2)
    (meanValue_log_condition_uniform hkK) (by simpa only [Nat.add_sub_cancel] using hl) hu
  have hc := logarithmicPowerConstant_uniform_bound (by omega : 0 < j + 1) hkK le_rfl
  have he := polynomialLogarithmicExponent_le_meanValue (by omega : 0 < j + 1) hkK
  exact hb.trans (mul_le_mul hc
    (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)) (by positivity)
    (polynomialLogarithmicConstant_pos K).le)

theorem polynomialLogarithmicExponent_le_difference (K : ℕ) :
    polynomialLogarithmicExponent K ≤ logarithmicSavingExponent 10 26 := by
  have hden : (26624 : ℝ) ≤ ((65536 * (K + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 26624 ≤ 65536 * (K + 1) ^ 3 by
      nlinarith [Nat.one_le_pow 3 (K + 1) (by omega)])
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 26624) hden
  rw [show logarithmicSavingExponent 10 26 = (26624 : ℝ)⁻¹ by
    norm_num [logarithmicSavingExponent]]
  exact h

theorem polynomialLogarithmicConstant_ge_difference (K : ℕ) :
    4 * logarithmicSavingConstant 10 ≤ polynomialLogarithmicConstant K := by
  calc
    _ ≤ 4 * 4096 := mul_le_mul_of_nonneg_left (logarithmicSavingConstant_le 10) (by norm_num)
    _ = (2 : ℝ) ^ 14 := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
      (show 14 ≤ 1728 * (K + 1) ^ 11 by nlinarith [Nat.one_le_pow 11 (K + 1) (by omega)])

/-- A single estimate for every prefix and either sign, from the fourth-root
frequency threshold to arbitrary polynomial height. -/
theorem logarithmicSum_polynomial_uniform_bound {M N K : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hK : 12 ≤ K) {t : ℝ}
    (hlo : (M : ℝ) ^ (1 / 4 : ℝ) ≤ |t|) (hhi : |t| ≤ (M : ℝ) ^ K) :
    ‖logarithmicSum M N t‖ ≤ polynomialLogarithmicConstant K *
      (M : ℝ) ^ (1 - polynomialLogarithmicExponent K) := by
  by_cases ht : (M : ℝ) ^ 11 ≤ |t|
  · exact logarithmicSum_high_frequency_polynomial_bound hM hN hK ht hhi
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlow : (M : ℝ) ^ (2 / (26 : ℝ)) ≤ |t| :=
    (Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num : 2 / (26 : ℝ) ≤ 1 / 4)).trans hlo
  have hb := logarithmicSum_uniform_norm_bound hM hN 10 26 (by norm_num)
    hlow (lt_of_not_ge ht).le
  rw [logarithmicPowerSaving_eq hM] at hb
  have he : 4 * (M : ℝ) * (logarithmicSavingConstant 10 /
      (M : ℝ) ^ logarithmicSavingExponent 10 26) =
      (4 * logarithmicSavingConstant 10) *
        (M : ℝ) ^ (1 - logarithmicSavingExponent 10 26) := by
    rw [Real.rpow_sub hMp, Real.rpow_one]
    ring
  rw [he] at hb
  exact hb.trans (mul_le_mul (polynomialLogarithmicConstant_ge_difference K)
    (Real.rpow_le_rpow_of_exponent_le hM1
      (sub_le_sub_left (polynomialLogarithmicExponent_le_difference K) 1))
    (by positivity) (polynomialLogarithmicConstant_pos K).le)

end Erdos421
