import ErdosProblems.Erdos421.LogPolynomialUniform
import ErdosProblems.Erdos421.ZetaScaleSaving

/-! # A finite family of reciprocal-power factor-length bands -/

namespace Erdos421

noncomputable def primeFactorMaxMoment (δ : ℝ) : ℕ := max 5 ⌈δ⁻¹⌉₊

theorem primeFactorMaxMoment_ge_five (δ : ℝ) : 5 ≤ primeFactorMaxMoment δ := le_max_left _ _

theorem exists_factor_length_band {δ X H : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X)
    (hHlo : X ^ δ ≤ H) (hHhi : H ≤ X ^ (1 / 5 : ℝ)) :
    ∃ k : ℕ, 5 ≤ k ∧ k ≤ primeFactorMaxMoment δ ∧
      X ^ (1 / ((k : ℝ) + 1)) ≤ H ∧ H ≤ X ^ (1 / (k : ℝ)) := by
  let K := primeFactorMaxMoment δ
  have hXp : 0 < X := by linarith
  have hHp : 0 < H := (Real.rpow_pos_of_pos hXp δ).trans_le hHlo
  have hR : 1 ≤ δ * ((K : ℝ) + 1) := by
    have hc : δ⁻¹ ≤ (K : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈δ⁻¹⌉₊ ≤ K from le_max_right _ _))
    have hm := mul_le_mul_of_nonneg_left hc hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at hm
    linarith
  have hpow5 : H ^ 5 ≤ X := by
    have hb := pow_le_pow_left₀ hHp.le hHhi 5
    rw [← Real.rpow_mul_natCast hXp.le,
      show (1 / 5 : ℝ) * ((5 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at hb
    exact hb
  have htop : X ≤ H ^ (K + 1) := power_length_frequency_upper hX hHlo hR
  obtain ⟨k, hk, hkK, hl, hu⟩ := exists_integer_power_band
    (primeFactorMaxMoment_ge_five δ) hpow5 htop
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hks : (0 : ℝ) < k + 1 := by positivity
  refine ⟨k, hk, hkK, ?_, ?_⟩
  · have hb := Real.rpow_le_rpow hXp.le hu (by positivity : 0 ≤ 1 / ((k : ℝ) + 1))
    have he : (H ^ (k + 1)) ^ (1 / ((k : ℝ) + 1)) = H := by
      rw [← Real.rpow_natCast H (k + 1), ← Real.rpow_mul hHp.le]
      have hmul : ((k + 1 : ℕ) : ℝ) * (1 / ((k : ℝ) + 1)) = 1 := by
        push_cast
        field_simp
      rw [hmul, Real.rpow_one]
    rwa [he] at hb
  · have hb := Real.rpow_le_rpow (pow_nonneg hHp.le k) hl (by positivity : 0 ≤ 1 / (k : ℝ))
    have he : (H ^ k) ^ (1 / (k : ℝ)) = H := by
      rw [← Real.rpow_natCast H k, ← Real.rpow_mul hHp.le,
        mul_one_div_cancel hkp.ne', Real.rpow_one]
    rwa [he] at hb

end Erdos421
