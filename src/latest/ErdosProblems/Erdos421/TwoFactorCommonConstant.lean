import ErdosProblems.Erdos421.NormalizedDirichletLargeValues
import ErdosProblems.Erdos421.TwoFactorPowerParameters

/-! # A common logarithmic factor for the two-polynomial large-value argument -/

namespace Erdos421

noncomputable def twoFactorSampleConstant (k : ℕ) : ℝ :=
  1 + dirichletNormalizedMeanConstant 1 + dirichletNormalizedHalaszConstant 1 +
    dirichletNormalizedMeanConstant k + dirichletNormalizedHalaszConstant k

def twoFactorSampleExponent (k : ℕ) : ℕ := 3 * k ^ 2 + 8

noncomputable def twoFactorSampleWeight (k : ℕ) (L : ℝ) : ℝ :=
  twoFactorSampleConstant k * L ^ twoFactorSampleExponent k

theorem twoFactorSampleConstant_bounds (k : ℕ) :
    0 < twoFactorSampleConstant k ∧
      dirichletNormalizedMeanConstant 1 ≤ twoFactorSampleConstant k ∧
      dirichletNormalizedHalaszConstant 1 ≤ twoFactorSampleConstant k ∧
      dirichletNormalizedMeanConstant k ≤ twoFactorSampleConstant k ∧
      dirichletNormalizedHalaszConstant k ≤ twoFactorSampleConstant k := by
  have h1 := dirichletNormalizedMeanConstant_pos 1
  have h2 := dirichletNormalizedHalaszConstant_pos 1
  have h3 := dirichletNormalizedMeanConstant_pos k
  have h4 := dirichletNormalizedHalaszConstant_pos k
  dsimp only [twoFactorSampleConstant]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem twoFactorSampleWeight_bounds {k : ℕ} (hk : 1 ≤ k) {L : ℝ} (hL : 1 ≤ L) :
    0 < twoFactorSampleWeight k L ∧
      dirichletNormalizedMeanConstant 1 * L ^ 4 ≤ twoFactorSampleWeight k L ∧
      dirichletNormalizedHalaszConstant 1 * L ^ 11 ≤ twoFactorSampleWeight k L ∧
      dirichletNormalizedMeanConstant k * L ^ (k ^ 2 + 3) ≤ twoFactorSampleWeight k L ∧
      dirichletNormalizedHalaszConstant k * L ^ (3 * k ^ 2 + 8) ≤ twoFactorSampleWeight k L := by
  obtain ⟨hC, h1, h2, h3, h4⟩ := twoFactorSampleConstant_bounds k
  have hLp : 0 < L := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk
  refine ⟨mul_pos hC (pow_pos hLp _), ?_, ?_, ?_, ?_⟩
  · exact mul_le_mul h1 (pow_le_pow_right₀ hL (by dsimp only [twoFactorSampleExponent]; omega))
      (pow_nonneg hLp.le _) hC.le
  · exact mul_le_mul h2 (pow_le_pow_right₀ hL (by dsimp only [twoFactorSampleExponent]; omega))
      (pow_nonneg hLp.le _) hC.le
  · exact mul_le_mul h3 (pow_le_pow_right₀ hL (by dsimp only [twoFactorSampleExponent]; omega))
      (pow_nonneg hLp.le _) hC.le
  · exact mul_le_mul_of_nonneg_right h4 (pow_nonneg hLp.le _)

theorem scaled_largeValue_inequality {R C a b : ℝ} (hC : 0 < C) (h : R * a ≤ C * b) :
    (R / C) * a ≤ b := by
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)

theorem twoFactor_scaled_power_range_saving {X u w R M H T η e d C : ℝ}
    (hX : 1 ≤ X) (hu : 0 ≤ u) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hT : 0 ≤ T) (hC : 0 < C) (hprod : M * H = X)
    {k : ℕ} (hk : 5 ≤ k) (he : 0 ≤ e) (hd : d ≤ e / 2) (hd' : d ≤ 1 / (60 * k))
    (hHlo : X ^ (1 / ((k : ℝ) + 1)) ≤ H) (hHhi : H ≤ X ^ (1 / (k : ℝ)))
    (hThi : T ≤ X ^ (9 / 10 - e)) (hη : X ^ (-d) ≤ η)
    (huM : u ≤ M) (hwH : w ≤ η ^ 2 * H)
    (hmeanM : R * u ≤ C * (M + T))
    (hhalaszM : R * u ^ 3 ≤ C * (M * u ^ 2 + M * T))
    (hmeanH : R * w ^ k ≤ C * (H ^ k + T))
    (hhalaszH : R * w ^ (3 * k) ≤ C * (H ^ k * w ^ (2 * k) + H ^ k * T)) :
    R * u * w ≤ 2 * C * η * X := by
  have hb := twoFactor_power_range_saving hX hu hw (div_nonneg hR hC.le) hM hH hT hprod
    hk he hd hd' hHlo hHhi hThi hη huM hwH
    (scaled_largeValue_inequality hC hmeanM) (scaled_largeValue_inequality hC hhalaszM)
    (scaled_largeValue_inequality hC hmeanH) (scaled_largeValue_inequality hC hhalaszH)
  have hidentity : u * w * (R / C) = (R * u * w) / C := by ring
  rw [hidentity] at hb
  exact ((div_le_iff₀ hC).mp hb).trans_eq (by ring)

end Erdos421
