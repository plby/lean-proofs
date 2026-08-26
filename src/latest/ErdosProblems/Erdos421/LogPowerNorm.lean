import ErdosProblems.Erdos421.LogUniformPower

/-! # Norm form of the uniform logarithmic-sum estimate -/

namespace Erdos421

noncomputable def logarithmicPowerSaving (M R K : ℕ) : ℝ :=
  (2 * logarithmicDifferenceConstant R / (M : ℝ) ^ ((K : ℝ)⁻¹)) ^
    (((2 ^ R : ℕ) : ℝ)⁻¹)

theorem logarithmicPowerSaving_pos {M : ℕ} (hM : 0 < M) (R K : ℕ) :
    0 < logarithmicPowerSaving M R K := by
  unfold logarithmicPowerSaving
  exact Real.rpow_pos_of_pos
    (div_pos (mul_pos (by norm_num) (logarithmicDifferenceConstant_pos R))
      (Real.rpow_pos_of_pos (by exact_mod_cast hM) _)) _

/-- Uniform norm control for every initial subinterval of a dyadic block. -/
theorem logarithmicSum_uniform_norm_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) {τ : ℝ}
    (hlo : (M : ℝ) ^ (2 / (K : ℝ)) ≤ |τ|) (hhi : |τ| ≤ (M : ℝ) ^ (R + 1)) :
    ‖logarithmicSum M N τ‖ ≤ 4 * M * logarithmicPowerSaving M R K := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := logarithmicSum_uniform_abs_power_bound hM hN R K hK hlo hhi
  have he : (2 ^ R : ℕ) ≠ 0 := by positivity
  have hroot := Real.rpow_le_rpow (by positivity) hb
    (by positivity : (0 : ℝ) ≤ (((2 ^ R : ℕ) : ℝ)⁻¹))
  rw [Real.pow_rpow_inv_natCast (by positivity) he] at hroot
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * M)).mp hroot |>.trans_eq
    (by unfold logarithmicPowerSaving; ring)

end Erdos421
