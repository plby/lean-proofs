import ErdosProblems.Erdos421.LogPowerNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Explicit exponents and logarithmic decay of the power saving -/

namespace Erdos421

open Filter Topology

noncomputable def logarithmicSavingExponent (R K : ℕ) : ℝ :=
  ((K : ℝ) * ((2 ^ R : ℕ) : ℝ))⁻¹

noncomputable def logarithmicSavingConstant (R : ℕ) : ℝ :=
  (2 * logarithmicDifferenceConstant R) ^ (((2 ^ R : ℕ) : ℝ)⁻¹)

theorem logarithmicSavingExponent_pos (R : ℕ) {K : ℕ} (hK : 0 < K) :
    0 < logarithmicSavingExponent R K := by
  unfold logarithmicSavingExponent
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  positivity

theorem logarithmicSavingConstant_pos (R : ℕ) : 0 < logarithmicSavingConstant R := by
  unfold logarithmicSavingConstant
  exact Real.rpow_pos_of_pos (mul_pos (by norm_num) (logarithmicDifferenceConstant_pos R)) _

theorem logarithmicPowerSaving_eq {M : ℕ} (hM : 0 < M) (R K : ℕ) :
    logarithmicPowerSaving M R K = logarithmicSavingConstant R /
      (M : ℝ) ^ (logarithmicSavingExponent R K) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hc := logarithmicDifferenceConstant_pos R
  unfold logarithmicPowerSaving logarithmicSavingConstant logarithmicSavingExponent
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hMp.le]
  congr 2
  rw [mul_inv]

/-- Any fixed logarithmic factor is smaller than the proved power saving. -/
theorem logarithmicPowerSaving_mul_log_tendsto (R : ℕ) {K : ℕ} (hK : 0 < K) (A : ℝ) :
    Tendsto (fun M : ℕ ↦ logarithmicPowerSaving M R K * (Real.log M) ^ A)
      atTop (𝓝 0) := by
  have hδ := logarithmicSavingExponent_pos R hK
  have hlim := (isLittleO_log_rpow_rpow_atTop A hδ).tendsto_div_nhds_zero
  have hnat : Tendsto (fun M : ℕ ↦ (Real.log (M : ℝ)) ^ A /
      (M : ℝ) ^ (logarithmicSavingExponent R K)) atTop (𝓝 0) :=
    hlim.comp tendsto_natCast_atTop_atTop
  have hc := hnat.const_mul (logarithmicSavingConstant R)
  simp only [mul_zero] at hc
  apply hc.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [logarithmicPowerSaving_eq (by omega) R K]
  ring

end Erdos421
