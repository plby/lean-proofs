import ErdosProblems.Erdos67b.MRRelativeEnergyBudget

/-! # Exact logarithmic parameters for the quantitative MRT schedule -/

namespace Erdos67b

noncomputable section

def mrtLogPowerWindow (L : ℝ) : ℝ := Real.exp (1024 * Real.log L)

def mrtLogPowerLower (L : ℝ) : ℝ := 204800 * Real.log L

def mrtLogPowerUpper (L : ℝ) : ℝ := L - 3072 * Real.log L

def mrtLogPowerCutoff (L : ℝ) : ℝ := Real.exp (10240 * Real.log L - L)

theorem mrtLogPowerWindow_pos (L : ℝ) : 0 < mrtLogPowerWindow L := Real.exp_pos _

theorem mrtLogPowerCutoff_pos (L : ℝ) : 0 < mrtLogPowerCutoff L := Real.exp_pos _

theorem mrtLogPowerWindow_one_le {L : ℝ} (hL : 1 ≤ L) : 1 ≤ mrtLogPowerWindow L := by
  apply Real.one_le_exp_iff.2
  exact mul_nonneg (by norm_num) (Real.log_nonneg hL)

theorem mrtLogPowerWindow_pow (L : ℝ) (k : ℕ) :
    mrtLogPowerWindow L ^ k = Real.exp ((k : ℝ) * 1024 * Real.log L) := by
  unfold mrtLogPowerWindow
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem mrtLogPowerWindow_eq_pow {L : ℝ} (hL : 0 < L) :
    mrtLogPowerWindow L = L ^ (1024 : ℕ) := by
  unfold mrtLogPowerWindow
  rw [show (1024 : ℝ) * Real.log L = (1024 : ℕ) * Real.log L by norm_num,
    Real.exp_nat_mul, Real.exp_log hL]

theorem mrtLogPowerWindow_log (L : ℝ) :
    Real.log (mrtLogPowerWindow L) = 1024 * Real.log L := Real.log_exp _

theorem mrtLogPower_exp_lower (L : ℝ) :
    Real.exp (mrtLogPowerLower L) = mrtLogPowerWindow L ^ 200 := by
  rw [mrtLogPowerWindow_pow]
  unfold mrtLogPowerLower
  norm_num

theorem mrtLogPower_exp_upper (L : ℝ) :
    Real.exp (mrtLogPowerUpper L) = Real.exp L / mrtLogPowerWindow L ^ 3 := by
  rw [mrtLogPowerWindow_pow]
  unfold mrtLogPowerUpper
  rw [Real.exp_sub]
  norm_num

theorem mrtLogPowerCutoff_eq (L : ℝ) :
    mrtLogPowerCutoff L = mrtLogPowerWindow L ^ 10 / Real.exp L := by
  rw [mrtLogPowerWindow_pow]
  unfold mrtLogPowerCutoff
  rw [Real.exp_sub]
  norm_num

theorem mrtLogPowerCutoff_mul_exp_upper (L : ℝ) :
    mrtLogPowerCutoff L * Real.exp (mrtLogPowerUpper L) = mrtLogPowerWindow L ^ 7 := by
  rw [mrtLogPowerWindow_pow]
  unfold mrtLogPowerCutoff mrtLogPowerUpper
  rw [← Real.exp_add]
  congr 1
  ring

end

end Erdos67b
