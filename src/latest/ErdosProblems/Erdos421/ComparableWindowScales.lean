import ErdosProblems.Erdos421.LogWindowScales

/-! # Comparing window parameters at nearby product scales -/

namespace Erdos421

open Filter Topology

theorem eventually_constant_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ X : ℕ in atTop, C * (X : ℝ) ^ a ≤ (X : ℝ) ^ b := by
  have hlim : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C, eventually_ge_atTop 1] with X hlarge hX
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    _ ≤ (X : ℝ) ^ (b - a) * (X : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hXp.le _)
    _ = _ := by rw [← Real.rpow_add hXp, sub_add_cancel]

theorem comparable_log_bounds {X T : ℝ} (hX : 0 < X) (hXT : X / 4 ≤ T) (hTX : T ≤ 3 * X)
    (hLX4 : 2 * Real.log 4 ≤ Real.log X) (hLX3 : Real.log 3 ≤ Real.log X) :
    Real.log X / 2 ≤ Real.log T ∧ Real.log T ≤ 2 * Real.log X := by
  have hTp : 0 < T := (div_pos hX (by norm_num : (0 : ℝ) < 4)).trans_le hXT
  have hlo := Real.log_le_log (div_pos hX (by norm_num : (0 : ℝ) < 4)) hXT
  rw [Real.log_div hX.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hlo
  have hhi := Real.log_le_log hTp hTX
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hX.ne'] at hhi
  constructor <;> linarith

theorem comparable_short_window_lower {X T d : ℝ} (hX : 0 < X) (hT : 0 < T)
    (hXT : X ≤ 4 * T) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    4 * Real.pi / T ^ d ≤ 16 * Real.pi / X ^ d := by
  have hpow : X ^ d ≤ 4 * T ^ d := by
    calc
      _ ≤ (4 * T) ^ d := Real.rpow_le_rpow hX.le hXT hd
      _ = (4 : ℝ) ^ d * T ^ d := Real.mul_rpow (by norm_num) hT.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 4) hd1)
        (Real.rpow_nonneg hT.le _)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hT d) (Real.rpow_pos_of_pos hX d)).mpr
  have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4 * Real.pi)
  nlinarith

theorem comparable_inverse_log_window {L R B : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hB : 0 ≤ B) (hRL : R ≤ 2 * L) (hlarge : (2 : ℝ) ^ B ≤ L) :
    L ^ (-(B + 1)) ≤ R ^ (-B) := by
  have hpow : R ^ B ≤ L ^ (B + 1) := by
    calc
      _ ≤ (2 * L) ^ B := Real.rpow_le_rpow hR.le hRL hB
      _ = (2 : ℝ) ^ B * L ^ B := Real.mul_rpow (by norm_num) hL.le
      _ ≤ L * L ^ B := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]; ring
  rw [Real.rpow_neg hL.le, Real.rpow_neg hR.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hR _) hpow

theorem comparable_inverse_log_power {L R A : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hA : 0 ≤ A) (hLR : L / 2 ≤ R) : 1 / R ^ A ≤ (2 : ℝ) ^ A / L ^ A := by
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ L / 2) hLR hA
  rw [Real.div_rpow hL.le (by norm_num)] at hp
  have hm := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) A)).mp hp
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hR A) (Real.rpow_pos_of_pos hL A)).mpr
  simpa only [one_mul, mul_one, mul_comm] using hm

end Erdos421
