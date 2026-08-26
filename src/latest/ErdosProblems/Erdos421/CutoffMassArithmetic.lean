import ErdosProblems.Erdos421.LogarithmicPrimePartition
import ErdosProblems.Erdos421.LogWindowScales

/-! # Numerical bounds for the total mass lost when freezing prime cutoffs -/

namespace Erdos421

theorem harmonic_cast_one_le {B : ℕ} (hB : 1 ≤ B) : 1 ≤ (harmonic B : ℝ) := by
  have h := harmonic_cast_mono hB
  have h1 : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic]
  rwa [h1] at h

theorem harmonic_cast_le_three_log {B : ℕ} (hB : 0 < B) {X : ℝ} (hX : 0 < X)
    (hBX : (B : ℝ) ≤ 4 * X) (hlog : 1 ≤ Real.log X) (hlog4 : Real.log 4 ≤ Real.log X) :
    (harmonic B : ℝ) ≤ 3 * Real.log X := by
  have hh := harmonic_le_one_add_log B
  have hb := Real.log_le_log (by exact_mod_cast hB) hBX
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hX.ne'] at hb
  linarith

theorem clipped_cutoff_mass_numeric {W B : ℕ} {X β : ℝ} (hX : 0 < X)
    (hW : X ^ β ≤ W) (hB : 0 < B) (hBX : (B : ℝ) ≤ 4 * X)
    (hlog : 1 ≤ Real.log X) (hlog4 : Real.log 4 ≤ Real.log X) :
    ((primePartitionCount X : ℝ)⁻¹ + 2 / (W : ℝ)) * (harmonic B : ℝ) ^ 3 ≤
      27 / (Real.log X) ^ (7 : ℕ) + 54 * X ^ (-β) * (Real.log X) ^ (3 : ℕ) := by
  have hL : 0 < Real.log X := by linarith
  have hWi : (W : ℝ)⁻¹ ≤ X ^ (-β) := by
    rw [Real.rpow_neg hX.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hX β) hW
  have hgamma : (primePartitionCount X : ℝ)⁻¹ + 2 / (W : ℝ) ≤
      ((Real.log X) ^ (10 : ℕ))⁻¹ + 2 * X ^ (-β) := by
    rw [div_eq_mul_inv]
    exact add_le_add (primePartitionCount_inv_le hlog)
      (mul_le_mul_of_nonneg_left hWi (by norm_num))
  have hH0 : (0 : ℝ) ≤ harmonic B :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (harmonic_cast_one_le hB)
  have hHp := pow_le_pow_left₀ hH0 (harmonic_cast_le_three_log hB hX hBX hlog hlog4) 3
  calc
    _ ≤ (((Real.log X) ^ (10 : ℕ))⁻¹ + 2 * X ^ (-β)) * (3 * Real.log X) ^ 3 :=
      mul_le_mul hgamma hHp (pow_nonneg hH0 _) (by positivity)
    _ = _ := by field_simp; ring

end Erdos421
