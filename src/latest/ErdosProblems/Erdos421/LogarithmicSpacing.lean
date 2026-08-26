import ErdosProblems.Erdos421.LogarithmicSums

/-! # Quantitative decrease of logarithmic phase increments -/

namespace Erdos421

theorem log_increment_drop_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) / (y * (x + 1)) ≤
      (Real.log (x + 1) - Real.log x) - (Real.log (y + 1) - Real.log y) := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · simp
  have hy := hx.trans hxy
  have hinv : 1 + y⁻¹ < 1 + x⁻¹ :=
    add_lt_add_of_le_of_lt le_rfl ((inv_lt_inv₀ hy hx).mpr hxy)
  have h := log_difference_lower (by positivity : 0 < 1 + y⁻¹) hinv
  rw [log_increment_eq hx, log_increment_eq hy]
  have heq : ((1 + x⁻¹) - (1 + y⁻¹)) / (1 + x⁻¹) = (y - x) / (y * (x + 1)) := by
    have hx1 : x + 1 ≠ 0 := by linarith
    have hinvpos : 1 + x⁻¹ ≠ 0 := by positivity
    field_simp
    ring
  rwa [heq] at h

theorem log_increment_drop_lower_bounded {x y B : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyB : y + 1 ≤ B) :
    (y - x) / B ^ 2 ≤
      (Real.log (x + 1) - Real.log x) - (Real.log (y + 1) - Real.log y) := by
  have hy := hx.trans_le hxy
  have hden : 0 < y * (x + 1) := by positivity
  have hB : 0 < B := by linarith
  have hmul : y * (x + 1) ≤ B ^ 2 := by nlinarith
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hden hmul).trans
    (log_increment_drop_lower hx hxy)

theorem logarithmic_phase_increment_spacing {M N i j : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) (hij : i ≤ j) (hj : j ≤ N) :
    (τ / (M + N + 1 : ℝ) ^ 2) * ((j : ℝ) - i) ≤
      phaseIncrement (fun n ↦ τ * Real.log (M + n : ℕ)) i -
        phaseIncrement (fun n ↦ τ * Real.log (M + n : ℕ)) j := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hxy : (M : ℝ) + i ≤ M + j := by exact_mod_cast Nat.add_le_add_left hij M
  have hyB : (M : ℝ) + j + 1 ≤ M + N + 1 := by
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hj M) 1
  have h := log_increment_drop_lower_bounded (by positivity : (0 : ℝ) < M + i) hxy hyB
  have hm := mul_le_mul_of_nonneg_left h hτ
  simp only [phaseIncrement, Nat.cast_add, Nat.cast_one, ← add_assoc]
  calc
    _ = τ * (((M : ℝ) + j - (M + i)) / (M + N + 1 : ℝ) ^ 2) := by ring
    _ ≤ τ * ((Real.log ((M : ℝ) + i + 1) - Real.log ((M : ℝ) + i)) -
        (Real.log ((M : ℝ) + j + 1) - Real.log ((M : ℝ) + j))) := hm
    _ = _ := by ring

end Erdos421
