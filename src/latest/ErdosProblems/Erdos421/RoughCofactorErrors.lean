import ErdosProblems.Erdos421.RoughCofactorParameters
import ErdosProblems.Erdos421.LongIntervalScale

/-! # Summing the logarithmic and quadratic errors over Buchstab cofactors -/

namespace Erdos421

theorem cofactor_log_error_le {b p A η : ℝ} (hb : 1 < b) (hp : 0 < p)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hlog : Real.log b / 2 ≤ Real.log (b / p)) :
    η * (b / p) / (Real.log (b / p)) ^ A ≤
      (η * (2 : ℝ) ^ A * b / (Real.log b) ^ A) * p⁻¹ := by
  have hLb := Real.log_pos hb
  have hLc : 0 < Real.log (b / p) := by linarith
  calc
    _ = (η * (b / p)) * (1 / (Real.log (b / p)) ^ A) := by ring
    _ ≤ (η * (b / p)) * ((2 : ℝ) ^ A / (Real.log b) ^ A) :=
      mul_le_mul_of_nonneg_left (comparable_inverse_log_power hLb hLc hA hlog)
        (mul_nonneg hη (div_nonneg (by linarith) hp.le))
    _ = _ := by ring

theorem cofactor_quadratic_error_le {a b p C : ℝ} (hb : 1 < b) (hp : 0 < p)
    (hC : 0 ≤ C) (hlog : Real.log b / 2 ≤ Real.log (b / p)) :
    C * (b / p - a / p) ^ 2 / ((b / p) * (Real.log (b / p)) ^ 2) ≤
      (4 * C * (b - a) ^ 2 / (b * (Real.log b) ^ 2)) * p⁻¹ := by
  have hbp : 0 < b := by linarith
  have hLb := Real.log_pos hb
  have hLc : 0 < Real.log (b / p) := by linarith
  have hinv : 1 / (Real.log (b / p)) ^ (2 : ℕ) ≤ 4 / (Real.log b) ^ (2 : ℕ) := by
    have h := comparable_inverse_log_power hLb hLc (by norm_num : (0 : ℝ) ≤ 2) hlog
    norm_num only [Real.rpow_ofNat] at h
    exact h
  calc
    _ = (C * (b - a) ^ 2 / (b * p)) * (1 / (Real.log (b / p)) ^ 2) := by
      field_simp
    _ ≤ (C * (b - a) ^ 2 / (b * p)) * (4 / (Real.log b) ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

theorem sum_cofactor_errors_le (P : Finset ℕ) {a b A η C R : ℝ}
    (hb : 1 < b) (hA : 0 ≤ A) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hP : ∀ p ∈ P, 0 < p ∧ Real.log b / 2 ≤ Real.log (b / p))
    (hmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ R) :
    (∑ p ∈ P, (η * (b / p) / (Real.log (b / p)) ^ A +
      C * (b / p - a / p) ^ 2 / ((b / p) * (Real.log (b / p)) ^ 2))) ≤
      (η * (2 : ℝ) ^ A * R) * b / (Real.log b) ^ A +
        (4 * C * R) * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  have hbp : 0 < b := by linarith
  have hLb := Real.log_pos hb
  let T : ℝ := η * (2 : ℝ) ^ A * b / (Real.log b) ^ A +
    4 * C * (b - a) ^ 2 / (b * (Real.log b) ^ 2)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  calc
    _ ≤ ∑ p ∈ P, T * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpr : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1
      have hl := cofactor_log_error_le hb hpr hA hη (hP p hp).2
      have hq := cofactor_quadratic_error_le (a := a) hb hpr hC (hP p hp).2
      exact (add_le_add hl hq).trans_eq (by dsimp only [T]; ring)
    _ = T * ∑ p ∈ P, (p : ℝ)⁻¹ := (Finset.mul_sum P _ T).symm
    _ ≤ T * R := mul_le_mul_of_nonneg_left hmass hT
    _ = _ := by dsimp only [T]; ring

end Erdos421
