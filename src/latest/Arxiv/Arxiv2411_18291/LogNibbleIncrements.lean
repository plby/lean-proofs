import Arxiv.Arxiv2411_18291.LogNibbleComparisons

/-! # Finite increments of the logarithmic error functions -/

namespace Arxiv2411_18291

theorem log_difference_bounds {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p) :
    (p - s) / p ≤ Real.log p - Real.log s ∧
      Real.log p - Real.log s ≤ (p - s) / s := by
  have hp := hs.trans_le hsp
  have hlo := Real.log_le_sub_one_of_pos (div_pos hs hp)
  have hhi := Real.log_le_sub_one_of_pos (div_pos hp hs)
  rw [Real.log_div hs.ne' hp.ne'] at hlo
  rw [Real.log_div hp.ne' hs.ne'] at hhi
  have h₁ : (p - s) / p = 1 - s / p := by field_simp
  have h₂ : (p - s) / s = p / s - 1 := by field_simp
  rw [h₁, h₂]
  exact ⟨by linarith only [hlo], hhi⟩

theorem nibbleLogFactor_increment_bounds (k : ℕ) {s p : ℝ}
    (hs : 0 < s) (hsp : s ≤ p) :
    k * (p - s) / p ≤ nibbleLogFactor k s - nibbleLogFactor k p ∧
      nibbleLogFactor k s - nibbleLogFactor k p ≤ k * (p - s) / s := by
  obtain ⟨hlo, hhi⟩ := log_difference_bounds hs hsp
  have hlo' := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg k (α := ℝ))
  have hhi' := mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg k (α := ℝ))
  unfold nibbleLogFactor
  simp only [div_eq_mul_inv] at hlo' hhi' ⊢
  constructor <;> nlinarith only [hlo', hhi']

theorem nibbleLogFactor_square_increment_bounds (k : ℕ) {s p : ℝ}
    (hs : 0 < s) (hsp : s ≤ p) (hp1 : p ≤ 1) :
    2 * nibbleLogFactor k p * k * (p - s) / p ≤
        (nibbleLogFactor k s) ^ 2 - (nibbleLogFactor k p) ^ 2 ∧
      (nibbleLogFactor k s) ^ 2 - (nibbleLogFactor k p) ^ 2 ≤
        2 * nibbleLogFactor k s * k * (p - s) / s := by
  have hp := hs.trans_le hsp
  have hLp := nibbleLogFactor_one_le k hp hp1
  have hLs := nibbleLogFactor_one_le k hs (hsp.trans hp1)
  obtain ⟨hlo, hhi⟩ := nibbleLogFactor_increment_bounds k hs hsp
  have hlo' := mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ 2 * nibbleLogFactor k p by positivity)
  have hhi' := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ 2 * nibbleLogFactor k s by positivity)
  have hsq := sq_nonneg (nibbleLogFactor k s - nibbleLogFactor k p)
  simp only [div_eq_mul_inv] at hlo' hhi' ⊢
  constructor <;> nlinarith only [hlo', hhi', hsq]

theorem logNibbleDegreeError_increment_bounds (k : ℕ) {s p a D : ℝ}
    (hs : 0 < s) (hsp : s ≤ p) (hD : 0 ≤ D) :
    3 * k * a ^ 2 * D * (p - s) / p ≤
        logNibbleDegreeError k a D s - logNibbleDegreeError k a D p ∧
      logNibbleDegreeError k a D s - logNibbleDegreeError k a D p ≤
        3 * k * a ^ 2 * D * (p - s) / s := by
  obtain ⟨hlo, hhi⟩ := nibbleLogFactor_increment_bounds k hs hsp
  have hlo' := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 3 * a ^ 2 * D by positivity)
  have hhi' := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 3 * a ^ 2 * D by positivity)
  unfold logNibbleDegreeError
  simp only [div_eq_mul_inv] at hlo' hhi' ⊢
  constructor <;> nlinarith only [hlo', hhi']

theorem logNibbleCliqueError_increment_bounds (k : ℕ) {s p a D g : ℝ}
    (hs : 0 < s) (hsp : s ≤ p) (hp1 : p ≤ 1)
    (ha : 0 ≤ a) (hD : 0 ≤ D) (hg : 0 ≤ g) :
    8 * nibbleLogFactor k p * k * a ^ 3 * D * g * (p - s) / p ≤
        logNibbleCliqueError k a g D s - logNibbleCliqueError k a g D p ∧
      logNibbleCliqueError k a g D s - logNibbleCliqueError k a g D p ≤
        8 * nibbleLogFactor k s * k * a ^ 3 * D * g * (p - s) / s := by
  obtain ⟨hlo, hhi⟩ := nibbleLogFactor_square_increment_bounds k hs hsp hp1
  have hlo' := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 4 * a ^ 3 * D * g by positivity)
  have hhi' := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 4 * a ^ 3 * D * g by positivity)
  unfold logNibbleCliqueError
  simp only [div_eq_mul_inv] at hlo' hhi' ⊢
  constructor <;> nlinarith only [hlo', hhi']

end Arxiv2411_18291
