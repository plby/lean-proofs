import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Cancellation between a principal pole and a nearby real zero

These estimates retain the distance `1 - beta`; replacing the difference
by separate norm bounds would lose the factor needed in Linnik's theorem.
-/

namespace Linnik

open Complex

theorem norm_pow_sub_pow_le_of_norm_le_one {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ n * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : z ^ (n + 1) - w ^ (n + 1) =
        (z ^ n - w ^ n) * z + w ^ n * (z - w) := by ring
    have hwpow : ‖w ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg w) hw
    calc
      ‖z ^ (n + 1) - w ^ (n + 1)‖ ≤
          ‖z ^ n - w ^ n‖ * ‖z‖ + ‖w ^ n‖ * ‖z - w‖ := by
        rw [hid]
        simpa only [norm_mul] using norm_add_le ((z ^ n - w ^ n) * z) (w ^ n * (z - w))
      _ ≤ (n : ℝ) * ‖z - w‖ * 1 + 1 * ‖z - w‖ := by
        exact add_le_add
          (mul_le_mul ih hz (norm_nonneg z) (by positivity))
          (mul_le_mul_of_nonneg_right hwpow (norm_nonneg _))
      _ = (n + 1 : ℕ) * ‖z - w‖ := by push_cast; ring

theorem norm_one_add_mul_I_ge_one (t : ℝ) :
    1 ≤ ‖(1 : ℂ) + t * I‖ := by
  simpa using Complex.abs_re_le_norm ((1 : ℂ) + t * I)

theorem norm_two_sub_beta_add_mul_I_ge_one {beta : ℝ} (hbeta : beta ≤ 1) (t : ℝ) :
    1 ≤ ‖((2 - beta : ℝ) : ℂ) + t * I‖ := by
  have hreal : 0 ≤ 2 - beta := by linarith
  have hre : 2 - beta ≤ ‖((2 - beta : ℝ) : ℂ) + t * I‖ := by
    simpa [abs_of_nonneg hreal] using
      Complex.abs_re_le_norm (((2 - beta : ℝ) : ℂ) + t * I)
  linarith

theorem norm_principal_exceptional_inverse_difference_le
    {beta : ℝ} (hbeta : beta ≤ 1) (t : ℝ) :
    ‖((1 : ℂ) + t * I)⁻¹ - (((2 - beta : ℝ) : ℂ) + t * I)⁻¹‖ ≤ 1 - beta := by
  let z : ℂ := (1 : ℂ) + t * I
  let w : ℂ := ((2 - beta : ℝ) : ℂ) + t * I
  have hz₁ : 1 ≤ ‖z‖ := norm_one_add_mul_I_ge_one t
  have hw₁ : 1 ≤ ‖w‖ := norm_two_sub_beta_add_mul_I_ge_one hbeta t
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖z‖ ≠ 0)
  have hw : w ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖w‖ ≠ 0)
  have hdiff : w - z = ((1 - beta : ℝ) : ℂ) := by dsimp [w, z]; push_cast; ring
  have hid : z⁻¹ - w⁻¹ = (w - z) / (z * w) := by field_simp
  change ‖z⁻¹ - w⁻¹‖ ≤ 1 - beta
  rw [hid, norm_div, norm_mul, hdiff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  exact div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hz₁ hw₁)

theorem norm_principal_exceptional_power_difference_le
    {beta : ℝ} (hbeta : beta ≤ 1) (t : ℝ) (n : ℕ) :
    ‖(((1 : ℂ) + t * I) ^ n)⁻¹ -
        ((((2 - beta : ℝ) : ℂ) + t * I) ^ n)⁻¹‖ ≤ n * (1 - beta) := by
  have hz₁ := norm_one_add_mul_I_ge_one t
  have hw₁ := norm_two_sub_beta_add_mul_I_ge_one hbeta t
  have hz : ‖((1 : ℂ) + t * I)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (by linarith : 0 < ‖(1 : ℂ) + t * I‖)).mpr hz₁
  have hw : ‖(((2 - beta : ℝ) : ℂ) + t * I)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (by linarith : 0 < ‖((2 - beta : ℝ) : ℂ) + t * I‖)).mpr hw₁
  rw [← inv_pow, ← inv_pow]
  exact (norm_pow_sub_pow_le_of_norm_le_one hz hw n).trans
    (mul_le_mul_of_nonneg_left
      (norm_principal_exceptional_inverse_difference_le hbeta t) (Nat.cast_nonneg n))

theorem norm_principalPolePower_le_at_large_height {t : ℝ} (ht : 4 ≤ |t|) (n : ℕ) :
    ‖(((1 : ℂ) + t * I) ^ n)⁻¹‖ ≤ (1 / 4 : ℝ) ^ n := by
  have hnorm : 4 ≤ ‖(1 : ℂ) + t * I‖ := by
    apply ht.trans
    simpa using Complex.abs_im_le_norm ((1 : ℂ) + t * I)
  rw [norm_inv, norm_pow, ← inv_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hnorm

end Linnik
