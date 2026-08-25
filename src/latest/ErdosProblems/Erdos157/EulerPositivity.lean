import ErdosProblems.Erdos157.ElementaryBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-! Positivity of the Euler-factor combination used in the zero-free region. -/

namespace Erdos157.Elementary.ElementaryCharacterBound

theorem hasSum_geometric_succ {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => w ^ (n + 1)) (w / (1 - w)) := by
  simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hw).mul_left w

/-- A geometric average preserves the elementary character positivity identity. -/
theorem geometric_character_positivity (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (a : ℂ) (ha : ‖a‖ ≤ 1) :
    0 ≤ 3 * (t / (1 - t)) + 4 * (((t : ℂ) * a) / (1 - (t : ℂ) * a)).re +
      (((t : ℂ) * a ^ 2) / (1 - (t : ℂ) * a ^ 2)).re := by
  have htC : ‖(t : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg ht] using ht1
  have hta : ‖(t : ℂ) * a‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact (mul_le_of_le_one_right ht ha).trans_lt ht1
  have hta2 : ‖(t : ℂ) * a ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact (mul_le_of_le_one_right ht (pow_le_one₀ (norm_nonneg _) ha)).trans_lt ht1
  have hs := (((hasSum_geometric_succ htC).mul_left 3).add
    ((hasSum_geometric_succ hta).mul_left 4)).add (hasSum_geometric_succ hta2)
  have hre := hs.map Complex.reCLM Complex.reCLM.continuous
  have hterm : ∀ n : ℕ,
      0 ≤ (3 * (t : ℂ) ^ (n + 1) + 4 * ((t : ℂ) * a) ^ (n + 1) +
        ((t : ℂ) * a ^ 2) ^ (n + 1)).re := by
    intro n
    have han : ‖a ^ (n + 1)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ha
    have h := mul_nonneg (pow_nonneg ht (n + 1)) (character_positivity han)
    have hp : (a ^ 2) ^ (n + 1) = (a ^ (n + 1)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (n + 1)]
    simp only [mul_pow, hp, ← Complex.ofReal_pow, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero] at ⊢
    nlinarith
  have hnonneg := HasSum.nonneg hterm hre
  simpa only [Complex.reCLM_apply, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_div, Complex.ofReal_re] using hnonneg

end Erdos157.Elementary.ElementaryCharacterBound
