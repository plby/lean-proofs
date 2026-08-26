/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPrimeChoices

/-!
# The prime-to-totient local denominator correction

The quotient is uniformly close to one at all frequencies, not merely
at zero exponents. Its denominator has a proved positive norm bound.
-/

namespace Erdos4b

noncomputable section

def totientFourierLocalCorrection (p : ℝ) (a : ℂ) : ℂ :=
  (1 + a / (p - 1 : ℝ)) / (1 + a / (p : ℂ))

theorem half_le_norm_one_add_div_of_norm_le {p A : ℝ} {a : ℂ}
    (hp : 0 < p) (hpa : 2 * A ≤ p) (ha : ‖a‖ ≤ A) :
    (1 : ℝ) / 2 ≤ ‖1 + a / (p : ℂ)‖ := by
  have hab : ‖a / (p : ℂ)‖ ≤ (1 : ℝ) / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    linarith
  have h := norm_sub_le (1 + a / (p : ℂ)) (a / (p : ℂ))
  rw [add_sub_cancel_right, norm_one] at h
  linarith

theorem norm_totient_denominator_difference_le {p A : ℝ} {a : ℂ}
    (hp : 2 ≤ p) (ha : ‖a‖ ≤ A) :
    ‖(1 + a / (p - 1 : ℝ)) - (1 + a / (p : ℂ))‖ ≤ 2 * A / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hA : 0 ≤ A := (norm_nonneg a).trans ha
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpC1 : ((p - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp1.ne'
  have hid : (1 + a / (p - 1 : ℝ)) - (1 + a / (p : ℂ)) =
      a / ((p * (p - 1) : ℝ) : ℂ) := by
    push_cast
    have hpC1' : (p : ℂ) - 1 ≠ 0 := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hpC1
    field_simp
    ring
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hp0 hp1)]
  calc
    _ ≤ A / (p * (p - 1)) := div_le_div_of_nonneg_right ha (by positivity)
    _ ≤ A / (p * (p / 2)) := div_le_div_of_nonneg_left hA (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith : p / 2 ≤ p - 1) hp0.le)
    _ = _ := by field_simp

theorem norm_totientFourierLocalCorrection_sub_one_le {p A : ℝ} {a : ℂ}
    (hp : 2 ≤ p) (hpa : 2 * A ≤ p) (ha : ‖a‖ ≤ A) :
    ‖totientFourierLocalCorrection p a - 1‖ ≤ 4 * A / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hA : 0 ≤ A := (norm_nonneg a).trans ha
  have hhalf := half_le_norm_one_add_div_of_norm_le hp0 hpa ha
  have hne : 1 + a / (p : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hhalf)
  have hid : totientFourierLocalCorrection p a - 1 =
      ((1 + a / (p - 1 : ℝ)) - (1 + a / (p : ℂ))) / (1 + a / (p : ℂ)) := by
    rw [sub_div, div_self hne]
    rfl
  rw [hid, norm_div]
  calc
    _ ≤ (2 * A / p ^ 2) / ‖1 + a / (p : ℂ)‖ :=
      div_le_div_of_nonneg_right (norm_totient_denominator_difference_le hp ha) (norm_nonneg _)
    _ ≤ (2 * A / p ^ 2) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hhalf
    _ = _ := by ring

end

end Erdos4b
