import ErdosProblems.Erdos4.OuterAtomDecay

/-! Uniform elementary iterated-log bounds below the CRT endpoint. -/

namespace Erdos4.OuterLogBounds

open SmoothParameters OuterRay OuterAccuracy OuterDensity OuterAtomDecay

theorem log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at hh
    norm_num at hh
    linarith
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh

theorem upper_logs {a r n : ℕ} (hra : a ≤ r) (hr : 4 ≤ r)
    (h₁ : 1 ≤ Real.log (n : ℝ)) (h₂ : 1 ≤ Real.log (Real.log (n : ℝ)))
    (h₃ : 1 ≤ Real.log (Real.log (Real.log (n : ℝ))))
    (hupper : Real.log (n : ℝ) ≤ 3 * frontier a r) :
    Real.log (Real.log (n : ℝ)) ≤ 100 * primaryExponent a r ∧
      Real.log (Real.log (Real.log (Real.log (n : ℝ)))) ≤ 8 * r := by
  have ht : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hE1 : (1 : ℝ) ≤ primaryExponent a r := by exact_mod_cast primaryExponent_pos a r
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hlog2 := log_two_bounds
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have harg : Real.log (n : ℝ) ≤ 1024 * (primaryFrontier a r : ℝ) ^ 50 := by
    apply hupper.trans
    rw [OuterRay.frontier, OuterRay.base]
    push_cast
    nlinarith [pow_nonneg ht.le 50]
  have hl₂ := Real.log_le_log (by linarith : 0 < Real.log (n : ℝ)) harg
  rw [Real.log_mul (by norm_num) (pow_ne_zero 50 ht.ne'), Real.log_pow,
    show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow, log_primary] at hl₂
  norm_num only [Nat.cast_ofNat] at hl₂
  have hElog : (primaryExponent a r : ℝ) * Real.log 2 ≤ primaryExponent a r :=
    mul_le_of_le_one_right (by positivity) hlog2.2
  have hl₂bound : Real.log (Real.log (n : ℝ)) ≤ 100 * primaryExponent a r := by
    nlinarith only [hl₂, hElog, hlog2.2, hE1]
  have hEsq : (primaryExponent a r : ℝ) ≤ (core r : ℝ) ^ 2 := by
    exact_mod_cast primaryExponent_le_core_sq_of (stable_exponent_comparison hra hr)
  have harg₃ : Real.log (Real.log (n : ℝ)) ≤ 128 * (core r : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (core r : ℝ)]
  have hl₃ := Real.log_le_log (by linarith : 0 < Real.log (Real.log (n : ℝ))) harg₃
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hV.ne'), Real.log_pow,
    show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow, log_core] at hl₃
  norm_num only [Nat.cast_ofNat] at hl₃
  have hpLog : (2 : ℝ) ^ r * Real.log 2 ≤ (2 : ℝ) ^ r :=
    mul_le_of_le_one_right (by positivity) hlog2.2
  have harg₄ : Real.log (Real.log (Real.log (n : ℝ))) ≤ 128 * (2 : ℝ) ^ r := by
    nlinarith only [hl₃, hpLog, hlog2.2, hpow]
  have hl₄ := Real.log_le_log (by linarith : 0 < Real.log (Real.log (Real.log (n : ℝ)))) harg₄
  rw [Real.log_mul (by norm_num) (pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)),
    Real.log_pow, show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at hl₄
  norm_num only [Nat.cast_ofNat] at hl₄
  have hrLog : (r : ℝ) * Real.log 2 ≤ r := mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2.2
  exact ⟨hl₂bound, by nlinarith only [hl₄, hrLog, hlog2.2, hrR]⟩

theorem lower_third_log {a r n : ℕ}
    (hlarge : (primaryFrontier a r : ℝ) ^ 25 ≤ Real.log (n : ℝ)) :
    (2 : ℝ) ^ r * Real.log 2 ≤ Real.log (Real.log (Real.log (n : ℝ))) := by
  have ht : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hE : (0 : ℝ) < primaryExponent a r := by exact_mod_cast primaryExponent_pos a r
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hl₂ := Real.log_le_log (pow_pos ht 25) hlarge
  rw [Real.log_pow, log_primary] at hl₂
  norm_num only [Nat.cast_ofNat] at hl₂
  have hhalf := log_two_bounds.1
  have hElog := mul_le_mul_of_nonneg_left hhalf hE.le
  have hEl₂ : (primaryExponent a r : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by
    nlinarith only [hl₂, hElog, hE]
  have hEV : (core r : ℝ) ≤ primaryExponent a r := by exact_mod_cast core_le_primaryExponent a r
  have hh := Real.log_le_log hV (hEV.trans hEl₂)
  simpa only [log_core] using hh

theorem exponent_ratio (a r : ℕ) :
    (primaryExponent a r : ℝ) = (2 : ℝ) ^ a * ((2 : ℝ) ^ r) ^ 2 * core r := by
  simp only [primaryExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add, show 2 * r = r * 2 by omega, pow_mul]

end Erdos4.OuterLogBounds
