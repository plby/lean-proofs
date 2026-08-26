import ErdosProblems.Erdos421.ZetaHeightParameters

/-! # Eliminating the auxiliary dyadic height from the growth term -/

namespace Erdos421

theorem dyadic_initial_zeta_weight_bound (u R : ℕ) {T a : ℝ} (ha : 0 ≤ a)
    (hT : ((2 ^ ((R + 1) * u) : ℕ) : ℝ) ≤ T) :
    ((u + 1 : ℕ) : ℝ) * (((2 ^ (u + 1) : ℕ) : ℝ)) ^ a ≤
      (1 + Real.log T / (((R : ℝ) + 1) * Real.log 2)) *
        (2 : ℝ) ^ a * T ^ (a / ((R : ℝ) + 1)) := by
  have hTp : 0 < T := (show (0 : ℝ) < (2 ^ ((R + 1) * u) : ℕ) by positivity).trans_le hT
  have hRp : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log
    (show (0 : ℝ) < (2 ^ ((R + 1) * u) : ℕ) by positivity) hT
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
  have hule : (u : ℝ) ≤ Real.log T / (((R : ℝ) + 1) * Real.log 2) := by
    apply (le_div_iff₀ (mul_pos hRp hlog2)).mpr
    push_cast at hlog
    nlinarith
  have hcoef : ((u + 1 : ℕ) : ℝ) ≤ 1 + Real.log T / (((R : ℝ) + 1) * Real.log 2) := by
    push_cast
    linarith
  have hnatural : (((2 ^ u : ℕ) : ℝ)) ^ (R + 1) ≤ T := by
    have he : (((2 ^ u : ℕ) : ℝ)) ^ (R + 1) = ((2 ^ ((R + 1) * u) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← pow_mul, Nat.mul_comm u]
    rwa [he]
  have hroot : ((2 ^ u : ℕ) : ℝ) ≤ T ^ (((R + 1 : ℕ) : ℝ)⁻¹) := by
    have hr := Real.rpow_le_rpow (by positivity) hnatural
      (by positivity : (0 : ℝ) ≤ (((R + 1 : ℕ) : ℝ)⁻¹))
    rwa [Real.pow_rpow_inv_natCast (by positivity) (by omega : R + 1 ≠ 0)] at hr
  have hweight : (((2 ^ (u + 1) : ℕ) : ℝ)) ^ a ≤
      (2 : ℝ) ^ a * T ^ (a / ((R : ℝ) + 1)) := by
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hroot ha
    have he : (T ^ (((R + 1 : ℕ) : ℝ)⁻¹)) ^ a = T ^ (a / ((R : ℝ) + 1)) := by
      rw [← Real.rpow_mul hTp.le]
      congr 1
      push_cast
      ring
    rw [he] at hp
    have hpow : ((2 ^ (u + 1) : ℕ) : ℝ) = 2 * ((2 ^ u : ℕ) : ℝ) := by
      rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hpow, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hb := mul_le_mul hcoef hweight (by positivity)
    (show 0 ≤ 1 + Real.log T / (((R : ℝ) + 1) * Real.log 2) from
      (Nat.cast_nonneg (u + 1)).trans hcoef)
  simpa only [mul_assoc] using hb

end Erdos421
