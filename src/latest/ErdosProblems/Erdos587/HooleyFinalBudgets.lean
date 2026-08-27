import ErdosProblems.Erdos587.HooleyCriticalSquare

/-! # Ambient log-log and cube-root budgets for the final bound -/

namespace Erdos587

lemma delta_loglog_of_cubic_ambient {M N : ℕ} (hN : 2 ≤ N) (hM : M ≤ N ^ 3) :
    max 1 (Real.log (Real.log (M : ℝ))) ≤ 3 * max 1 (Real.log (Real.log (N : ℝ))) := by
  let L := max 1 (Real.log (Real.log (N : ℝ)))
  have hL : 1 ≤ L := le_max_left _ _
  have hlogL : Real.log (Real.log (N : ℝ)) ≤ L := le_max_right _ _
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    exact hh
  have hmono := delta_loglog_nat_real_mono (show (M : ℝ) ≤ (N : ℝ) ^ 3 by exact_mod_cast hM)
  apply hmono.trans
  apply max_le (by linarith : (1 : ℝ) ≤ 3 * L)
  rw [Real.log_pow, Real.log_mul (by norm_num) hlogN.ne']
  norm_num only [Nat.cast_ofNat]
  linarith

lemma delta_final_cubic_surplus (R E a m N : ℕ) (hR : 0 < R) (hretain : a ≤ R * m)
    (L : ℝ) (hL : 1 ≤ L)
    (hlarge : ((R ^ 3 * E * 3 ^ 44 : ℕ) : ℝ) * N * L ^ 48 ≤ (a : ℝ) ^ 3) :
    (E : ℝ) * N * (3 * L) ^ 44 ≤ (m : ℝ) ^ 3 := by
  have hRpos : (0 : ℝ) < (R : ℝ) ^ 3 := by positivity
  have hkeep : (a : ℝ) ^ 3 ≤ ((R : ℝ) * m) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hretain) 3
  have h48 : (E : ℝ) * 3 ^ 44 * N * L ^ 48 ≤ (m : ℝ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ hRpos).mp
    calc
      (R : ℝ) ^ 3 * ((E : ℝ) * 3 ^ 44 * N * L ^ 48) =
          ((R ^ 3 * E * 3 ^ 44 : ℕ) : ℝ) * N * L ^ 48 := by push_cast; ring
      _ ≤ (a : ℝ) ^ 3 := hlarge
      _ ≤ ((R : ℝ) * m) ^ 3 := hkeep
      _ = (R : ℝ) ^ 3 * (m : ℝ) ^ 3 := by ring
  calc
    (E : ℝ) * N * (3 * L) ^ 44 = (E : ℝ) * 3 ^ 44 * N * L ^ 44 := by rw [mul_pow]; ring
    _ ≤ (E : ℝ) * 3 ^ 44 * N * L ^ 48 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (by positivity)
    _ ≤ (m : ℝ) ^ 3 := h48

lemma delta_cube_root_loglog_cube (N : ℕ) (L : ℝ) :
    ((N : ℝ) ^ (1 / 3 : ℝ) * L ^ 16) ^ 3 = (N : ℝ) * L ^ 48 := by
  rw [mul_pow, ← pow_mul]
  have hroot : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = N := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  rw [hroot]

end Erdos587
