import ErdosProblems.Erdos1148.FourFactorHyperbola

/-! # A polynomial cutoff making the four-factor remainder small -/

namespace Erdos1148.DukeArithmetic

theorem exists_fourFactor_scale {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ 2 * K ≤ δ * (M : ℝ) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (2 * K / δ))
  have hM1 : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hKM : 2 * K < (M : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM)
  refine ⟨M, by exact_mod_cast zero_lt_one.trans hM1, ?_⟩
  have hsq : (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  nlinarith

theorem fourFactor_error_at_scaled_power {K β : ℝ} (hK : 0 < K)
    (hβ : 15 / 16 ≤ β) (hβ1 : β < 1) {M q r : ℕ} (hM : 0 < M) (hq : 0 < q) (hr : 0 < r)
    (hsize : 2 * K ≤ (1 - β) * (M : ℝ) ^ 2) :
    K * ((q : ℝ) * r * ((q * r : ℕ) : ℝ) / (1 - β)) *
      (((M * q * r) ^ 8 : ℕ) : ℝ) ^ (13 / 8 - 2 * β) ≤ 1 / 2 := by
  have hd : 0 < 1 - β := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hbase : (0 : ℝ) < (M : ℝ) * q * r := mul_pos (mul_pos hM0 hq0) hr0
  have hN1 : (1 : ℝ) ≤ (((M * q * r) ^ 8 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (Nat.mul_pos (Nat.mul_pos hM hq) hr)
  have hp : (((M * q * r) ^ 8 : ℕ) : ℝ) ^ (13 / 8 - 2 * β) ≤
      1 / ((M : ℝ) * q * r) ^ 2 := by
    calc
      _ ≤ (((M * q * r) ^ 8 : ℕ) : ℝ) ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = ((M : ℝ) * q * r) ^ (-2 : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_mul, ← Real.rpow_natCast_mul hbase.le]
        norm_num
      _ = _ := by rw [Real.rpow_neg hbase.le, Real.rpow_two, one_div]
  calc
    _ ≤ K * ((q : ℝ) * r * ((q * r : ℕ) : ℝ) / (1 - β)) *
        (1 / ((M : ℝ) * q * r) ^ 2) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = K / ((1 - β) * (M : ℝ) ^ 2) := by
      rw [Nat.cast_mul]
      field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hd (sq_pos_of_pos hM0))).mpr
      linarith

end Erdos1148.DukeArithmetic
