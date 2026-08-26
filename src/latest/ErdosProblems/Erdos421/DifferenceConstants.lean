import ErdosProblems.Erdos421.PowerSavingAsymptotics

/-! # Uniform control of the constants after taking difference roots -/

namespace Erdos421

theorem two_mul_logarithmicDifferenceConstant_le (r : ℕ) :
    2 * logarithmicDifferenceConstant r ≤ ((r : ℝ) + 3) ^ (2 * r + 6) := by
  let b : ℝ := (r : ℝ) + 3
  have hb3 : 3 ≤ b := by dsimp only [b]; linarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hpow : 1 ≤ b ^ r := one_le_pow₀ hb1
  have hf : (r.factorial : ℝ) ≤ b ^ r := by
    have h := Nat.factorial_le_pow r
    exact (by exact_mod_cast h : (r.factorial : ℝ) ≤ (r : ℝ) ^ r).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg r) (by dsimp only [b]; linarith) r)
  have hquad : 9 ≤ b ^ (r + 2) := by
    calc
      (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
      _ ≤ b ^ 2 := pow_le_pow_left₀ (by norm_num) hb3 2
      _ ≤ _ := pow_le_pow_right₀ hb1 (by omega)
  have hcoeff : 14 + 2 * b ^ (r + 2) ≤ 4 * b ^ (r + 2) := by linarith
  have hfact : (r.factorial : ℝ) + 3 ≤ 4 * b ^ r := by linarith
  have hm := mul_le_mul hcoeff hfact (by positivity) (by positivity)
  have he : b ^ (r + 2) * b ^ r = b ^ (2 * r + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hp1 : 1 ≤ b ^ (2 * r + 2) := one_le_pow₀ hb1
  have hsmall : 2 * logarithmicDifferenceConstant r ≤ 34 * b ^ (2 * r + 2) := by
    unfold logarithmicDifferenceConstant
    change 2 * (1 + (14 + 2 * b ^ (r + 2)) * (r.factorial + 3)) ≤ _
    nlinarith [he]
  have hfour : 34 ≤ b ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 4
    norm_num at hp
    linarith
  calc
    _ ≤ 34 * b ^ (2 * r + 2) := hsmall
    _ ≤ b ^ 4 * b ^ (2 * r + 2) := mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem quadratic_order_exponent_le (r : ℕ) :
    (r + 2) * (2 * r + 6) ≤ 12 * 2 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [pow_succ]
    nlinarith

theorem logarithmicDifferenceConstant_exp_bound (r : ℕ) :
    2 * logarithmicDifferenceConstant r ≤ (2 : ℝ) ^ (12 * 2 ^ r) := by
  have hb : r + 3 ≤ 2 ^ (r + 2) := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [show r + 1 + 2 = (r + 2) + 1 by omega, pow_succ]
      omega
  calc
    _ ≤ ((r : ℝ) + 3) ^ (2 * r + 6) := two_mul_logarithmicDifferenceConstant_le r
    _ ≤ ((2 : ℝ) ^ (r + 2)) ^ (2 * r + 6) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hb) _
    _ = (2 : ℝ) ^ ((r + 2) * (2 * r + 6)) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (quadratic_order_exponent_le r)

theorem logarithmicSavingConstant_le (r : ℕ) : logarithmicSavingConstant r ≤ 4096 := by
  have hpow : (2 : ℝ) ^ (12 * 2 ^ r) = (4096 : ℝ) ^ (2 ^ r) := by
    rw [pow_mul]
    norm_num
  have hb := Real.rpow_le_rpow
    (mul_nonneg (by norm_num) (logarithmicDifferenceConstant_pos r).le)
    (logarithmicDifferenceConstant_exp_bound r)
    (by positivity : (0 : ℝ) ≤ (((2 ^ r : ℕ) : ℝ)⁻¹))
  rw [hpow, Real.pow_rpow_inv_natCast (by norm_num) (by positivity : (2 ^ r : ℕ) ≠ 0)] at hb
  exact hb

end Erdos421
