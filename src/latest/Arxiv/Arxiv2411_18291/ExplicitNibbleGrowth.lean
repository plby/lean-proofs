import Arxiv.Arxiv2411_18291.PaperReserveGrowth

/-! # One explicit bound for the constants in the nibble criteria -/

namespace Arxiv2411_18291

def nibbleScalarConstant (q k : ℕ) : ℕ := 2 ^ 24 * q ^ 2 * k ^ 6 * q.factorial

theorem nibbleScalarConstant_le_base {q k : ℕ} (hq : 2 ≤ q) :
    nibbleScalarConstant q k ≤ (4 * q) ^ (10 * (q + k)) := by
  have htwo : 2 ^ 24 ≤ (4 * q) ^ 8 := by
    calc
      _ = 8 ^ 8 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by omega) 8
  have hqpow : q ^ 2 ≤ (4 * q) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkpow : k ≤ (4 * q) ^ k :=
    (Nat.lt_two_pow_self (n := k)).le.trans (Nat.pow_le_pow_left (by omega) k)
  have hfac : q.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le_pow q).trans (Nat.pow_le_pow_left (by omega) q)
  unfold nibbleScalarConstant
  calc
    _ ≤ (4 * q) ^ 8 * (4 * q) ^ 2 * ((4 * q) ^ k) ^ 6 * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul htwo hqpow)
        (Nat.pow_le_pow_left hkpow 6)) hfac
    _ = (4 * q) ^ (8 + 2 + k * 6 + q) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem nibble_monomial_le_constant {q k C i j d : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hC : C ≤ 2 ^ 24) (hi : i ≤ 2) (hj : j ≤ 6) (hd : d ≤ q) :
    C * q ^ i * k ^ j * d.factorial ≤ nibbleScalarConstant q k :=
  Nat.mul_le_mul (Nat.mul_le_mul
    (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hi))
    (Nat.pow_le_pow_right (by omega) hj)) (Nat.factorial_le hd)

theorem paper_threshold_nibble_constant {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    (nibbleScalarConstant q (q.choose r) : ℝ) ≤ (n : ℝ) ^ paperRho q r := by
  calc
    _ ≤ (4 * q : ℝ) ^ (10 * (q + q.choose r)) := by
      exact_mod_cast nibbleScalarConstant_le_base (k := q.choose r) (by omega : 2 ≤ q)
    _ ≤ _ := paper_threshold_reserve_growth hqr hn

theorem paper_threshold_nibble_monomial {q r n C i j d : ℕ} (hr : 1 ≤ r)
    (hqr : r < q) (hn : paperSizeThreshold q r ≤ n)
    (hC : C ≤ 2 ^ 24) (hi : i ≤ 2) (hj : j ≤ 6) (hd : d ≤ q) :
    (C : ℝ) * (q : ℝ) ^ i * (q.choose r : ℝ) ^ j * d.factorial ≤
      (n : ℝ) ^ paperRho q r := by
  calc
    _ ≤ (nibbleScalarConstant q (q.choose r) : ℝ) := by
      exact_mod_cast nibble_monomial_le_constant (by omega : 1 ≤ q)
        (Nat.choose_pos hqr.le) hC hi hj hd
    _ ≤ _ := paper_threshold_nibble_constant hr hqr hn

theorem scaled_rpow_le_of_coefficient_bound {x C c t u v : ℝ} (hx : 1 ≤ x)
    (hc : 0 ≤ c) (hC : C ≤ c * x ^ t) (hgap : t + u ≤ v) :
    C * x ^ u ≤ c * x ^ v := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    _ ≤ (c * x ^ t) * x ^ u := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0.le _)
    _ = c * x ^ (t + u) := by rw [Real.rpow_add hx0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hgap) hc

end Arxiv2411_18291
