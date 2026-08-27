import Arxiv.Arxiv2411_18291.PaperReserveGrowth

/-! # Fixed losses in the reserve construction -/

namespace Arxiv2411_18291

theorem reserve_normalization_constant_le {q K : ℕ} (hq : 2 ≤ q) :
    4 * (4 + 2 * K * 2 ^ K) ≤ (4 * q) ^ (10 * (q + K)) := by
  have hK : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
  have hKK : K * 2 ^ K ≤ 4 ^ K := by
    calc
      _ ≤ 2 ^ K * 2 ^ K := Nat.mul_le_mul_right _ hK
      _ = _ := by rw [← mul_pow]; norm_num
  have hpow : 1 ≤ 4 ^ K := one_le_pow₀ (by decide)
  have hbase : 24 ≤ (4 * q) ^ 2 := by nlinarith
  calc
    _ ≤ 24 * 4 ^ K := by nlinarith only [hKK, hpow]
    _ ≤ (4 * q) ^ 2 * (4 * q) ^ K :=
      Nat.mul_le_mul hbase (Nat.pow_le_pow_left (by omega) K)
    _ = (4 * q) ^ (2 + K) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem reserve_size_constant_le {q K : ℕ} (hq : 2 ≤ q) :
    4 * q * 8 ^ K ≤ (4 * q) ^ (10 * (q + K)) := by
  calc
    _ ≤ (4 * q) * (4 * q) ^ K :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) K)
    _ = (4 * q) ^ (K + 1) := by rw [pow_succ]; ac_rfl
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem reserve_count_loss_constant_le {q K t : ℕ} (hq : 2 ≤ q) (ht : t ≤ q) :
    2 ^ t * 8 ^ (K - 1) * t.factorial ≤ (4 * q) ^ (10 * (q + K)) := by
  have hfac : t.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le ht).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  calc
    _ ≤ (4 * q) ^ t * (4 * q) ^ (K - 1) * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.pow_le_pow_left (by omega) t)
        (Nat.pow_le_pow_left (by omega) (K - 1))) hfac
    _ = (4 * q) ^ (t + (K - 1) + q) := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem reserve_tail_constant_lt {q K r : ℕ} (hq : 2 ≤ q) (hK : 1 ≤ K)
    (hr : r ≤ q) : 48 * (r * K) + 24 * K + 36 < (4 * q) ^ (10 * (q + K)) := by
  have hqK : q ≤ q * K := by simpa using Nat.mul_le_mul_left q hK
  have hKq : K ≤ q * K := by nlinarith only [hq]
  have hrK := Nat.mul_le_mul_right K hr
  have hlinear : 48 * (r * K) + 24 * K + 36 ≤ 108 * (q * K) := by omega
  have hKpow : K ≤ (4 * q) ^ K :=
    (Nat.lt_two_pow_self (n := K)).le.trans (Nat.pow_le_pow_left (by omega) K)
  have hqpow : q ≤ (4 * q) ^ 1 := by simp only [pow_one]; omega
  have h108 : 108 ≤ (4 * q) ^ 3 := by
    have hh := Nat.pow_le_pow_left (by omega : 8 ≤ 4 * q) 3
    norm_num at hh
    omega
  calc
    _ ≤ 108 * (q * K) := hlinear
    _ ≤ (4 * q) ^ 3 * ((4 * q) ^ 1 * (4 * q) ^ K) :=
      Nat.mul_le_mul h108 (Nat.mul_le_mul hqpow hKpow)
    _ = (4 * q) ^ (3 + (1 + K)) := by rw [← pow_add, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)

end Arxiv2411_18291
