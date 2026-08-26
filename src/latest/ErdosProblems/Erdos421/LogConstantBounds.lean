import ErdosProblems.Erdos421.LogMeanValueSaving

/-! # Polynomial bounds for the logarithms of the exponential-sum constants -/

namespace Erdos421

def meanValueLogConstantExponent (k r : ℕ) : ℕ :=
  (k + 2) * k + k ^ 2 + (2 * k + 5) + 4 * ((r + 1) * k) +
    32 * (k + 1) ^ 5 * (r + 1) ^ 3

theorem logarithmicMeanValueConstant_le_two_pow (k r : ℕ) :
    logarithmicMeanValueConstant k r ≤ (2 : ℝ) ^ meanValueLogConstantExponent k r := by
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hbase : (Real.pi * k) ^ k ≤ (2 : ℝ) ^ ((k + 2) * k) := by
    calc
      _ ≤ ((4 : ℝ) * (2 : ℝ) ^ k) ^ k :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul Real.pi_le_four hk2 (Nat.cast_nonneg k) (by norm_num)) k
      _ = _ := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_mul]
        congr 1
        ring
  have hfactorial : (k.factorial : ℝ) ≤ (2 : ℝ) ^ (k ^ 2) := by
    exact_mod_cast nat_factorial_le_two_pow_square k
  have hthree : (3 : ℝ) ^ (2 * ((r + 1) * k)) ≤ (2 : ℝ) ^ (4 * ((r + 1) * k)) := by
    calc
      _ ≤ (4 : ℝ) ^ (2 * ((r + 1) * k)) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        ring
  calc
    _ ≤ (2 : ℝ) ^ ((k + 2) * k) * (2 : ℝ) ^ (k ^ 2) * (2 : ℝ) ^ (2 * k + 5) *
        (2 : ℝ) ^ (4 * ((r + 1) * k)) * (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) := by
      unfold logarithmicMeanValueConstant
      gcongr
    _ = _ := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      rfl

theorem meanValueLogConstantExponent_le (k r : ℕ) :
    meanValueLogConstantExponent k r + 3 ≤ 64 * (k + 1) ^ 5 * (r + 1) ^ 3 := by
  dsimp only [meanValueLogConstantExponent]
  ring_nf
  omega

theorem logarithmicPowerConstant_le_two_pow {k : ℕ} (hk : 0 < k) (r : ℕ) :
    logarithmicPowerConstant k r ≤ (2 : ℝ) ^ (64 * (k + 1) ^ 5 * (r + 1) ^ 3) := by
  let p := 2 * ((r + 1) * k)
  have hp : 0 < p := Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos (Nat.succ_pos r) hk)
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hq : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpR).mpr (by exact_mod_cast hp)
  have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ meanValueLogConstantExponent k r := one_le_pow₀ (by norm_num)
  have hroot : logarithmicMeanValueConstant k r ^ ((p : ℝ)⁻¹) ≤
      (2 : ℝ) ^ meanValueLogConstantExponent k r :=
    (Real.rpow_le_rpow (logarithmicMeanValueConstant_nonneg k r)
      (logarithmicMeanValueConstant_le_two_pow k r) (by positivity)).trans
        (Real.rpow_le_self_of_one_le hbase hq)
  calc
    _ ≤ (2 : ℝ) ^ meanValueLogConstantExponent k r + 4 := add_le_add hroot le_rfl
    _ ≤ (2 : ℝ) ^ (meanValueLogConstantExponent k r + 3) := by
      rw [pow_add]
      norm_num
      linarith
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (meanValueLogConstantExponent_le k r)

theorem logarithmicPowerConstant_uniform_bound {k K r : ℕ} (hk : 0 < k)
    (hkK : k ≤ K) (hr : r ≤ 2 * K ^ 2) :
    logarithmicPowerConstant k r ≤ (2 : ℝ) ^ (1728 * (K + 1) ^ 11) := by
  apply (logarithmicPowerConstant_le_two_pow hk r).trans
  apply pow_le_pow_right₀ (by norm_num)
  have hr' : r + 1 ≤ 3 * (K + 1) ^ 2 := by nlinarith
  calc
    64 * (k + 1) ^ 5 * (r + 1) ^ 3 ≤
        64 * (K + 1) ^ 5 * (3 * (K + 1) ^ 2) ^ 3 := by gcongr
    _ = _ := by ring

end Erdos421
