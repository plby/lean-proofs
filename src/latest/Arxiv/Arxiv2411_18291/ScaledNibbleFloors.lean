import Arxiv.Arxiv2411_18291.FiniteNibbleFloors

/-! # A scaled stopping density reduces the uniform nibble leave constant -/

namespace Arxiv2411_18291

theorem nibble_scaled_floor_coefficient_bounds {k : ℕ} (hk : 3 ≤ k) :
    256 * k ^ 2 ≤ 16 ^ k ∧ 144 * k ^ 3 ≤ 16 ^ k ∧ 384 * k ≤ 16 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsquare : 3 * k ≤ k ^ 2 := by nlinarith only [hk]
    have hcube : 3 * k ^ 2 ≤ k ^ 3 := by
      nlinarith only [Nat.mul_le_mul_right (k ^ 2) hk]
    simp only [pow_succ (16 : ℕ)]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith only [ih.1, hsquare, hk]
    · nlinarith only [ih.2.1, hsquare, hcube, hk]
    · nlinarith only [ih.2.2, hk]

theorem nibble_coefficient_times_floor_pow_le {C p b : ℝ} {m d : ℕ}
    (hb : 0 < b) (hp0 : 0 ≤ p) (hp : p ≤ 1 / b) (hC : C ≤ b ^ (m + d)) :
    C * p ^ m ≤ b ^ d := by
  have hcap := nibble_coefficient_times_floor_pow_le_one_of_base hb hp0 hp
    (C := b ^ m) le_rfl
  calc
    _ ≤ b ^ (m + d) * p ^ m := mul_le_mul_of_nonneg_right hC (pow_nonneg hp0 m)
    _ = b ^ d * (b ^ m * p ^ m) := by rw [pow_add]; ring
    _ ≤ b ^ d * 1 := mul_le_mul_of_nonneg_left hcap (pow_nonneg hb.le d)
    _ = _ := mul_one _

theorem nibble_floor_of_scaled_leave {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 16) :
    NibbleFloorConditions k (p ^ k) ((16 / 3 : ℝ) * p) := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hsmallN, hdenN, hfaceN⟩ := nibble_scaled_floor_coefficient_bounds hk
  have hsmallC : (16 * (k : ℝ)) ^ 2 ≤ (16 : ℝ) ^ k := by
    have hh : 256 * (k : ℝ) ^ 2 ≤ (16 : ℝ) ^ k := by exact_mod_cast hsmallN
    nlinarith only [hh]
  have hsmall := nibble_coefficient_times_floor_pow_le_one_of_base
    (by norm_num : (0 : ℝ) < 16) hp0 hp hsmallC
  have htwo : 2 * p ^ k ≤ (16 * (k : ℝ)) ^ 2 * p ^ k :=
    mul_le_mul_of_nonneg_right (by nlinarith only [hK]) (pow_nonneg hp0 k)
  have hpow2 : p ^ (k - 2) * p ^ 2 = p ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (show 2 ≤ k by omega)]
  have hpow1 : p ^ (k - 1) * p = p ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  have hpScale : p ≤ (16 / 3 : ℝ) * p := by linarith only [hp0]
  refine ⟨by linarith only [htwo, hsmall], hsmall, ?_, ?_, ?_⟩
  · have hC : 144 * (k : ℝ) ^ 3 ≤ (16 : ℝ) ^ ((k - 2) + 2) := by
      rw [Nat.sub_add_cancel (show 2 ≤ k by omega)]
      exact_mod_cast hdenN
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le (by norm_num : (0 : ℝ) < 16) hp0 hp hC)
      (sq_nonneg p)
    have hden : 144 * (k : ℝ) ^ 3 * p ^ k ≤ 256 * p ^ 2 := by
      simpa only [mul_assoc, hpow2, show (16 : ℝ) ^ 2 = 256 by norm_num] using hh
    nlinarith only [hden]
  · have hv : 128 * p ^ 2 ≤ k := by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2)
        (by norm_num : (0 : ℝ) ≤ 128)
      norm_num at hh
      linarith only [hh, hK]
    have hh := mul_le_mul_of_nonneg_right hv (pow_nonneg hp0 (k - 2))
    calc
      128 * p ^ k = (128 * p ^ 2) * p ^ (k - 2) := by rw [← hpow2]; ring
      _ ≤ (k : ℝ) * p ^ (k - 2) := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hpScale _)
        (Nat.cast_nonneg k)
  · have hC : 384 * (k : ℝ) ≤ (16 : ℝ) ^ ((k - 1) + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ k by omega)]
      exact_mod_cast hfaceN
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le (by norm_num : (0 : ℝ) < 16) hp0 hp hC) hp0
    have hface : 384 * (k : ℝ) * p ^ k ≤ 16 * p := by
      simpa only [mul_assoc, hpow1, pow_one] using hh
    linarith only [hface]

theorem sparse_nibble_floor_of_scaled_leave {q r n : ℕ} (hn : 1 ≤ n)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hp : (n : ℝ) ^ (-(ε / (3 * q.choose r))) ≤ 1 / 16) :
    NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((16 / 3 : ℝ) * (n : ℝ) ^ (-(ε / (3 * q.choose r)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (show q.choose r ≠ 0 by omega)
  have heq : ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) ^ (q.choose r) =
      (n : ℝ) ^ (-(ε / 3)) := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    field_simp
  simpa only [heq] using nibble_floor_of_scaled_leave hk (Real.rpow_nonneg hn0.le _) hp

end Arxiv2411_18291
