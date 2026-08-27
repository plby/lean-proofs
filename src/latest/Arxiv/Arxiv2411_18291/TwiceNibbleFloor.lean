import Arxiv.Arxiv2411_18291.ScaledNibbleFloors

/-! # A doubled stopping density preserves leave constant three for k at least ten -/

namespace Arxiv2411_18291

theorem nibble_twice_floor_coefficient_bounds {k : ℕ} (hk : 10 ≤ k) :
    256 * k ^ 2 ≤ 3 ^ k ∧ 4 * k ^ 3 ≤ 3 ^ (k - 2) ∧
      128 * k + 1 ≤ 3 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsquare : 3 * k ≤ k ^ 2 := by nlinarith only [hk]
    have hcube : 3 * k ^ 2 ≤ k ^ 3 := by
      nlinarith only [Nat.mul_le_mul_right (k ^ 2) (show 3 ≤ k by omega)]
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ 3 * (256 * k ^ 2) := by nlinarith only [hk, hsquare]
        _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 ih.1
        _ = _ := by rw [pow_succ]; ring
    · calc
        _ ≤ 3 * (4 * k ^ 3) := by nlinarith only [hk, hsquare, hcube]
        _ ≤ 3 * 3 ^ (k - 2) := Nat.mul_le_mul_left 3 ih.2.1
        _ = _ := by rw [show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ]; ring
    · calc
        _ ≤ 3 * (128 * k + 1) := by omega
        _ ≤ 3 * 3 ^ (k - 1) := Nat.mul_le_mul_left 3 ih.2.2
        _ = _ := by rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring

theorem nibble_floor_of_twice_leave {k : ℕ} (hk : 10 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) :
    NibbleFloorConditions k (p ^ k) (2 * p) ∧
      2 * p + (128 * (k : ℝ) + 1) * p ^ k ≤ 3 * p := by
  have hK : (10 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hsmallN, hdenN, hfaceN⟩ := nibble_twice_floor_coefficient_bounds hk
  have hsmallC : (16 * (k : ℝ)) ^ 2 ≤ (3 : ℝ) ^ k := by
    have hh : 256 * (k : ℝ) ^ 2 ≤ (3 : ℝ) ^ k := by exact_mod_cast hsmallN
    nlinarith only [hh]
  have hsmall := nibble_coefficient_times_floor_pow_le_one hp0 hp hsmallC
  have htwo : 2 * p ^ k ≤ (16 * (k : ℝ)) ^ 2 * p ^ k :=
    mul_le_mul_of_nonneg_right (by nlinarith only [hK]) (pow_nonneg hp0 k)
  have hpow2 : p ^ (k - 2) * p ^ 2 = p ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (show 2 ≤ k by omega)]
  have hpow1 : p ^ (k - 1) * p = p ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  have hfaceC : 128 * (k : ℝ) + 1 ≤ (3 : ℝ) ^ (k - 1) := by exact_mod_cast hfaceN
  have hface : (128 * (k : ℝ) + 1) * p ^ k ≤ p := by
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le_one hp0 hp hfaceC) hp0
    simpa only [mul_assoc, hpow1, one_mul] using hh
  refine ⟨⟨by linarith only [htwo, hsmall], hsmall, ?_, ?_, ?_⟩,
    by linarith only [hface]⟩
  · have hdenC : 4 * (k : ℝ) ^ 3 ≤ (3 : ℝ) ^ (k - 2) := by exact_mod_cast hdenN
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le_one hp0 hp hdenC) (sq_nonneg p)
    rw [mul_assoc, hpow2, one_mul] at hh
    nlinarith only [hh]
  · have hfour : (4 : ℝ) ≤ (2 : ℝ) ^ (k - 2) := by
      exact_mod_cast (show 2 ^ 2 ≤ 2 ^ (k - 2) from
        Nat.pow_le_pow_right (by decide) (by omega))
    have hv : 128 * p ^ 2 ≤ (k : ℝ) * 2 ^ (k - 2) := by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2)
        (by norm_num : (0 : ℝ) ≤ 128)
      norm_num at hh
      have hk4 := mul_le_mul_of_nonneg_left hfour (Nat.cast_nonneg k)
      linarith only [hh, hK, hk4]
    have hh := mul_le_mul_of_nonneg_right hv (pow_nonneg hp0 (k - 2))
    calc
      128 * p ^ k = (128 * p ^ 2) * p ^ (k - 2) := by rw [← hpow2]; ring
      _ ≤ _ := hh
      _ = _ := by rw [mul_pow]; ring
  · have hz := pow_nonneg hp0 k
    nlinarith only [hface, hp0, hz]

theorem sparse_nibble_floor_of_twice_leave {q r n : ℕ} (hn : 1 ≤ n)
    (hk : 10 ≤ q.choose r) {ε : ℝ}
    (hp : (n : ℝ) ^ (-(ε / (3 * q.choose r))) ≤ 1 / 3) :
    NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      (2 * (n : ℝ) ^ (-(ε / (3 * q.choose r)))) ∧
    2 * (n : ℝ) ^ (-(ε / (3 * q.choose r))) +
      (128 * (q.choose r : ℝ) + 1) * (n : ℝ) ^ (-(ε / 3)) ≤
        3 * (n : ℝ) ^ (-(ε / (3 * q.choose r))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (show q.choose r ≠ 0 by omega)
  have heq : ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) ^ (q.choose r) =
      (n : ℝ) ^ (-(ε / 3)) := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    field_simp
  simpa only [heq] using nibble_floor_of_twice_leave hk (Real.rpow_nonneg hn0.le _) hp

end Arxiv2411_18291
