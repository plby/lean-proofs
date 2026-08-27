import Arxiv.Arxiv2411_18291.FiniteSparseNibbleMargins

/-! # Finite smallness conditions from the allowed nibble leave -/

namespace Arxiv2411_18291

/-- The five comparisons that do not follow from sparse density alone. -/
structure NibbleFloorConditions (k : ℕ) (a p : ℝ) : Prop where
  error_half : a ≤ 1 / 2
  small : (16 * (k : ℝ)) ^ 2 * a ≤ 1
  denominator : 16 * (k : ℝ) ^ 3 * a ≤ p ^ 2
  variance_bound : 128 * a ≤ (k : ℝ) * p ^ (k - 2)
  face_error : 128 * (k : ℝ) * a ≤ p

theorem nibble_floor_coefficient_bounds_of_seed {b k₀ k : ℕ}
    (hb : 3 ≤ b) (h₀ : 3 ≤ k₀)
    (hseed : 256 * k₀ ^ 2 ≤ b ^ k₀ ∧ 16 * k₀ ^ 3 ≤ b ^ (k₀ - 2) ∧
      128 * k₀ ≤ b ^ (k₀ - 1)) (hk : k₀ ≤ k) :
    256 * k ^ 2 ≤ b ^ k ∧ 16 * k ^ 3 ≤ b ^ (k - 2) ∧
      128 * k ≤ b ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => exact hseed
  | succ k hk ih =>
    have hk3 : 3 ≤ k := h₀.trans hk
    have hsquare : 3 * k ≤ k ^ 2 := by nlinarith only [hk3]
    have hcube : 3 * k ^ 2 ≤ k ^ 3 := by
      nlinarith only [Nat.mul_le_mul_right (k ^ 2) hk3]
    refine ⟨?_, ?_, ?_⟩
    · calc
        256 * (k + 1) ^ 2 ≤ 3 * (256 * k ^ 2) := by nlinarith only [hk3, hsquare]
        _ ≤ 3 * b ^ k := Nat.mul_le_mul_left 3 ih.1
        _ ≤ b * b ^ k := Nat.mul_le_mul_right _ hb
        _ = b ^ (k + 1) := by rw [pow_succ]; ring
    · calc
        16 * (k + 1) ^ 3 ≤ 3 * (16 * k ^ 3) := by nlinarith only [hk3, hsquare, hcube]
        _ ≤ 3 * b ^ (k - 2) := Nat.mul_le_mul_left 3 ih.2.1
        _ ≤ b * b ^ (k - 2) := Nat.mul_le_mul_right _ hb
        _ = b ^ (k + 1 - 2) := by
          rw [show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ]
          ring
    · calc
        128 * (k + 1) ≤ 3 * (128 * k) := by omega
        _ ≤ 3 * b ^ (k - 1) := Nat.mul_le_mul_left 3 ih.2.2
        _ ≤ b * b ^ (k - 1) := Nat.mul_le_mul_right _ hb
        _ = b ^ (k + 1 - 1) := by
          rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
          ring

theorem nibble_floor_coefficient_bounds {k : ℕ} (hk : 15 ≤ k) :
    256 * k ^ 2 ≤ 3 ^ k ∧ 16 * k ^ 3 ≤ 3 ^ (k - 2) ∧
      128 * k ≤ 3 ^ (k - 1) := by
  exact nibble_floor_coefficient_bounds_of_seed (by norm_num : 3 ≤ 3)
    (by norm_num : 3 ≤ 15) (by norm_num) hk

theorem nibble_coefficient_times_floor_pow_le_one_of_base {C p b : ℝ} {m : ℕ}
    (hb : 0 < b) (hp0 : 0 ≤ p) (hp : p ≤ 1 / b) (hC : C ≤ b ^ m) :
    C * p ^ m ≤ 1 := by
  calc
    C * p ^ m ≤ b ^ m * p ^ m := mul_le_mul_of_nonneg_right hC (pow_nonneg hp0 m)
    _ ≤ b ^ m * (1 / b) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp m) (pow_nonneg hb.le m)
    _ = 1 := by rw [← mul_pow]; simp only [mul_one_div_cancel hb.ne', one_pow]

theorem nibble_coefficient_times_floor_pow_le_one {C p : ℝ} {m : ℕ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) (hC : C ≤ 3 ^ m) : C * p ^ m ≤ 1 :=
  nibble_coefficient_times_floor_pow_le_one_of_base (by norm_num) hp0 hp hC

theorem nibble_floor_of_coefficient_bounds {b k : ℕ} (hb : 0 < b) (hk : 3 ≤ k)
    (hcoeff : 256 * k ^ 2 ≤ b ^ k ∧ 16 * k ^ 3 ≤ b ^ (k - 2) ∧
      128 * k ≤ b ^ (k - 1))
    (hvar : 128 * (1 / (b : ℝ)) ^ 2 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (b : ℝ)) : NibbleFloorConditions k (p ^ k) p := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨hsmallN, hdenN, hfaceN⟩ := hcoeff
  have hsmallC : (16 * (k : ℝ)) ^ 2 ≤ (b : ℝ) ^ k := by
    have hh : 256 * (k : ℝ) ^ 2 ≤ (b : ℝ) ^ k := by exact_mod_cast hsmallN
    nlinarith only [hh]
  have hsmall := nibble_coefficient_times_floor_pow_le_one_of_base hbR hp0 hp hsmallC
  have htwo : 2 * p ^ k ≤ (16 * (k : ℝ)) ^ 2 * p ^ k :=
    mul_le_mul_of_nonneg_right (by nlinarith only [hK]) (pow_nonneg hp0 k)
  have hpow2 : p ^ (k - 2) * p ^ 2 = p ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (show 2 ≤ k by omega)]
  have hpow1 : p ^ (k - 1) * p = p ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  refine ⟨by linarith only [htwo, hsmall], hsmall, ?_, ?_, ?_⟩
  · have hC : 16 * (k : ℝ) ^ 3 ≤ (b : ℝ) ^ (k - 2) := by exact_mod_cast hdenN
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le_one_of_base hbR hp0 hp hC) (sq_nonneg p)
    simpa only [mul_assoc, hpow2, one_mul] using hh
  · have hv : 128 * p ^ 2 ≤ k :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2) (by norm_num)).trans hvar
    have hh := mul_le_mul_of_nonneg_right hv (pow_nonneg hp0 (k - 2))
    calc
      128 * p ^ k = (128 * p ^ 2) * p ^ (k - 2) := by rw [← hpow2]; ring
      _ ≤ (k : ℝ) * p ^ (k - 2) := hh
  · have hC : 128 * (k : ℝ) ≤ (b : ℝ) ^ (k - 1) := by exact_mod_cast hfaceN
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le_one_of_base hbR hp0 hp hC) hp0
    simpa only [mul_assoc, hpow1, one_mul] using hh

theorem nibble_floor_of_small_leave {k : ℕ} (hk : 15 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) : NibbleFloorConditions k (p ^ k) p := by
  have hK : (15 : ℝ) ≤ k := by exact_mod_cast hk
  exact nibble_floor_of_coefficient_bounds (by norm_num : 0 < 3) (by omega)
    (nibble_floor_coefficient_bounds hk) (by norm_num; linarith only [hK]) hp0 hp

theorem nibble_floor_of_leave_le_one_div_432 {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 432) : NibbleFloorConditions k (p ^ k) p := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff := nibble_floor_coefficient_bounds_of_seed (by norm_num : 3 ≤ 432)
    (by norm_num : 3 ≤ 3) (by norm_num) hk
  exact nibble_floor_of_coefficient_bounds (by norm_num : 0 < 432) hk
    hcoeff (by norm_num; linarith only [hK]) hp0 hp

theorem sparse_nibble_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hεlo : 3 * (q.choose r : ℝ) * paperRho q r ≤ ε)
    (hn : paperSizeThreshold q r ≤ n) :
    NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) := by
  let K := q.choose r
  let ρ := paperRho q r
  let β : ℝ := ε / (3 * K)
  have hkR : (3 : ℝ) ≤ K := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < K := by linarith only [hkR]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  obtain ⟨hε0, _, hgap, hface, hvar⟩ := paper_sparse_nibble_floor_gaps hqr hk hεlo
  have hαlo : ρ ≤ ε / 3 := by
    have hβ0 : 0 ≤ ε / (3 * (q.choose r : ℝ)) := by positivity
    linarith only [hgap, hβ0]
  have hhalf : 2 * (n : ℝ) ^ (-(ε / 3)) ≤ 1 := by
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat,
      mul_one, Real.rpow_zero] using
      paper_nibble_scaled_monomial (C := 2) (j := 0) (d := 0) hr hqr hn
        (by norm_num) (by norm_num) (by omega) (u := -(ε / 3)) (v := 0)
        (by linarith only [hαlo])
  refine ⟨by linarith only [hhalf], ?_, ?_, ?_, ?_⟩
  · have hh := paper_nibble_scaled_monomial (C := 256) (j := 2) (d := 0) hr hqr hn
      (by norm_num) (by norm_num) (by omega) (u := -(ε / 3)) (v := 0)
      (by linarith only [hαlo])
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Real.rpow_zero] at hh
    nlinarith only [hh]
  · rw [← Real.rpow_mul_natCast hn0.le]
    simpa only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.cast_ofNat] using
      paper_nibble_scaled_monomial (C := 16) (j := 3) (d := 0) hr hqr hn
        (by norm_num) (by norm_num) (by omega) (u := -(ε / 3)) (v := (-β) * 2)
        (by dsimp only [β, K]; linarith only [hgap])
  · have hβK : β * K = ε / 3 := by dsimp only [β]; field_simp
    have hsub : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ K by omega), Nat.cast_ofNat]
    have hh := paper_nibble_scaled_monomial (C := 128) (j := 0) (d := 0) hr hqr hn
      (by norm_num) (by norm_num) (by omega) (u := -(ε / 3)) (v := (-β) * (K - 2 : ℕ))
      (by rw [hsub]; change ρ ≤ 2 * β at hvar; nlinarith only [hvar, hβK])
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] at hh
    rw [Real.rpow_mul_natCast hn0.le] at hh
    exact hh.trans (le_mul_of_one_le_left (by positivity) (by linarith only [hkR]))
  · simpa only [pow_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] using
      paper_nibble_scaled_monomial (C := 128) (j := 1) (d := 0) hr hqr hn
        (by norm_num) (by norm_num) (by omega) (u := -(ε / 3)) (v := -β)
        (by dsimp only [β, K]; linarith only [hface])

theorem sparse_nibble_floor_of_small_leave {q r n : ℕ} (hn : 1 ≤ n)
    (hk : 15 ≤ q.choose r) {ε : ℝ}
    (hp : (n : ℝ) ^ (-(ε / (3 * q.choose r))) ≤ 1 / 3) :
    NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (show q.choose r ≠ 0 by omega)
  have heq : ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) ^ (q.choose r) =
      (n : ℝ) ^ (-(ε / 3)) := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    field_simp
  simpa only [heq] using nibble_floor_of_small_leave hk (Real.rpow_nonneg hn0.le _) hp

theorem sparse_nibble_floor_of_leave_le_one_div_432 {q r n : ℕ} (hn : 1 ≤ n)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hp : (n : ℝ) ^ (-(ε / (3 * q.choose r))) ≤ 1 / 432) :
    NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (show q.choose r ≠ 0 by omega)
  have heq : ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) ^ (q.choose r) =
      (n : ℝ) ^ (-(ε / 3)) := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    field_simp
  simpa only [heq] using nibble_floor_of_leave_le_one_div_432 hk (Real.rpow_nonneg hn0.le _) hp

end Arxiv2411_18291
