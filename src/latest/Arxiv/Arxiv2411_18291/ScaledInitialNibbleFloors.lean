import Arxiv.Arxiv2411_18291.TwiceNibbleFloor

/-! # Smaller comparison errors from explicit floor coefficients -/

namespace Arxiv2411_18291

noncomputable def scaledNibbleError (k : ℕ) (p : ℝ) : ℝ := 2 / (5 * (k : ℝ)) * p ^ k

theorem scaled_nibble_coefficient_bounds_of_seed {b k₀ k : ℕ}
    (hb : 3 ≤ b) (hk₀ : 3 ≤ k₀)
    (hseed : 512 * k₀ ≤ 5 * b ^ k₀ ∧ 8 * k₀ ^ 2 ≤ 5 * b ^ (k₀ - 2) ∧
      52 ≤ b ^ (k₀ - 1)) (hk : k₀ ≤ k) :
    512 * k ≤ 5 * b ^ k ∧ 8 * k ^ 2 ≤ 5 * b ^ (k - 2) ∧ 52 ≤ b ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => exact hseed
  | succ k hk ih =>
    have h3 : 3 ≤ k := hk₀.trans hk
    have hsquare : 3 * k ≤ k ^ 2 := by nlinarith only [h3]
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ 3 * (512 * k) := by omega
        _ ≤ 3 * (5 * b ^ k) := Nat.mul_le_mul_left 3 ih.1
        _ ≤ b * (5 * b ^ k) := Nat.mul_le_mul_right _ hb
        _ = _ := by rw [pow_succ]; ring
    · calc
        _ ≤ 3 * (8 * k ^ 2) := by nlinarith only [h3, hsquare]
        _ ≤ 3 * (5 * b ^ (k - 2)) := Nat.mul_le_mul_left 3 ih.2.1
        _ ≤ b * (5 * b ^ (k - 2)) := Nat.mul_le_mul_right _ hb
        _ = _ := by rw [show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ]; ring
    · exact ih.2.2.trans (Nat.pow_le_pow_right (by omega) (by omega))

theorem scaled_nibble_coefficient_bounds {k : ℕ} (hk : 6 ≤ k) :
    512 * k ≤ 5 * 3 ^ k ∧ 8 * k ^ 2 ≤ 5 * 3 ^ (k - 2) ∧ 52 ≤ 3 ^ (k - 1) :=
  scaled_nibble_coefficient_bounds_of_seed (by norm_num) (by norm_num)
    (by norm_num) hk

theorem scaledNibbleError_nonneg {k : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ scaledNibbleError k p := by unfold scaledNibbleError; positivity

theorem scaledNibbleError_le_pow {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp : 0 ≤ p) :
    scaledNibbleError k p ≤ p ^ k := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 2 / (5 * (k : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  exact mul_le_of_le_one_left (pow_nonneg hp k) hc

theorem scaled_nibble_floor_of_coefficients {b k : ℕ} (hb : 0 < b) (hk : 3 ≤ k)
    (hcoeff : 512 * k ≤ 5 * b ^ k ∧ 8 * k ^ 2 ≤ 5 * b ^ (k - 2) ∧
      52 ≤ b ^ (k - 1))
    (hvar : 128 * (1 / (b : ℝ)) ^ 2 ≤ (k : ℝ) * 2 ^ (k - 2)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (b : ℝ)) :
    NibbleFloorConditions k (scaledNibbleError k p) (2 * p) ∧
      2 * p + (128 * (k : ℝ) + 1) * scaledNibbleError k p ≤ 3 * p := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hK]
  obtain ⟨hsmallN, hdenN, hfaceN⟩ := hcoeff
  have hsmallC : (512 / 5 : ℝ) * k ≤ (b : ℝ) ^ k := by
    have hh : 512 * (k : ℝ) ≤ 5 * (b : ℝ) ^ k := by exact_mod_cast hsmallN
    linarith only [hh]
  have hsmall : (16 * (k : ℝ)) ^ 2 * scaledNibbleError k p ≤ 1 := by
    have hh := nibble_coefficient_times_floor_pow_le_one_of_base
        (by exact_mod_cast hb) hp0 hp hsmallC
    convert hh using 1
    unfold scaledNibbleError
    field_simp
    ring
  have ha0 := scaledNibbleError_nonneg hp0 (k := k)
  have htwo : 2 * scaledNibbleError k p ≤
      (16 * (k : ℝ)) ^ 2 * scaledNibbleError k p :=
    mul_le_mul_of_nonneg_right (by nlinarith only [hK]) ha0
  have hpow2 : p ^ (k - 2) * p ^ 2 = p ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (show 2 ≤ k by omega)]
  have hpow1 : p ^ (k - 1) * p = p ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  have hfaceC : (52 : ℝ) ≤ (b : ℝ) ^ (k - 1) := by exact_mod_cast hfaceN
  have hface : (128 * (k : ℝ) + 1) * scaledNibbleError k p ≤ p := by
    have hc : (128 * (k : ℝ) + 1) * (2 / (5 * k)) ≤ 52 := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hK])
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le_one_of_base
        (by exact_mod_cast hb) hp0 hp hfaceC) hp0
    have h52 : 52 * p ^ k ≤ p := by simpa only [mul_assoc, hpow1, one_mul] using hh
    calc
      _ ≤ 52 * p ^ k := by
        simpa only [scaledNibbleError, mul_assoc] using
          mul_le_mul_of_nonneg_right hc (pow_nonneg hp0 k)
      _ ≤ _ := h52
  refine ⟨⟨by linarith only [htwo, hsmall], hsmall, ?_, ?_, ?_⟩,
    by linarith only [hface]⟩
  · have hdenC : (8 / 5 : ℝ) * (k : ℝ) ^ 2 ≤ (b : ℝ) ^ (k - 2) := by
      have hh : 8 * (k : ℝ) ^ 2 ≤ 5 * (b : ℝ) ^ (k - 2) := by exact_mod_cast hdenN
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right
      (nibble_coefficient_times_floor_pow_le_one_of_base
        (by exact_mod_cast hb) hp0 hp hdenC) (sq_nonneg p)
    rw [mul_assoc, hpow2, one_mul] at hh
    have heq : 16 * (k : ℝ) ^ 3 * scaledNibbleError k p =
        4 * ((8 / 5 : ℝ) * (k : ℝ) ^ 2 * p ^ k) := by
      unfold scaledNibbleError
      field_simp
      ring
    rw [heq]
    nlinarith only [hh]
  · have hv : 128 * p ^ 2 ≤ (k : ℝ) * 2 ^ (k - 2) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2) (by norm_num)).trans hvar
    have hh := mul_le_mul_of_nonneg_right hv (pow_nonneg hp0 (k - 2))
    calc
      _ ≤ 128 * p ^ k := mul_le_mul_of_nonneg_left
        (scaledNibbleError_le_pow (by omega) hp0) (by norm_num)
      _ = (128 * p ^ 2) * p ^ (k - 2) := by rw [← hpow2]; ring
      _ ≤ _ := hh
      _ = _ := by rw [mul_pow]; ring
  · nlinarith only [hface, ha0, hp0]

theorem scaled_nibble_floor {k : ℕ} (hk : 6 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) :
    NibbleFloorConditions k (scaledNibbleError k p) (2 * p) ∧
      2 * p + (128 * (k : ℝ) + 1) * scaledNibbleError k p ≤ 3 * p := by
  have hK : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hfour : (4 : ℝ) ≤ (2 : ℝ) ^ (k - 2) := by
    exact_mod_cast (show 2 ^ 2 ≤ 2 ^ (k - 2) from
      Nat.pow_le_pow_right (by decide) (by omega))
  have hk4 := mul_le_mul_of_nonneg_left hfour (Nat.cast_nonneg k)
  exact scaled_nibble_floor_of_coefficients (b := 3) (by norm_num) (by omega)
    (scaled_nibble_coefficient_bounds hk) (by norm_num; linarith only [hK, hk4]) hp0 hp

end Arxiv2411_18291
