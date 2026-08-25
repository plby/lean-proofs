import Mathlib

/-!
# Parameter arithmetic for a weak Burgess estimate

The averaging lengths are `floor(q^(5/16))` and `floor(q^(1/8))`.
These leave a power saving for prefix lengths at least `q^(15/32)`.
-/

namespace Erdos1141

lemma half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have h := Nat.lt_floor_add_one x
  linarith

lemma burgess_short_box {q A N : ℕ} (hq : 1 < q)
    (hA : (A : ℝ) ≤ (q : ℝ) ^ (5 / 16 : ℝ))
    (hN : (N : ℝ) ≤ (q : ℝ) ^ (5 / 8 : ℝ)) : A * N < q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hqone : (1 : ℝ) < q := by exact_mod_cast hq
  have hprod : ((A * N : ℕ) : ℝ) < q := by
    calc
      _ = (A : ℝ) * N := by push_cast; rfl
      _ ≤ (q : ℝ) ^ (5 / 16 : ℝ) * (q : ℝ) ^ (5 / 8 : ℝ) :=
        mul_le_mul hA hN (by positivity) (by positivity)
      _ = (q : ℝ) ^ (15 / 16 : ℝ) := by rw [← Real.rpow_add hqpos]; norm_num
      _ < (q : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hqone (by norm_num)
      _ = _ := Real.rpow_one _
  exact_mod_cast hprod

lemma burgess_seventh_power_le {q B : ℕ} (hq : 1 ≤ q)
    (hB : (B : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) : B ^ 7 ≤ q := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  have hpower : (B : ℝ) ^ 7 ≤ q := by
    calc
      _ ≤ ((q : ℝ) ^ (1 / 8 : ℝ)) ^ 7 := pow_le_pow_left₀ (by positivity) hB 7
      _ = (q : ℝ) ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_mul_natCast hqpos.le]; norm_num
      _ ≤ (q : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hqone (by norm_num)
      _ = _ := Real.rpow_one _
  exact_mod_cast hpower

/-- A common constant is absorbed by an arbitrarily small positive power. -/
lemma eventually_const_le_rpow (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, C ≤ (q : ℝ) ^ ε :=
  ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

/-- The explicit averaging choices give a negative power after normalization. -/
lemma burgess_parameter_bound {q A B N : ℝ} (hq : 1 ≤ q)
    (hAlo : q ^ (5 / 16 : ℝ) / 2 ≤ A) (hAhi : A ≤ q ^ (5 / 16 : ℝ))
    (hBlo : q ^ (1 / 8 : ℝ) / 2 ≤ B) (hBhi : B ≤ q ^ (1 / 8 : ℝ))
    (hN : q ^ (15 / 32 : ℝ) ≤ N) :
    512 * N ^ 3 * q ^ (129 / 128 : ℝ) / (A * B ^ 2) + 128 * (A * B) ^ 4 ≤
      4224 * N ^ 4 * q ^ (-3 / 128 : ℝ) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hAlo
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hBlo
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hden : q ^ (9 / 16 : ℝ) ≤ 8 * (A * B ^ 2) := by
    have h := mul_le_mul hAlo (pow_le_pow_left₀ (by positivity) hBlo 2)
      (by positivity) hA.le
    have hid : (q ^ (5 / 16 : ℝ) / 2) * (q ^ (1 / 8 : ℝ) / 2) ^ 2 =
        q ^ (9 / 16 : ℝ) / 8 := by
      rw [div_pow, ← Real.rpow_mul_natCast hqpos.le]
      rw [div_mul_div_comm, ← Real.rpow_add hqpos]
      norm_num
    rw [hid] at h
    linarith
  have hmain : 512 * N ^ 3 * q ^ (129 / 128 : ℝ) / (A * B ^ 2) ≤
      4096 * N ^ 4 * q ^ (-3 / 128 : ℝ) := by
    calc
      _ = (4096 * N ^ 3 * q ^ (129 / 128 : ℝ)) / (8 * (A * B ^ 2)) := by
        field_simp; ring
      _ ≤ (4096 * N ^ 3 * q ^ (129 / 128 : ℝ)) / q ^ (9 / 16 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 4096 * N ^ 3 * q ^ (57 / 128 : ℝ) := by
        rw [mul_div_assoc, ← Real.rpow_sub hqpos]
        norm_num
      _ = (4096 * N ^ 3) * (q ^ (15 / 32 : ℝ) * q ^ (-3 / 128 : ℝ)) := by
        rw [← Real.rpow_add hqpos]; norm_num
      _ ≤ (4096 * N ^ 3) * (N * q ^ (-3 / 128 : ℝ)) := by gcongr
      _ = _ := by ring
  have hshift : A * B ≤ q ^ (7 / 16 : ℝ) := by
    calc
      _ ≤ q ^ (5 / 16 : ℝ) * q ^ (1 / 8 : ℝ) :=
        mul_le_mul hAhi hBhi hB.le (by positivity)
      _ = _ := by rw [← Real.rpow_add hqpos]; norm_num
  have herror : (A * B) ^ 4 ≤ N ^ 4 * q ^ (-3 / 128 : ℝ) := by
    calc
      _ ≤ (q ^ (7 / 16 : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hshift 4
      _ = q ^ (7 / 4 : ℝ) := by rw [← Real.rpow_mul_natCast hqpos.le]; norm_num
      _ ≤ q ^ (237 / 128 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
      _ = (q ^ (15 / 32 : ℝ)) ^ 4 * q ^ (-3 / 128 : ℝ) := by
        rw [← Real.rpow_mul_natCast hqpos.le, ← Real.rpow_add hqpos]; norm_num
      _ ≤ _ := by gcongr
  nlinarith [hmain, herror]

lemma eventually_two_log_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, 2 * Real.log (q : ℝ) ≤ (q : ℝ) ^ ε := by
  have hsmall := (isLittleO_log_rpow_atTop hε).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hsmall.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h, Filter.eventually_ge_atTop 1] with q hq hq1
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hqone),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) ε)] at hq
  linarith

lemma eventually_polyaVinogradov_scale_le :
    ∀ᶠ q : ℕ in Filter.atTop,
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤ (q : ℝ) ^ (159 / 256 : ℝ) := by
  filter_upwards [eventually_two_log_le_rpow (31 / 256) (by norm_num),
    Filter.eventually_ge_atTop 1] with q hq hq1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  calc
    _ = Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ)) := by ring
    _ ≤ Real.sqrt (q : ℝ) * (q : ℝ) ^ (31 / 256 : ℝ) :=
      mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hqpos]; norm_num

end Erdos1141
