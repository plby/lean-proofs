import ErdosProblems.Erdos1141.BurgessPowerScales
import ErdosProblems.Erdos1141.BurgessMomentAsymptotics

/-!
# Finite power-scale estimates for the Burgess amplifier
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem pow_le_scaled_rpow {x q C a : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (h : x ≤ C * q ^ a) (k : ℕ) : x ^ k ≤ C ^ k * q ^ (a * k) := by
  simpa only [mul_pow, ← Real.rpow_mul_natCast hq] using pow_le_pow_left₀ hx h k

theorem scaled_rpow_le_pow {x q C a : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (h : C * q ^ a ≤ x) (k : ℕ) : C ^ k * q ^ (a * k) ≤ x ^ k := by
  simpa only [mul_pow, ← Real.rpow_mul_natCast hq] using
    pow_le_pow_left₀ (mul_nonneg hC (Real.rpow_nonneg hq _)) h k

theorem harmonic_energy_scale_le {q : ℕ} (hq : 1 ≤ q) {H U : ℕ}
    (hU : 0 < U) {c u δ : ℝ} (hu1 : u ≤ 1) (huδ : u ≤ c + δ)
    (hH : (H : ℝ) ≤ (q : ℝ) ^ c) (hUp : (U : ℝ) ≤ (q : ℝ) ^ u)
    (hlog : 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ) :
    ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) ≤
      2 * (q : ℝ) ^ (c + u + 2 * δ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hUq : (U : ℝ) ≤ q := hUp.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq1 hu1)
  have hL : 1 + Real.log (U : ℝ) ≤ (q : ℝ) ^ δ := by
    have hl := Real.log_le_log hU0 hUq
    linarith
  have hL0 : 0 ≤ 1 + Real.log (U : ℝ) := by
    have hl := Real.log_nonneg (by exact_mod_cast hU : (1 : ℝ) ≤ U)
    linarith
  have hA : (H : ℝ) * (1 + Real.log U) ≤ (q : ℝ) ^ (c + δ) := by
    simpa only [Real.rpow_add hq0] using mul_le_mul hH hL hL0 (Real.rpow_nonneg hq0.le c)
  have hU' : (U : ℝ) ≤ (q : ℝ) ^ (c + δ) :=
    hUp.trans (Real.rpow_le_rpow_of_exponent_le hq1 huδ)
  have hA' : (H : ℝ) * (1 + Real.log U) + U ≤ 2 * (q : ℝ) ^ (c + δ) := by
    linarith
  have hB : (U : ℝ) * (1 + Real.log U) ≤ (q : ℝ) ^ (u + δ) := by
    simpa only [Real.rpow_add hq0] using mul_le_mul hUp hL hL0 (Real.rpow_nonneg hq0.le u)
  calc
    _ ≤ (2 * (q : ℝ) ^ (c + δ)) * (q : ℝ) ^ (u + δ) :=
      mul_le_mul hA' hB (mul_nonneg hU0.le hL0) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring

theorem moment_scale_le {q : ℕ} (hq : 0 < q) {V r : ℕ} {v δ : ℝ}
    (hv : v * (r : ℝ) = 1 / 2) (hV : (V : ℝ) ≤ 2 * (q : ℝ) ^ v) :
    (q : ℝ) ^ δ * ((q : ℝ) * (V : ℝ) ^ r + Real.sqrt q * (V : ℝ) ^ (2 * r)) ≤
      ((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 + δ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have h₁ := pow_le_scaled_rpow (Nat.cast_nonneg V) hq0.le hV r
  have h₂ := pow_le_scaled_rpow (Nat.cast_nonneg V) hq0.le hV (2 * r)
  have hvr : v * ((2 * r : ℕ) : ℝ) = 1 := by push_cast; nlinarith only [hv]
  rw [hv] at h₁
  rw [hvr, Real.rpow_one] at h₂
  have hqpow : (q : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) = (q : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      _ = (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (q : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hq0 _ _).symm
      _ = _ := by norm_num
  have hsum : (q : ℝ) * (V : ℝ) ^ r + Real.sqrt q * (V : ℝ) ^ (2 * r) ≤
      ((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 : ℝ) := by
    have ha := mul_le_mul_of_nonneg_left h₁ hq0.le
    have hb := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg q)
    rw [Real.sqrt_eq_rpow] at hb ⊢
    calc
      _ ≤ (q : ℝ) * (2 ^ r * (q : ℝ) ^ (1 / 2 : ℝ)) +
          (q : ℝ) ^ (1 / 2 : ℝ) * (2 ^ (2 * r) * q) := add_le_add ha hb
      _ = (2 ^ r + 2 ^ (2 * r)) * ((q : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hqpow]
  calc
    _ ≤ (q : ℝ) ^ δ * (((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hq0.le δ)
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add hq0]; congr 2; ring

end Pollack17.Burgess
