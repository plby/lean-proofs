/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SquarefreeSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Vanishing normalized errors in the fixed sieve window -/

open Filter

namespace Erdos946.SieveAsymptotics

open SieveWindow

noncomputable section

theorem tendsto_log_pow_div_nat_pow {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ)) ^ 17 / (N : ℝ) ^ d)
      atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop ((17 : ℕ) : ℝ)
    (show (0 : ℝ) < d by exact_mod_cast hd)).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast, Function.comp_def] using
    h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)

theorem tendsto_inverse_sieveV_div_pow {z d : ℕ} (hz : 272 ≤ z) (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦ (sieveV z N)⁻¹ / (N : ℝ) ^ d) atTop (nhds 0) := by
  let C : ℝ := (3 : ℝ) ^ 17 / (Real.log (z : ℝ)) ^ 17
  have hlim : Tendsto (fun N : ℕ ↦
      C * ((Real.log (N : ℝ)) ^ 17 / (N : ℝ) ^ d)) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_log_pow_div_nat_pow hd).const_mul C
  apply squeeze_zero' _ _ hlim
  · filter_upwards [] with N
    exact div_nonneg (inv_nonneg.mpr (sieveV_pos (by omega : 16 ≤ z)).le)
      (pow_nonneg (Nat.cast_nonneg N) d)
  · filter_upwards [eventually_ge_atTop z] with N hN
    have hb := div_le_div_of_nonneg_right (sieveV_inv_bound hz hN)
      (pow_nonneg (Nat.cast_nonneg N) d)
    calc
      _ ≤ ((3 : ℝ) ^ 17 * (Real.log (N : ℝ) / Real.log (z : ℝ)) ^ 17) /
          (N : ℝ) ^ d := hb
      _ = _ := by dsimp [C]; rw [div_pow]; ring

def normalizedPower (z k N : ℕ) : ℝ :=
  (N : ℝ) ^ k / ((N : ℝ) ^ 2100 * sieveV z N)

theorem normalizedPower_nonneg (z k N : ℕ) (hz : 16 ≤ z) :
    0 ≤ normalizedPower z k N := by
  unfold normalizedPower
  exact div_nonneg (pow_nonneg (Nat.cast_nonneg N) k)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg N) 2100) (sieveV_pos hz).le)

theorem tendsto_normalizedPower {z k : ℕ} (hz : 272 ≤ z) (hk : k < 2100) :
    Tendsto (normalizedPower z k) atTop (nhds 0) := by
  apply (tendsto_inverse_sieveV_div_pow hz (show 0 < 2100 - k by omega)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hV0 : sieveV z N ≠ 0 := (sieveV_pos (by omega : 16 ≤ z)).ne'
  unfold normalizedPower
  have hp : (N : ℝ) ^ 2100 = (N : ℝ) ^ k * (N : ℝ) ^ (2100 - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk.le]
  rw [hp]
  field_simp

def combinedNormalizedError (z N : ℕ) : ℝ :=
  normalizedPower z 1000 N +
    16 * (normalizedPower z 2099 N + normalizedPower z 1051 N) +
    16 * normalizedPower z 2000 N

theorem combinedNormalizedError_nonneg {z N : ℕ} (hz : 16 ≤ z) :
    0 ≤ combinedNormalizedError z N := by
  unfold combinedNormalizedError
  exact add_nonneg
    (add_nonneg (normalizedPower_nonneg z 1000 N hz)
      (mul_nonneg (by norm_num) (add_nonneg (normalizedPower_nonneg z 2099 N hz)
        (normalizedPower_nonneg z 1051 N hz))))
    (mul_nonneg (by norm_num) (normalizedPower_nonneg z 2000 N hz))

theorem tendsto_combinedNormalizedError {z : ℕ} (hz : 272 ≤ z) :
    Tendsto (combinedNormalizedError z) atTop (nhds 0) := by
  have h := ((tendsto_normalizedPower (k := 1000) hz (by norm_num)).add
    (((tendsto_normalizedPower (k := 2099) hz (by norm_num)).add
      (tendsto_normalizedPower (k := 1051) hz (by norm_num))).const_mul 16)).add
    ((tendsto_normalizedPower (k := 2000) hz (by norm_num)).const_mul 16)
  change Tendsto (fun N ↦ normalizedPower z 1000 N +
    16 * (normalizedPower z 2099 N + normalizedPower z 1051 N) +
    16 * normalizedPower z 2000 N) atTop (nhds 0)
  simpa only [add_zero, mul_zero] using h

theorem eventually_combinedNormalizedError_lt {z : ℕ} (hz : 272 ≤ z) :
    ∀ᶠ N : ℕ in atTop, combinedNormalizedError z N < 1 / 1000 :=
  (tendsto_combinedNormalizedError hz).eventually_lt_const (by norm_num)

theorem eventually_combinedError_lt {z : ℕ} (hz : 272 ≤ z) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ 1000 + 16 * ((N : ℝ) ^ 2099 + (N : ℝ) ^ 1051) +
        16 * (N : ℝ) ^ 2000 < ((N : ℝ) ^ 2100 * sieveV z N) / 1000 := by
  filter_upwards [eventually_combinedNormalizedError_lt hz,
    eventually_ge_atTop 1] with N hN hNpos
  have hQ : 0 < (N : ℝ) ^ 2100 * sieveV z N :=
    mul_pos (pow_pos (by exact_mod_cast (show 0 < N by omega)) _)
      (sieveV_pos (by omega : 16 ≤ z))
  have heq : combinedNormalizedError z N =
      ((N : ℝ) ^ 1000 + 16 * ((N : ℝ) ^ 2099 + (N : ℝ) ^ 1051) +
        16 * (N : ℝ) ^ 2000) / ((N : ℝ) ^ 2100 * sieveV z N) := by
    unfold combinedNormalizedError normalizedPower
    ring
  rw [heq, div_lt_iff₀ hQ] at hN
  simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using hN

end

end Erdos946.SieveAsymptotics
