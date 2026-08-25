/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.GeneralBetaChainRatio
import ErdosProblems.Erdos851.BetaSieveFundamental

/-!
# Uniform inflation at beta proportional to dimension
-/

namespace Erdos387.GeneralBetaInflation

open Erdos387.GeneralBetaChainRatio
open Erdos851.BetaSieveFundamental

/-- Elementary finite substitute for the exponential estimate:
`(1+x)^n <= (1-nx)^-1` while `n*x < 1`. -/
theorem one_add_pow_le_one_sub_mul_inv
    (x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hsmall : (n : ℝ) * x < 1) :
    (1 + x) ^ n ≤ (1 - (n : ℝ) * x)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnx : (n : ℝ) * x < 1 := by
        have hnle : (n : ℝ) ≤ n + 1 := by norm_num
        exact (mul_le_mul_of_nonneg_right hnle hx).trans_lt (by
          simpa [Nat.cast_add, Nat.cast_one] using hsmall)
      have hden : 0 < 1 - (n : ℝ) * x := by linarith
      have hden' : 0 < 1 - ((n + 1 : ℕ) : ℝ) * x := by
        simpa [Nat.cast_add, Nat.cast_one] using sub_pos.mpr hsmall
      rw [pow_succ]
      calc
        (1 + x) ^ n * (1 + x) ≤
            (1 - (n : ℝ) * x)⁻¹ * (1 + x) := by
          exact mul_le_mul_of_nonneg_right (ih hnx) (by linarith)
        _ ≤ (1 - ((n + 1 : ℕ) : ℝ) * x)⁻¹ := by
          rw [inv_mul_eq_div]
          rw [div_le_iff₀ hden]
          rw [le_inv_mul_iff₀ hden']
          push_cast
          nlinarith [sq_nonneg x]

/-- With `beta = 100*k`, one full dimension-`k` cutoff inflation is already
smaller than two powers of the beta-100 ratio used by the existing analytic
tail. -/
theorem hundred_mul_beta_inflation_rpow_dimension_le
    {k : ℕ} (hk : 1 ≤ k) :
    Real.rpow (inflation ((100 * k + 1 : ℕ) : ℝ)) (k : ℝ) ≤
      Real.rpow betaRatio 2 := by
  let x : ℝ := 2 / (100 * (k : ℝ) - 1)
  have hden : 0 < 100 * (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hx : 0 ≤ x := (div_pos (by norm_num) hden).le
  have hratio : inflation ((100 * k + 1 : ℕ) : ℝ) = 1 + x := by
    unfold inflation
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have hdenEq : 100 * (k : ℝ) + 1 - 2 = 100 * (k : ℝ) - 1 := by ring
    rw [hdenEq]
    change (100 * (k : ℝ) + 1) / (100 * (k : ℝ) - 1) = 1 + x
    dsimp [x]
    field_simp [ne_of_gt hden]
    ring
  have hkx : (k : ℝ) * x ≤ 2 / 99 := by
    dsimp [x]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hdenle : 99 * (k : ℝ) ≤ 100 * (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hinv := one_div_le_one_div_of_le
      (show (0 : ℝ) < 99 * k by positivity) hdenle
    rw [one_div] at hinv
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ 2 * k by positivity)
    calc
      (k : ℝ) * (2 * (100 * (k : ℝ) - 1)⁻¹) =
          (2 * k) * (100 * (k : ℝ) - 1)⁻¹ := by ring
      _ ≤ (2 * k) * (99 * (k : ℝ))⁻¹ := by
        simpa [one_div] using hmul
      _ = 2 / 99 := by
        field_simp [show (k : ℝ) ≠ 0 by positivity]
  have hsmall : (k : ℝ) * x < 1 := hkx.trans_lt (by norm_num)
  have hpow := one_add_pow_le_one_sub_mul_inv x k hx hsmall
  have hinv : (1 - (k : ℝ) * x)⁻¹ ≤ (99 / 97 : ℝ) := by
    have hdenLower : (97 / 99 : ℝ) ≤ 1 - (k : ℝ) * x := by
      linarith
    have hdenPos : 0 < 1 - (k : ℝ) * x := by linarith
    have hfrac : (99 / 97 : ℝ) = (97 / 99 : ℝ)⁻¹ := by norm_num
    rw [hfrac]
    exact (inv_le_inv₀ hdenPos (by norm_num : (0 : ℝ) < 97 / 99)).2
      hdenLower
  have hratSq : (99 / 97 : ℝ) ≤ (101 / 99 : ℝ) ^ (2 : ℕ) := by norm_num
  calc
    Real.rpow (inflation ((100 * k + 1 : ℕ) : ℝ)) (k : ℝ) =
        inflation ((100 * k + 1 : ℕ) : ℝ) ^ k :=
      Real.rpow_natCast _ _
    _ = (1 + x) ^ k := by rw [hratio]
    _ ≤ (1 - (k : ℝ) * x)⁻¹ := hpow
    _ ≤ (99 / 97 : ℝ) := hinv
    _ ≤ (101 / 99 : ℝ) ^ (2 : ℕ) := hratSq
    _ = Real.rpow betaRatio 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ← Real.rpow_natCast]
      rfl

/-- Depth-multiplied form used by the cutoff Euler-product estimate. -/
theorem hundred_mul_beta_inflation_rpow_dimension_depth_le
    {k r : ℕ} (hk : 1 ≤ k) :
    Real.rpow (inflation ((100 * k + 1 : ℕ) : ℝ))
        ((k : ℝ) * r) ≤
      Real.rpow betaRatio ((2 : ℝ) * r) := by
  have hc : (2 : ℝ) < ((100 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 < 100 * k + 1 by omega)
  calc
    Real.rpow (inflation ((100 * k + 1 : ℕ) : ℝ))
        ((k : ℝ) * r) =
        (Real.rpow (inflation ((100 * k + 1 : ℕ) : ℝ)) (k : ℝ)) ^ r :=
      Real.rpow_mul_natCast (inflation_pos hc).le (k : ℝ) r
    _ ≤ (Real.rpow betaRatio 2) ^ r :=
      pow_le_pow_left₀ (Real.rpow_nonneg (inflation_pos hc).le _)
        (hundred_mul_beta_inflation_rpow_dimension_le hk) r
    _ = Real.rpow betaRatio ((2 : ℝ) * r) := by
      exact (Real.rpow_mul_natCast (by norm_num [betaRatio]) (2 : ℝ) r).symm

end Erdos387.GeneralBetaInflation
